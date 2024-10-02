theory Ex71
  imports Main
begin

type_synonym vname = string
type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

datatype aexp = N int | V vname | Plus aexp aexp
datatype bexp = Bc bool | Not bexp | And bexp bexp | Less aexp aexp

datatype
  com = SKIP 
  | Assign vname aexp       ("_ ::= _" [1000, 61] 61)
  | Seq    com  com         ("_;;/ _"  [60, 61] 60)
  | If     bexp com com     ("(IF _/ THEN _/ ELSE _)"  [0, 0, 61] 61)
  | While  bexp com         ("(WHILE _/ DO _)"  [0, 61] 61)



inductive
  big_step :: "com \<times> state \<Rightarrow> state \<Rightarrow> bool" (infix "\<Rightarrow>" 55)
  where
    Skip: "(SKIP,s) \<Rightarrow> s" |
    Assign: "(x ::= a,s) \<Rightarrow> s(x := aval a s)" |
    Seq: "\<lbrakk> (c\<^sub>1,s\<^sub>1) \<Rightarrow> s\<^sub>2;  (c\<^sub>2,s\<^sub>2) \<Rightarrow> s\<^sub>3 \<rbrakk> \<Longrightarrow> (c\<^sub>1;;c\<^sub>2, s\<^sub>1) \<Rightarrow> s\<^sub>3" |
    IfTrue: "\<lbrakk> bval b s;  (c\<^sub>1,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Rightarrow> t" |
    IfFalse: "\<lbrakk> \<not>bval b s;  (c\<^sub>2,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Rightarrow> t" |
    WhileFalse: "\<not>bval b s \<Longrightarrow> (WHILE b DO c,s) \<Rightarrow> s" |
    WhileTrue:
    "\<lbrakk> bval b s\<^sub>1;  (c,s\<^sub>1) \<Rightarrow> s\<^sub>2;  (WHILE b DO c, s\<^sub>2) \<Rightarrow> s\<^sub>3 \<rbrakk> 
\<Longrightarrow> (WHILE b DO c, s\<^sub>1) \<Rightarrow> s\<^sub>3"

thm big_step.induct

lemmas big_step_induct = big_step.induct[split_format(complete)]
thm big_step_induct

fun assigned :: "com \<Rightarrow> vname set" where
  "assigned SKIP = {}" |
  "assigned (Assign v a) = {v}" |
  "assigned (Seq c1 c2) = (assigned c1) \<union> (assigned c2)" |
  "assigned (If b c1 c2) = (assigned c1) \<union> (assigned c2)" |
  "assigned (While b c) = assigned c"

lemma "((c, s) \<Rightarrow> t) \<Longrightarrow> (x \<notin> assigned c) \<Longrightarrow> ((s x) = (t x))"
  apply(induction rule: big_step_induct)
        apply auto
  done

end