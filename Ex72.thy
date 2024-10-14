theory Ex72
imports "HOL-IMP.Big_Step"
begin

fun skip :: "com \<Rightarrow> bool" where
"skip (SKIP) = True"|
"skip (Assign v a) = False"|
"skip (Seq c1 c2) =  (skip(c1) \<and> skip(c2))"|
"skip (If b c1 c2) = (skip(c1) \<and>  skip(c2))"|
"skip (While b c) = False"

lemma "skip c \<Longrightarrow> c \<sim> SKIP"
apply(induction c rule: skip.induct)
  apply (blast)
 apply simp
apply fastforce
apply auto
apply blast

done
end