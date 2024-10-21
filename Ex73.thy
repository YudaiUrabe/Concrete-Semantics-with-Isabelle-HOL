theory Ex73
  imports "HOL-IMP.Big_Step"
begin

fun seq :: "com \<Rightarrow> com \<Rightarrow> com" where
  "seq SKIP c = c"|
  "seq c SKIP = c"|
  "seq c1 c2 = Seq c1 c2"

lemma Ss:"Seq c1 c2 \<sim> seq c1 c2"
proof
  (induct c1 c2  rule: seq.induct)
  case (1 c)  (* c1 = SKIP*)
  then show ?case 
    by auto
next  (* c2 = SKIP*)
  case ("2_1" v va)
  then show ?case
    by auto
next
  case ("2_2" v va)
  then show ?case
    by auto
next
  case ("2_3" v va vb)
  then show ?case
    by auto
next
  case ("2_4" v va)
  then show ?case
    by auto
next  (* c1, c2 are not SKIP*)
  case ("3_1" v va vb vc)
  then show ?case 
    by simp
next
  case ("3_2" v va vb vc)
  then show ?case
    by simp
next
  case ("3_3" v va vb vc vd)
  then show ?case
    by simp
next
  case ("3_4" v va vb vc)
  then show ?case
    by simp
next
  case ("3_5" v va vb vc)
  then show ?case
    by simp
next
  case ("3_6" v va vb vc)
  then show ?case
    by simp
next
  case ("3_7" v va vb vc vd)
  then show ?case 
    by simp
next
  case ("3_8" v va vb vc)
  then show ?case 
    by simp
next
  case ("3_9" v va vb vc vd)
  then show ?case 
    by simp
next
  case ("3_10" v va vb vc vd)
  then show ?case 
    by simp
next
  case ("3_11" v va vb vc vd ve)
  then show ?case
    by simp
next
  case ("3_12" v va vb vc vd)
  then show ?case
    by simp
next
  case ("3_13" v va vb vc)
  then show ?case
    by simp
next
  case ("3_14" v va vb vc)
  then show ?case
    by simp
next
  case ("3_15" v va vb vc vd)
  then show ?case 
    by simp
next
  case ("3_16" v va vb vc)
  then show ?case
    by simp
qed



fun deskip :: "com \<Rightarrow> com" where
  "deskip (SKIP) = SKIP"|
  "deskip (Assign v a) = Assign v a"|
  "deskip (Seq c1 c2) = seq( deskip c1) ( deskip c2)"|
  "deskip (If b c1 c2) = If b (deskip c1) (deskip c2)"|
  "deskip (While b c) = While b (deskip c)"


lemma sim_deskip: "deskip c \<sim> c"
proof
  (induct c rule: deskip.induct)
  case 1
  then show ?case 
    by simp
next
  case (2 v a)
  then show ?case 
    by simp
next
  case (3 c1 c2)
  then show ?case
    by (smt (verit, del_insts) Seq SeqE Ss deskip.simps(3))
next
  case (4 b c1 c2)
  then show ?case
    by auto
next
  case (5 b c)
  have A:"c \<sim> deskip c"  
    using sim_sym 5
    by auto
  then show ?case
    using sim_while_cong
    by auto
qed

end
