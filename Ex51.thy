theory Ex51
  imports Main
begin


lemma assumes T: "\<forall> x y. T x y \<or> T y x"
  and A: "\<forall> x y. A x y \<and> A y x \<longrightarrow> x = y"
  and TA: "\<forall> x y. T x y \<longrightarrow> A x y"
  and a: "A x y"
shows "T x y"

proof -
  have "T x y \<or> T y x" using T by blast
  thus "T x y"
  proof
    assume "T x y"
    thus "T x y"  by simp
  next
    assume t2:"T y x"
    hence "A y x" using TA  by blast
    hence "x = y" using A and a by blast
    thus "T x y" using t2 by blast
  qed
qed

end