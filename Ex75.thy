theory Ex75
imports "HOL-IMP.Small_Step"
begin


(* Q1: True *)

lemma "IF And b1 b2 THEN c1 ELSE c2 
       \<sim> IF b1 THEN IF b2 THEN c1 ELSE c2 ELSE c2"
apply(induction b1)

  apply (metis Big_Step.IfE big_step.IfFalse big_step.IfTrue bval.simps(3))

  apply (metis Big_Step.IfE big_step.IfFalse big_step.IfTrue bval.simps(3))

  apply (metis Big_Step.IfE big_step.IfFalse big_step.IfTrue bval.simps(3))

  by (metis Big_Step.IfE big_step.IfFalse big_step.IfTrue bval.simps(3))


(* Q2: False *)


(* Q3: True *)  

end

