(* Syntax, proving, first tactics, forward proof style *)
Theorem forward_small : (forall A B : Prop, A -> (A->B) -> B).
Proof.
 intros A.
 intros B.
 intros proof_of_A.
 intros A_implies_B.
 pose (proof_of_B := A_implies_B proof_of_A).
 exact proof_of_B.
Qed.

(* Backward proof style, apply tactic *)
Theorem backward_huge : (forall A B C : Prop, A -> (A->B) -> (A->B->C) -> C).
Proof.
 intros A B C.
 intros proof_of_A A_implies_B A_imp_B_imp_C.
 apply A_imp_B_imp_C.
 - exact proof_of_A.
 - apply A_implies_B. exact proof_of_A.
Qed.

(* Prop and Set Types, difference between True/False and true/false *)
Print False.
Print True.
Print bool.

Theorem True_can_be_proven : True.
  exact I.
Qed.

(* not is just implication to falsehood *)
Print not.
(**
Notation "~ x" := (not x) : type_scope.
**)
(* destruct tactic *)
Theorem False_cannot_be_proven__again : ~False.
Proof.
  intros proof_of_False.
  destruct proof_of_False.
Qed.

(* rewrite tactic *)
Theorem thm_eq_trans__again : (forall x y z: Set, x = y -> y = z -> x = z).
Proof.
  intros x y z.
  intros x_y y_z.
  destruct x_y.
  Undo.
  rewrite x_y.
  rewrite <- y_z.
  exact (eq_refl y).
Qed.

(* (familiar from FP) list definition *)
Require Import List.
Print list.

(* induction, simpl, auto, reflexivity tactics,
   intro patterns https://coq.inria.fr/refman/proof-engine/tactics.html#intro-patterns,
   bullets
*)
Theorem app_assoc : forall A (l m n : list A), l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros. induction l as [|x l IHl].
  - auto.
  - simpl. rewrite <- IHl. reflexivity.
Qed.
