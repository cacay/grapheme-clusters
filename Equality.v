Require Import List.
Require Import Coq.Logic.Decidable.


(**
 * Define what it means for equality on a type to be decidable.
 *)
Definition eq_decidable (A : Type) : Type :=
  forall (x y : A), {x = y} + {x <> y}.


(**
 * If we can decide the equality for a type, we can decide it
 * for lists of that type.
 *)
Lemma eq_dec_implies_list_eq_dec {A : Type} :
  eq_decidable A -> eq_decidable (list A).
Proof.
  intros H x y.
  apply list_eq_dec.
  apply H.
Qed.


(**
 * If we can computationally decide equality, then we can do
 * it propositionally.
 *)
Lemma eq_decidable_implies_decidable_eq (A : Type) :
  eq_decidable A -> (forall (x y : A), decidable (x = y)).
Proof.
  Hint Unfold decidable.
  Hint Constructors or.
  intros H x y.
  destruct (H x y); auto.
Qed.



Local Lemma decidable_equivalent_helper {P Q : Prop} :
  P <-> Q -> decidable P -> decidable Q.
Proof.
  intros H.
  intro Hdec.
  destruct Hdec as [HP | HP]; [left | right].
  - apply H; apply HP.
  - intros HQ. apply HP. apply H. apply HQ.
Qed.


Lemma decidable_equivalent {P Q : Prop} :
  P <-> Q -> decidable P <-> decidable Q.
Proof.
  intros H.
  split; apply decidable_equivalent_helper.
  - auto.
  - symmetry. auto.
Qed.


Lemma Forall_app :
  forall (A : Type) (P : A -> Prop) (l1 l2 : list A),
    (Forall P l1 /\ Forall P l2) <-> Forall P (l1 ++ l2).
Proof.
  intros A P l1 l2; split.
  - intros [HPl1 HPl2].
    induction l1; auto.
    inversion HPl1; subst.
    apply Forall_cons; auto.
  - intros HPl1l2; split; induction l1; inversion HPl1l2; auto.
Qed.
