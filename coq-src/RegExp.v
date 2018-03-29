Require Import List.
Import ListNotations.


From RelationAlgebra Require Import kat regex kat_tac.


Lemma test : forall (r1 r2 : regex'), r1 + r2 == r2 + r1.
Proof.
  intros.
  ka.
Qed.