Require Import List.
Require Import Coq.Logic.Decidable.
Import ListNotations.

Require Import CpdtTactics.

Require Import Equality.


Local Hint Unfold decidable.
Hint Constructors or.


Definition splits_into {A : Type} (l l1 l2 : list A) : Prop :=
  l = l1 ++ l2.


Definition is_prefix_of {A : Type} (p s : list A) : Prop :=
  exists s', splits_into s p s'.


(**
 * We give an inductive definition of being a prefix since proofs
 * work better with those. However, [is_prefix_of] is more straigtforward,
 * and probably easier to work with.
 *)
Inductive IsPrefix {A : Type} : list A -> list A -> Prop :=
  | prefix_nil : forall l, IsPrefix [] l
  | prefix_cons : forall a p l, IsPrefix p l -> IsPrefix (a :: p) (a :: l).


Hint Unfold is_prefix_of splits_into.
Local Hint Constructors IsPrefix.


Lemma splits_into_cons {A : Type} :
  forall (a : A) l l1 l2, splits_into (a :: l) l1 l2 ->
    (exists l1', l1 = a :: l1') \/ (l1 = [] /\ exists l2', l2 = a :: l2').
Proof.
  intros a l l1 l2 H.
  destruct l1.
  - right; split; auto.
    destruct l2; try solve [inversion H].
    inversion H; subst.
    exists l2; auto.
  - left.
    inversion H; subst.
    exists l1; auto.
Qed.


(**
 * Let's show that the two definitions of prefix are equivalent.
 *)
Lemma is_prefix_of_iff_IsPrefix {A : Type} :
  forall p s, @is_prefix_of A p s <-> IsPrefix p s.
Proof.
  intros p s; split; revert s.
  - induction p; intros s H.
    + auto.
    + inversion H as [s' Heq]; clear H.
      unfold splits_into in Heq. subst.
      simpl; constructor.
      apply IHp; clear IHp.
      exists s'; auto.
  - induction p; intros s H.
    + exists s; auto.
    + inversion H; subst; clear H.
      destruct (IHp l H3) as [l' Heq]; clear H3 IHp.
      exists l'. crush.
Qed.


Theorem IsPrefix_decidable {A : Type} :
  eq_decidable A -> forall p s, decidable (@IsPrefix A p s).
Proof.
  Ltac impossible :=
    solve [right; intro HContra; inversion HContra; contradiction].

  intros eq_dec p.
  induction p; intros s.
  - crush.
  - destruct s; try impossible.
    destruct (eq_dec a a0); destruct (IHp s); subst; try impossible; crush.
Qed.


Lemma IsPrefix_app {A : Type} :
  forall e p s, @IsPrefix A p s <-> IsPrefix (e ++ p) (e ++ s).
Proof.
  intros e p s; split; intro H.
  - induction e; crush.
  - induction e.
    + apply H.
    + apply IHe; clear IHe.
      inversion H; auto.
Qed.


Lemma mutual_prefix_implies_eq {A : Type} :
  forall (p1 p2 : list A),
    is_prefix_of p1 p2 ->
    is_prefix_of p2 p1 ->
    p1 = p2.
Proof.
  intros p1 p2 Hprefix1 Hprefix2.
  destruct Hprefix1 as [p2' Heq_p2].
  destruct Hprefix2 as [p1' Heq_p1].
  unfold splits_into in *. subst p2.
  rename Heq_p1 into H.
  rewrite <- app_nil_r in H at 1.
  rewrite <- app_assoc in H.
  apply app_inv_head in H.
  symmetry in H.
  apply app_eq_nil in H.
  destruct H; subst.
  rewrite app_nil_r.
  reflexivity.
Qed.


Definition partitions_into {A : Type} (l : list A) (ls : list (list A)) :=
  l = concat ls.

Hint Unfold partitions_into.


Lemma empty_list_partitions_into_empty_lists {A : Type} :
  forall (ps : list (list A)),
    partitions_into [] ps -> Forall (fun p => p = []) ps.
Proof.
  Hint Constructors Forall.
  induction ps as [ | p ps]; intro H; auto.
  destruct p as [ | a p].
  + crush.
  + inversion H.
Qed.


(* TODO
Theorem empty_partitions_are_irrelevant {A : Type} :
  forall (l : list A) (ps : list (list A)),
    partitions_into l ps <-> partitions_into l (filter (fun p => p <> []) ps).
*)


Lemma partitions_are_prefixes {A : Type} :
  forall (p l : list A) (ps : list (list A)),
    partitions_into l (p :: ps) -> is_prefix_of p l.
Proof.
  intros p l ps H.
  unfold partitions_into in H.
  exists (concat ps).
  auto.
Qed.


(**
 * We say that there is a break between [l1] and [l2] according to
 * [ps] (which is meant to be a partitioning of [l1 ++ l2]) if [ps]
 * can be split into two pieces, one partitioning [l1] and the other
 * partitioning [l2].
 *)
Definition break_between {A : Type} (l1 l2 : list A) (ps : list (list A)) :=
  exists (ps1 ps2 : list (list A)),
    splits_into ps ps1 ps2 /\
    partitions_into l1 ps1 /\
    partitions_into l2 ps2.


Lemma break_between_implies_partition {A : Type} :
  forall (l1 l2 : list A) (ps : list (list A)),
    break_between l1 l2 ps -> partitions_into (l1 ++ l2) ps.
Proof.
  intros l1 l2 ps H.
  inversion H as [ps1 [ps2 [Hsplit [Heqps1 Heqps2]]]].
  unfold partitions_into in *.
  subst l1 l2.
  rewrite Hsplit.
  rewrite concat_app.
  reflexivity.
Qed.


Lemma break_between_cons {A : Type} :
  forall (a l1 l2 : list A) (ps : list (list A)),
    break_between l1 l2 ps <-> break_between (a ++ l1) l2 (a :: ps).
Proof.
  intros a l1 l2 ps; split; intro H.
  - inversion_clear H as [ps1 [ps2 [Hsplit [Heqps1 Heqps2]]]].
    exists (a :: ps1); exists ps2.
    crush.
  - inversion_clear H as [ps1 [ps2 [Hsplit [Heqps1 Heqps2]]]].
    apply splits_into_cons in Hsplit as Hbreak.
    destruct Hbreak as [H | [Heq H]].
    + destruct H as [ps1' H]; subst.
      exists ps1', ps2; repeat split; auto.
      * inversion Hsplit; auto.
      * unfold partitions_into in Heqps1; simpl in Heqps1.
        apply app_inv_head in Heqps1.
        auto.
    + subst.
      apply app_eq_nil in Heqps1; destruct Heqps1; subst.
      inversion_clear H as [ps2' Heqps2']; subst.
      inversion Hsplit; subst.
      exists [], ps2'; crush.
Qed.


Lemma break_between_nil_cons {A : Type} :
  forall (a l2 : list A) (ps : list (list A)),
    break_between [] l2 ps <-> break_between [] (a ++ l2) (a :: ps).
Proof.
  intros a l2 ps; split; intro H.
  - inversion_clear H as [ps1 [ps2 [Hsplit [Heqps1 Heqps2]]]].
    exists []; exists (a :: ps1 ++ ps2); crush.
    unfold partitions_into in *; simpl.
    rewrite concat_app.
    rewrite <- Heqps1.
    rewrite app_nil_l.
    reflexivity.
  - inversion_clear H as [ps1 [ps2 [Hsplit [Heqps1 Heqps2]]]].
    apply splits_into_cons in Hsplit as Hbreak.
    destruct Hbreak as [H | [Heq H]]; subst.
    + destruct a.
      * destruct H as [ps1' Hbreak_ps1]; subst.
        inversion Hsplit.
        exists ps1', ps2; crush.
      * destruct H as [ps1' Hbreak_ps1]; subst.
        inversion Heqps1.
    + destruct H as [ps2' Hsplit_ps2]; subst.
      inversion_clear Hsplit; subst.
      exists [], ps2'; crush.
      unfold partitions_into in *; simpl in Heqps2.
      apply app_inv_head in Heqps2.
      assumption.
Qed.


(**
 * We can decide if there is a break between two list chunks.
 *)
Theorem break_between_decidable {A : Type} :
  eq_decidable A ->
    forall (l1 l2 : list A) (ps : list (list A)),
      decidable (break_between l1 l2 ps).
Proof.
  Ltac impossible_break :=
    solve [ 
      right;
      intro HContra;
      inversion HContra as [ps1 [ps2 [Hsplit [Hp1 Hp2]]]];
      inversion Hsplit as [Heq];
      symmetry in Heq;
      apply app_eq_nil in Heq; destruct Heq; subst;
      try (solve [inversion Hp1]);
      try (solve [inversion Hp2])
    ].

  intro eq_dec.
  intros l1 l2 ps; revert l1 l2.
  induction ps; intros l1 l2.
  - destruct l1; destruct l2; try impossible_break.
    + left; exists []; exists []; crush.
  - destruct (IsPrefix_decidable eq_dec a l1) as [Hprefix1 | Hprefix1].
    + apply is_prefix_of_iff_IsPrefix in Hprefix1.
      inversion_clear Hprefix1 as [l1' Heql1]; unfold splits_into in Heql1; subst.
      apply (decidable_equivalent (break_between_cons a l1' l2 ps)).
      apply IHps.
    + destruct l1 as [ | x l1'].
      -- destruct (IsPrefix_decidable eq_dec a l2) as [Hprefix2 | Hprefix2].
         ++ apply is_prefix_of_iff_IsPrefix in Hprefix2.
            inversion_clear Hprefix2 as [l2' Heql2].
            unfold splits_into in Heql2; subst.
            apply (decidable_equivalent (break_between_nil_cons a l2' ps)).
            apply IHps.
         ++ right; intro HContra.
            inversion_clear HContra as [ps1 [ps2 [Hsplit [Heqps1 Heqps2]]]].
            apply splits_into_cons in Hsplit as Hbreak.
            destruct Hbreak as [H | [Heq H]]; subst.
            * apply Hprefix1.
              apply is_prefix_of_iff_IsPrefix.
              destruct H as [ps1' Hbreak_ps1]; subst.
              apply partitions_are_prefixes in Heqps1.
              assumption.
            * apply Hprefix2.
              apply is_prefix_of_iff_IsPrefix.
              destruct H as [ps12' Hbreak_ps2]; subst.
              apply partitions_are_prefixes in Heqps2.
              assumption.
      -- right; intro HContra.
         inversion_clear HContra as [ps1 [ps2 [Hsplit [Heqps1 Heqps2]]]].
         apply splits_into_cons in Hsplit as Hbreak.
         destruct Hbreak as [H | [Heq H]]; subst.
         * destruct H as [ps1' Hbreak_ps1]; subst.
           apply Hprefix1.
           apply is_prefix_of_iff_IsPrefix.
           apply partitions_are_prefixes in Heqps1.
           assumption.
         * inversion Heqps1.
Qed.


Lemma empty_partition_only_breaks_empty_list {A : Type} :
  forall (s1 s2 : list A),
    break_between s1 s2 [] -> s1 = [] /\ s2 = [].
Proof.
  intros s1 s2 Hbreak.
  inversion Hbreak as [ps1 [ps2 [Hsplit [Heq_ps1 Heq_ps2]]]].
  unfold splits_into in Hsplit.
  symmetry in Hsplit; apply app_eq_nil in Hsplit as [Hnil_ps1 Hnil_ps2]; subst.
  crush.
Qed.


Lemma concat_app_prefix {A : Type} :
  forall (l1 l23 l12 l3 : list (list A)),
    l1 ++ l23 = l12 ++ l3 ->
    Forall (fun p => p <> []) l1 ->
    is_prefix_of (concat l1) (concat l12) ->
    is_prefix_of l1 l12.
Proof.
  induction l1 as [ | p l1]; intros l23 l12 l3 Heq Hneq_l1 Hprefix.
  - exists l12; auto.
  - destruct l12 as [ | p' l12].
    + destruct Hprefix as [Hl2' Heq_l2'].
      unfold splits_into in Heq_l2'; symmetry in Heq_l2'.
      apply app_eq_nil in Heq_l2' as [Hempty_l1 _].
      simpl in Hempty_l1.
      apply app_eq_nil in Hempty_l1 as [Hempty_p _].
      apply Forall_inv in Hneq_l1.
      contradiction.
    + inversion Heq; subst.

      apply is_prefix_of_iff_IsPrefix in Hprefix.
      simpl in Hprefix.
      apply IsPrefix_app in Hprefix.
      apply is_prefix_of_iff_IsPrefix in Hprefix.
      inversion_clear Hneq_l1.
      specialize (IHl1 l23 l12 l3 H1 H0 Hprefix).

      apply is_prefix_of_iff_IsPrefix.
      apply is_prefix_of_iff_IsPrefix in IHl1.
      apply IsPrefix_app with (e := [p']) in IHl1.
      assumption.
Qed.


Lemma concat_app_eq {A : Type} :
  forall (l1 l2 l1' l2' : list (list A)),
    l1 ++ l2 = l1' ++ l2' ->
    Forall (fun p => p <> []) l1 ->
    Forall (fun p => p <> []) l1' ->
    concat l1 = concat l1' ->
    l1 = l1'.
Proof.
  intros l1 l2 l1' l2' Heq Hno_empty_l1 Hno_empty_l1' Hconcat.
  assert (is_prefix_of l1 l1').
  + apply (concat_app_prefix l1 l2 l1' l2'); auto.
    - exists []; crush.
  + inversion H as [l1'' Heq_l1''].
    unfold splits_into in Heq_l1''; subst.
    replace l1'' with ([] : list (list A)).
    - symmetry; apply app_nil_r.
    - rewrite concat_app in Hconcat.
      rewrite <- app_nil_r in Hconcat at 1.
      apply app_inv_head in Hconcat.
      apply empty_list_partitions_into_empty_lists in Hconcat.
      destruct l1''; auto.
      exfalso.
      apply Forall_app in Hno_empty_l1'.
      destruct Hno_empty_l1' as [_ Hno_empty_l1''].
      apply Forall_inv in Hno_empty_l1''.
      apply Forall_inv in Hconcat.
      contradiction.
Qed.

Theorem break_of_break {A : Type} :
  forall (l1 l2 l3 : list A) (ps : list (list A)),
    Forall (fun p => p <> []) ps -> (* TODO: remove this requirement *)
    break_between (l1 ++ l2) l3 ps ->
    break_between l1 (l2 ++ l3) ps ->
    exists p1 p2 p3,
      ps = p1 ++ p2 ++ p3 /\
      partitions_into l1 p1 /\
      partitions_into l2 p2 /\
      partitions_into l3 p3.
Proof.
  intros l1 l2 l3 ps Hno_empty Hbreak23 Hbreak12.
  inversion_clear Hbreak23 as [p12 [p3 [Hsplit23 [Heq_p12 Heq_p3]]]].
  inversion_clear Hbreak12 as [p1 [p23 [Hsplit12 [Heq_p1 Heq_p23]]]].
  assert (Hprefix_l1 : is_prefix_of p1 p12).
  + apply (concat_app_prefix p1 p23 p12 p3).
    - crush.
    - unfold splits_into in Hsplit12; subst.
      apply Forall_app in Hno_empty.
      apply Hno_empty.
    - exists l2; crush.
  + inversion Hprefix_l1 as [p2 Heq_p2].
    exists p1, p2, p3; repeat split.
    - unfold splits_into in *; crush.
    - assumption.
    - unfold partitions_into in *; subst.
      unfold splits_into in Heq_p2; subst.
      rewrite concat_app in Heq_p12.
      apply app_inv_head in Heq_p12.
      assumption.
    - assumption.
Qed.


Lemma break_between_cons_prefix {A : Type} :
  forall (l1 l2 p : list A) (ps : list (list A)),
    l1 <> [] ->
    break_between l1 l2 (p :: ps) ->
    is_prefix_of p l1.
Admitted.


Local Lemma break_between_obvious {A : Type} :
  forall (p : list A) (ps : list (list A)),
    break_between p (concat ps) (p :: ps).
Proof.
  intros p ps.
  exists [p], ps; repeat split; auto.
  unfold partitions_into; simpl.
  rewrite app_nil_r.
  reflexivity.
Qed.


(**
 * Two partitionings are the same if and only if they
 * induce the same breaks (modulo empty partitions). This
 * gives us a nice way to characterize partitions.
 *)
Lemma breaks_eq_implies_partitions_eq {A : Type} :
  forall (ps1 ps2 : list (list A)),
  Forall (fun p => p <> []) ps1 ->
  Forall (fun p => p <> []) ps2 ->
  (forall (s1 s2 : list A),
     break_between s1 s2 ps1 <-> break_between s1 s2 ps2) ->
  ps1 = ps2.
Proof.
  induction ps1 as [ | p1 ps1]; intros ps2 Hno_empty_ps1 Hno_empty_ps2 Hsame_breaks.
  - destruct ps2 as [ | p2 ps2].
    + reflexivity.
    + inversion_clear Hno_empty_ps2.
      contradict H.
      apply (empty_partition_only_breaks_empty_list p2 (concat ps2)).
      apply Hsame_breaks.
      exists [p2], ps2; crush.
      unfold partitions_into; simpl.
      rewrite app_nil_r.
      reflexivity.

  - destruct ps2 as [| p2 ps2].
    + inversion_clear Hno_empty_ps1.
      contradict H.
      apply (empty_partition_only_breaks_empty_list p1 (concat ps1)).
      apply Hsame_breaks.
      apply break_between_obvious.
    + replace p2 with p1 in *.
      * replace ps2 with ps1; auto.
        apply IHps1.
        -- inversion_clear Hno_empty_ps1; assumption.
        -- inversion_clear Hno_empty_ps2; assumption.
        -- intros s1 s2; split; intro H;
             apply break_between_cons with (a := p1);
             apply Hsame_breaks;
             apply break_between_cons;
             assumption.
      * apply mutual_prefix_implies_eq.
        -- apply break_between_cons_prefix with (l2 := concat ps2) (ps := ps1).
           ** inversion Hno_empty_ps2; assumption.
           ** apply Hsame_breaks.
              apply break_between_obvious.
        -- apply break_between_cons_prefix with (l2 := concat ps1) (ps := ps2).
           ** inversion Hno_empty_ps1; assumption.
           ** apply Hsame_breaks.
              apply break_between_obvious.
Qed.


(* TODO: this might be useful *)
(*
Lemma non_empty_breaks_are_unique {A : Type} :
  forall (s1 s2 : list A) (ps : list (list A)) (cs1 cs2 cs1' cs2' : list (list A)),
    Forall (fun p => p <> []) ps ->
    splits_into ps cs1 cs2 ->
    partitions_into s1 cs1 ->
    partitions_into s2 cs2 ->
    splits_into ps cs1' cs2' ->
    partitions_into s1 cs1' ->
    partitions_into s2 cs2' ->
    cs1 = cs1' /\ cs2 = cs2'.
Proof.
  intros s1 s2 ps cs1 cs2 cs1' cs2' Hno_empty Hsplit Hp_cs1 Hp_cs2 Hsplit' Hp_cs1' Hp_cs2'.
  assert (cs1 = cs1').
  - induction cs1 as [_ | p cs1]; destruct cs1' as [_ | p' cs1']; auto.
    + unfold partitions_into in Hp_cs1; subst.
      simpl in Hp_cs1'.
      apply empty_list_partitions_into_empty_lists in Hp_cs1' as HContra.
      apply Forall_inv in HContra.
      contradict HContra.
      unfold splits_into in Hsplit'; subst.
      apply Forall_inv in Hno_empty.
      assumption.
    + unfold partitions_into in Hp_cs1'; subst.
      simpl in Hp_cs1.
      apply empty_list_partitions_into_empty_lists in Hp_cs1 as HContra.
      apply Forall_inv in HContra.
      contradict HContra.
      unfold splits_into in Hsplit; subst.
      apply Forall_inv in Hno_empty.
      assumption.
    + admit.

  - subst cs1; split; auto.
    unfold splits_into in *.
    rewrite Hsplit' in Hsplit.
    apply app_inv_head in Hsplit.
    symmetry; assumption.
Admitted.
   
*)

(* TODO: generalize breaks to multiple breaks.

(**
 * Given two partitionings [c, g], we say that [g] is more _granular_
 * than [c] (or [g] is a sub partition of [c]) if every "break" in [c]
 * also exists in [g].
 *)
Inductive IsSubPartition {A : Type} : list (list A) -> list (list A) -> Prop :=
  | sub_partition_nil : IsSubPartition [] []
  | sub_partition_empty : forall c g, IsSubPartition c g -> IsSubPartition c ([] :: g)
  | sub_partition_head : forall c g, forall hc hg rg,
    splits_into hg hc rg -> IsSubPartition c (rg :: g) -> IsSubPartition (hc :: c) (hg :: g).


Theorem IsSubPartition_decidable {A : Type} :
  forall c g, decidable (@IsSubPartition A c g).
Admitted.


Lemma partition_split_decidable {A : Type} :
  forall (l1 l2 : list A) (ps : list (list A)),
    decidable (
      exists (ps1 ps2 : list (list A)),
        splits_into ps ps1 ps2 /\
        partitions_into l1 ps1 /\
        partitions_into l2 ps2).
Proof.
  intros l1 l2 ps.
  destruct (IsSubPartition_decidable [l1; l2] ps).
*)