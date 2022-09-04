(**
 * We want to design a string library that works with
 * (default) extended grapheme clusters (see
 * [UAX29](http://unicode.org/reports/tr29/#Grapheme_Cluster_Boundaries))
 * rather than individual codepoints. Extended grapheme clusters
 * match user perceived characters much more closely than
 * codepoints.
 *
 * Unfortunately, Unicode strings might contain degenerate
 * grapheme clusters, which might combine with other grapheme
 * clusters when strings are concatenated together. This means
 * it is not safe to treat strings as sequences of extended
 * grapheme clusters (which is what we want to do). We need
 * to impose extra conditions on extended grapheme clusters so that
 * such unintended combinations do not occur. We explore a couple
 * sufficient conditions under which straightforward treatment of
 * strings as lists of "characters" is "safe".
 *)
Require Import List.
Import ListNotations.
Require Import Coq.Logic.Decidable.

Require Import CpdtTactics.

Require Import Equality.
Require Import Partition.


Section UnicodeCharacters.

(**
 * A Unicode scalar is any Unicode code point in the range
 * @U+0000@ to @U+D7FF@ inclusive or @U+E000@ to @U+10FFFF@
 * inclusive. Unicode scalars don't include the Unicode
 * surrogate pair code points, which are the code points in
 * the range @U+D800@ to @U+DFFF@ inclusive. Surrogate pairs
 * are an artifact introduced to support UTF-16 encoding of
 * characters that require more than 16 bits. They cannot be
 * encoded by Unicode (TODO: citation), so it makes sense to
 * exclude them as characters.
 *
 * Although we could easily represent Unicode scalars concretely,
 * we will leave them abstract here since we don't depend on
 * their representation.
 *)
Variable UnicodeScalar : Type.


(**
 * Equality of Unicode scalars is decidable.
 *)
Axiom unicode_scalar_eq_dec : 
  eq_decidable UnicodeScalar.


(**
 * The Unicode standard defines a string as any sequence of
 * Unicode scalars. Since our goal is to build a string library
 * that works with sequences of user perceived characters, we will
 * call Unicode's notion of a string a [RawString].
 *)
Definition RawString : Type :=
  list UnicodeScalar.


(**
 * Put a [RawString] in normalization form C as defined in
 * [UAX15](http://unicode.org/reports/tr15/#Norm_Forms).
 * 
 * Instead of defining the function explicitly, we leave it
 * abstract and posit the properties we need. This makes the
 * proofs easier to write and more general (This is a relativly
 * complicated function that changes with new versions of the
 * Unicode standard. The properties we need, however, should be
 * more stable.)
 *)
Variable nfc : RawString -> RawString.


(**
 * Break a [RawString] into a list of it's _default_ extended
 * grapheme clusters as defined in
 * [UAX29](http://www.unicode.org/reports/tr29/#Grapheme_Cluster_Boundaries).
 *
 * Left abstract.
 *)
Variable clusters : RawString -> list RawString.


(**
 * According to the Unicode standard, normalizing a [RawString]
 * never looks across (extended) grapheme cluster boundaries
 * (TODO: citation). This enables local reasoning: reasoning about
 * normalization only requires us to work with grapheme clusters
 * rather than whole strings.
 *
 * Conversely, breaking a string into grapheme clusters should
 * not change the behavior of normalization (TODO: citation).
 * The standard grapheme clustering algorithm is designed to work
 * with all strings (not just normalized ones) (TODO: citation),
 * but the result should be equivalent (in the sense of
 * [canonical equivalence](http://unicode.org/reports/tr15/#Canon_Compat_Equivalence))
 * to applying the algorithm to a normalized string.
 *
 * A good way to formalize this "noninterference" is the following:
 *)
Axiom nfc_commutes_over_clusters :
  forall s : RawString, clusters (nfc s) = map nfc (clusters s).


(**
 * [clusters] does not add or drop characters, it only splits
 * the string into substrings.
 *)
Axiom clusters_partition :
  forall s : RawString, partitions_into s (clusters s).


(**
 * [clusters] does not produce empty clusters.
 *)
Axiom no_empty_clusters :
  forall s : RawString, Forall (fun c => c <> []) (clusters s).


(**
 * Let's make sure our characterization of [clusters] as
 * a partitioning operation is sane. A simple property is that
 * clustering the empty string produces no clusters.
 *)
Theorem clusters_nil_is_nil :
  clusters [] = [].
Proof.
  specialize (clusters_partition []); intro Hempty.
  apply empty_list_partitions_into_empty_lists in Hempty.
  specialize (no_empty_clusters []); intro Hno_empty.
  destruct (clusters []);
    [auto | inversion Hempty; inversion Hno_empty; contradiction]. 
Qed.


(**
 * Also, clusters is only empty if the original string is.
 *)
Theorem clusters_is_nil_only_on_nil :
  forall s : RawString, clusters s = [] -> s = [].
Proof.
  intros s H.
  specialize (clusters_partition s); intro Hcs.
  rewrite H in Hcs; clear H.
  assumption.
Qed.


(**
 * Equality of clusters is decidable.
 *)
Lemma clusters_eq_dec : eq_decidable (list RawString).
Proof.
  repeat apply eq_dec_implies_list_eq_dec.
  apply unicode_scalar_eq_dec.
Qed.


(**
 * Given a string [s1 ++ s2], we say that [clusters] inserts a break
 * between [s1] and [s2] if there is no grapheme cluster that includes
 * this position. Alternatively, we can say that the resulting clusters
 * can be partitioned into two: one covering [s1] and the other covering
 * [s2].
 *)
Definition clusters_break_between (s1 : RawString) (s2 : RawString) : Prop :=
  break_between s1 s2 (clusters (s1 ++ s2)).


(**
 * Note that [clusters_break_between s1 s2] does not necessarily imply that
 * [clusters (s1 ++ s2) = clusters s1 ++ clusters s2]. That is, the fact
 * that there is a break between two strings does not mean [clusters] treats
 * them independently. It could potentially look across this break into [s2],
 * and then decide how to break up [s1] (and vice versa).
 * 
 * This is not good. We would like to use breaks as isolation points. This
 * would let us reason about [clusters] more locally as long as we can
 * manage to identify breaks. For this, we would _like_ the stronger version
 * to hold (we will be able to derive this from other properties of the
 * clustering algorithm).
 *)
Definition clusters_break_between_strong (s1 : RawString) (s2 : RawString) : Prop :=
  clusters s1 ++ clusters s2 = clusters (s1 ++ s2).


(**
 * Let's make sure [clusters_break_between_strong] is actually stronger than
 * [clusters_break_between].
 *)
Lemma break_between_strong_is_stronger :
  forall s1 s2 : RawString,
    clusters_break_between_strong s1 s2 -> clusters_break_between s1 s2.
Proof.
  intros s1 s2 H.
  exists (clusters s1), (clusters s2).
  repeat split.
  - auto.
  - apply clusters_partition.
  - apply clusters_partition.
Qed.


(**
 * For any given position, either there is a break or there isn't.
 *)
Lemma clusters_break_between_decidable :
  forall s1 s2 : RawString, decidable (clusters_break_between s1 s2).
Proof.
  intros s1 s2.
  apply break_between_decidable.
  apply unicode_scalar_eq_dec.
Qed.


(**
 * For any given position, either there is a strong break or there isn't.
 *)
Lemma break_between_strong_decidable :
  forall s1 s2 : RawString, decidable (clusters_break_between_strong s1 s2).
Proof.
  intros s1 s2.
  apply eq_decidable_implies_decidable_eq.
  apply clusters_eq_dec.
Qed.


(** 
 * According to [UAX19](http://unicode.org/reports/tr29/#Grapheme_Cluster_Boundaries)
 * "The boundary between default Unicode grapheme clusters can be
 * determined by just the two adjacent characters." This doesn't seem
 * to hold (regional character indicators come in pairs, so we might have
 * to look at arbitrarily many preceding characters to determine a break; see
 * for example, the rule [GB12](http://unicode.org/reports/tr29/#GB12)), but
 * it is true that only a lookahaed of one character is required
 * (This is quite obvious from the [declerative specification of the algorithm]
 * (http://unicode.org/reports/tr29/#Grapheme_Cluster_Boundary_Rules)).
.* That is, given the entire string up to a position and the next
 * character, we can tell if there is a break in that position.
 *)
Axiom clusters_need_lookahaed_of_one :
  forall (s s' : RawString) (c : UnicodeScalar),
    clusters_break_between s [c] <-> clusters_break_between s (c :: s').


(**
 * Under the single lookahaed assumption, a lot of "locality" properties
 * hold. For example, clusters before breaks are stable under extending
 * the string.
 *)
Theorem clusters_are_stable_under_extension :
  forall (s1 s2 : RawString),
    clusters_break_between s1 s2 ->
      is_prefix_of (clusters s1) (clusters (s1 ++ s2)).
Proof.
  Hint Rewrite app_nil_r concat_app.

  intros s1 s2 Hbreak.
  inversion Hbreak as [cs1 [cs2 [Hsplit [Heqcs1 Heqcs2]]]].
  exists cs2.
  rewrite Hsplit.
  replace cs1 with (clusters s1); auto.
  apply breaks_eq_implies_partitions_eq.
  - apply no_empty_clusters.
  - apply Forall_app with (l2 := cs2).
    rewrite <- Hsplit.
    apply no_empty_clusters.
  - intros s s'; split; intro Hbreak2.
    + replace s1 with (s ++ s') in *.
      * destruct s' as [ | c s'].
        -- exists cs1, []; crush.
        -- apply clusters_need_lookahaed_of_one in Hbreak2.
           apply clusters_need_lookahaed_of_one with (s' := s' ++ s2) in Hbreak2.

           specialize (break_of_break s (c :: s') s2 (clusters ((s ++ c :: s') ++ s2))); intro Hbreak3.
           specialize (Hbreak3 (no_empty_clusters _) Hbreak).
           rewrite <- app_assoc in Hbreak3; specialize (Hbreak3 Hbreak2).
           destruct Hbreak3 as [p1 [p2 [p3 [Heq_clusters [Heq_p1 [Heq_p2 Heq_p3]]]]]].
           clear Hbreak Hbreak2.

           exists p1, p2; repeat split; try assumption.
           specialize (no_empty_clusters ((s ++ c :: s') ++ s2)); intro Hno_empty.
           unfold splits_into in Hsplit; rewrite Hsplit in Hno_empty.
           unfold splits_into in *; unfold partitions_into in *; subst.
           rewrite app_assoc in Heq_clusters; rewrite Heq_clusters in Hsplit; clear Heq_clusters.
           symmetry.
           apply concat_app_eq with (l2 := p3) (l2' := cs2).
           ++ rewrite <- app_assoc; assumption.
           ++ rewrite <- Hsplit in Hno_empty.
              rewrite app_assoc in Hno_empty.
              apply Forall_app in Hno_empty.
              apply Hno_empty.
           ++ apply Forall_app in Hno_empty.
              apply Hno_empty.
           ++ rewrite concat_app; crush.
      * apply break_between_implies_partition in Hbreak2.
        rewrite Hbreak2.
        symmetry.
        apply clusters_partition.
    + replace s1 with (s ++ s') in *.
      * destruct s' as [ | c s'].
        -- exists (clusters s), []; crush. 
           rewrite <- Heqcs1.
           apply clusters_partition.
        -- apply clusters_need_lookahaed_of_one.
           apply clusters_need_lookahaed_of_one with (s' := s' ++ s2).
           inversion Hbreak2 as [cs1_1 [cs1_2 [Hsplit3 [Heqcs1_1 Heqcs1_2]]]].
           unfold splits_into in *; subst.
           exists cs1_1, (cs1_2 ++ cs2); unfold partitions_into in *; crush.
           rewrite <- Heqcs1_2; reflexivity.
      * apply break_between_implies_partition in Hbreak2.
        rewrite Hbreak2.
        symmetry.
        apply Heqcs1.
Qed.


(**
 * This is still not enough to prove that weak breaks imply strong breaks,
 * since clusters _after_ a break might depend on the characters before the
 * break. A good way to see this is to think of [clusters] as emulating a
 * state machine (which is certainly one way to implement [clusters]): it
 * processes the input string one character at a time, deciding for each
 * position whether to insert a break or not. [clusters_need_lookahaed_of_one]
 * ensures that the machine can only see the next character and not beyond.
 * However, we have made no assumptions on what _state_ it maintains. This
 * state can very well depend on all the characters it has seen so far.
 * A sensible assumption to make is that this state resets after each break.
 * (This is certainly true for the default Unicode segmentation algorithm,
 * though it requires squinting at the rules a bit to see).
 *)
Axiom clusters_resets_after_break :
  forall (s1 s2 : RawString),
    clusters_break_between s1 s2 ->
    exists cs1, splits_into (clusters (s1 ++ s2)) cs1 (clusters s2).


(**
 * Combined, these two locality assumptions mean weak breaks
 * are equivalent to strong breaks.
 *)
Lemma break_between_implies_break_between_strong :
  forall s1 s2 : RawString,
    clusters_break_between s1 s2 -> clusters_break_between_strong s1 s2.
Proof.
  intros s1 s2 H.
  apply clusters_are_stable_under_extension in H as Hbefore.
  apply clusters_resets_after_break in H as Hafter.
  destruct Hafter as [cs1 Heq_s2].
  destruct Hbefore as [cs2 Heq_s1].
  replace cs1 with (clusters s1) in *.
  * unfold clusters_break_between_strong.
    symmetry.
    assumption.
  * unfold splits_into in *.
    assert (Heq := Heq_s2).
    rewrite Heq_s1 in Heq.
    apply concat_app_eq in Heq; auto.
    - apply no_empty_clusters.
    - specialize (no_empty_clusters (s1 ++ s2)); intro Hno_empty.
      rewrite Heq_s2 in Hno_empty.
      apply Forall_app in Hno_empty.
      apply Hno_empty.
    - apply app_inv_tail with (l := s2).
      rewrite <- (clusters_partition s1).
      rewrite (clusters_partition s2) at 2.
      rewrite <- concat_app.
      rewrite <- Heq_s2 at 1.
      apply clusters_partition.
Qed.



Section GraphemeClusters.

(**
 * A (possibly degenerate) grapheme cluster is any non-empty sequence of
 * unicode scalars that is treated as a single unit by [clusters].
 *)
Inductive GraphemeCluster : Type :=
  | GC : forall c : RawString, clusters c = [c] -> GraphemeCluster.


(**
 * We identify some subset of [GraphemeCluster]s as well-formed.
 * It doesn't matter how this subset is chosen. We posit the properties
 * we need.
 *)
Variable cluster_well_formed : GraphemeCluster -> Prop.


(**
 * Extract the [RawString] from a [GraphemeCluster].
 * Useful for defining properties.
 *)
Definition raw_string (c : GraphemeCluster) : RawString :=
  match c with
  | GC s _ => s
  end.


(**
 * The main issue we are trying to avoid is grapheme clusters combining
 * with adjacent grapheme clusters. This is necessary for the string type
 * to behave like a simple sequence of characters. We require that two
 * well-formed grapheme clusters don't combine or interact with in any way
 * with respect to [clusters].
 *)
Axiom well_formed_clusters_do_not_combine :
  forall c1 c2 : GraphemeCluster,
    cluster_well_formed c1 /\ cluster_well_formed c2 ->
    clusters (raw_string c1 ++ raw_string c2) = [raw_string c1; raw_string c2].


(* Left here *)




End GraphemeClusters.

End UnicodeCharacters.