(* This module defines a data type [GraphemeClusterBreak] for
 * the Unicode Grapheme Cluster Break Property (defined in
 * [UAX29](http://unicode.org/reports/tr29/#Grapheme_Cluster_Break_Property_Values))
 * and proves that it is a finite type.
 *)

Require Import List.
Import ListNotations.

From mathcomp.ssreflect Require Import ssreflect eqtype choice fintype ssrbool ssrfun seq.


Inductive GraphemeClusterBreak :=
  | CR
  | LF
  | Control
  | Extend
  | ZWJ
  | RegionalIndicator
  | Prepend
  | SpacingMark
  | L
  | V
  | T
  | Nothing.


Section GraphemeClusterBreakEqType.

Implicit Types u v : GraphemeClusterBreak.

Definition gcb_eq u v :=
  match u, v with
  | CR, CR
  | LF, LF
  | Control, Control
  | Extend, Extend
  | ZWJ, ZWJ
  | RegionalIndicator, RegionalIndicator
  | Prepend, Prepend
  | SpacingMark, SpacingMark
  | L, L
  | V, V
  | T, T
  | Nothing, Nothing => true
  | _, _ => false
  end.

Lemma gcb_eqP : Equality.axiom gcb_eq.
Proof.
  case; case; by [right | left].
Qed.

Canonical gcb_eqMixin := EqMixin gcb_eqP.
Canonical gcb_eqType := Eval hnf in EqType GraphemeClusterBreak gcb_eqMixin.

Lemma gcb_eqE : gcb_eq = eq_op.
Proof.
  by [].
Qed.

End GraphemeClusterBreakEqType.


Section GraphemeClusterBreakCountableType.


Definition gcb_pickle (b : GraphemeClusterBreak) : nat :=
  match b with
  | CR => 0
  | LF => 1
  | Control => 2
  | Extend => 3
  | ZWJ => 4
  | RegionalIndicator => 5
  | Prepend => 6
  | SpacingMark => 7
  | L => 8
  | V => 9
  | T => 10
  | Nothing => 11
  end.


Definition gcb_unpickle (n : nat) : option GraphemeClusterBreak :=
  match n with
  | 0 => Some CR
  | 1 => Some LF
  | 2 => Some Control
  | 3 => Some Extend
  | 4 => Some ZWJ
  | 5 => Some RegionalIndicator
  | 6 => Some Prepend
  | 7 => Some SpacingMark
  | 8 => Some L
  | 9 => Some V
  | 10 => Some T
  | 11 => Some Nothing
  | _ => None
  end.

Lemma gcb_pickleK : pcancel gcb_pickle gcb_unpickle.
Proof.
  by [case].
Qed.


Definition gcb_unchoice (n : nat) : GraphemeClusterBreak :=
  match n with
  | 0 => CR
  | 1 => LF
  | 2 => Control
  | 3 => Extend
  | 4 => ZWJ
  | 5 => RegionalIndicator
  | 6 => Prepend
  | 7 => SpacingMark
  | 8 => L
  | 9 => V
  | 10 => T
  | _ => Nothing
  end.

Lemma gcb_choice : cancel gcb_pickle gcb_unchoice.
Proof.
  by [case].
Qed.


Definition gcb_choiceMixin := CanChoiceMixin gcb_choice.
Canonical gcb_choiceType := Eval hnf in ChoiceType GraphemeClusterBreak gcb_choiceMixin.

Definition gcb_countMixin := CountMixin gcb_pickleK.
Canonical gcb_countType := Eval hnf in CountType GraphemeClusterBreak gcb_countMixin.

End GraphemeClusterBreakCountableType.


Section GraphemeClusterBreakFinType.

Definition gcb_enum :=
  [
    CR;
    LF;
    Control;
    Extend;
    ZWJ;
    RegionalIndicator;
    Prepend;
    SpacingMark;
    L;
    V;
    T;
    Nothing
  ].


Lemma gcb_enum_uniq : uniq gcb_enum.
Proof.
  by [].
Qed.

Lemma mem_gcb_enum u : u \in gcb_enum.
Proof.
  case u; by [].
Qed.

Definition gcb_finMixin := Eval hnf in UniqFinMixin gcb_enum_uniq mem_gcb_enum.
Canonical gcb_finType := Eval hnf in FinType GraphemeClusterBreak gcb_finMixin.

End GraphemeClusterBreakFinType.


Notation GraphemeClusterBreakF := gcb_finType.
