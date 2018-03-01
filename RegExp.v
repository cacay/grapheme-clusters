Require Import List.
Import ListNotations.

From mathcomp.ssreflect Require Import ssreflect eqtype choice fintype ssrbool ssrfun seq.
From regexp Require Import regexp dfa_to_re automata.


Definition regexp (char : finType) : Type :=
  regexp char.


Definition intersect {char : finType} (r1 r2 : regexp char) : regexp char :=
  Inter r1 r2.


Definition complement {char : finType} (r : regexp char) : regexp char :=
  Neg r.


Definition simplify {char : finType} (r : regexp char) : regexp char :=
  dfa_to_re (minimize (re_to_dfa r)).
