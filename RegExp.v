Require Import List.
Import ListNotations.


Inductive RegExp {C : Type} :=
  | Symbol : C -> RegExp
  | Empty : RegExp
  | None : RegExp
  | Or : RegExp -> RegExp -> RegExp
  | Concat : RegExp -> RegExp -> RegExp
  | Many : RegExp -> RegExp
  | Not : RegExp -> RegExp
  | And : RegExp -> RegExp -> RegExp.


Inductive Matches {C : Type} : RegExp -> list C -> Prop :=
  | MSymbol : forall (c : C), Matches (Symbol c) [c]
  | MEmpty : Matches Empty []
  | MOrLeft : forall (r1 r2 : RegExp) (s1 : list C),
      Matches r1 s1 -> Matches (Or r1 r2) s1
  | MOrRight : forall (r1 r2 : RegExp) (s2 : list C),
      Matches r2 s2 -> Matches (Or r1 r2) s2
  | MConcat : forall (r1 r2 : RegExp) (s1 s2 : list C),
      Matches r1 s1 ->
      Matches r2 s2 ->
      Matches (Concat r1 r2) (s1 ++ s2)
  | MManyZero : forall (r : RegExp), Matches (Many r) []
  | MManySucc : forall (r : RegExp) (h t : list C),
      Matches r h ->
      Matches (Many r) t ->
      Matches (Many r) (h ++ t)
  (* | MNot : forall (r : RegExp) (s : list C),
      ~(Matches r s) ->
      Matches (Not r) s.
   *)
  | MAnd : forall (r1 r2 : RegExp) (s : list C),
      Matches r1 s ->
      Matches r2 s ->
      Matches (And r1 r2) s.