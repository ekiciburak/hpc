(**************************************************************************)
(*  This is part of EXCEPTIONS-PL, it is distributed under the terms of   *)
(*         the GNU Lesser General Public License version 3                *)
(*              (see file LICENSE for more details)                       *)
(*                                                                        *)
(*       Copyright 2015: Jean-Guillaume Dumas, Dominique Duval            *)
(*			 Burak Ekici, Damien Pous.                        *)
(**************************************************************************)


Require Import Relations Morphisms.
Require Import Program.
Require Prerequistes.

Module Make(Import M: Prerequistes.T).

 Inductive termpl: Type -> Type -> Type := 
  | pl_tpure: forall {X Y: Type}, (X -> Y) -> termpl Y X 
  | pl_comp: forall {X Y Z: Type}, termpl X Y -> termpl Y Z -> termpl X Z 
  | throw: forall {X} (e: EName), termpl X (Val e)
  | try_catch: forall {X Y} (e: EName), termpl Y X -> termpl Y (Val e) -> termpl Y X.

 Notation "a 'O' b" := (pl_comp a b) (at level 70).

 (*Definition emptyfun (X: Type) (e: Empty_set) : X := match e with end.
 Definition pl_empty X: termpl X Empty_set := pl_tpure (emptyfun X).*)
 Definition pl_id {X: Type} : termpl X X := pl_tpure (Datatypes.id).
 Definition const {A B} (a : A) := fun _ : B => a.

End Make.
