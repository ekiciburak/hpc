(**************************************************************************)
(*  This is part of EXCEPTIONS-CL, it is distributed under the terms of   *)
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

 Inductive term: Type -> Type -> Type := 
  | tpure: forall {X Y: Type}, (X -> Y) -> term Y X
  | comp: forall {X Y Z: Type}, term X Y -> term Y Z -> term X Z 
  | tag: forall t:EName, term empty_set (Val t)	
  | untag: forall t:EName, term (Val t) empty_set.

 Infix "o" := comp (at level 70).

 Definition id  {X: Type}       : term X X         := tpure id.
 
 Definition emptyfun (X: Type) (e: empty_set) : X := match e with end.
 Definition empty X: term X empty_set := tpure (emptyfun X).

 (*category theoretic approach*)
(* Definition constant {A B} (a: term A unit) := a o (@forget B). *)


End Make.
