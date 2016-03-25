(**************************************************************************)
(*  This is part of STATES-HP, it is distributed under the terms of the   *)
(*         GNU Lesser General Public License version 3                    *)
(*              (see file LICENSE for more details)                       *)
(*                                                                        *)
(*       Copyright 2015: Jean-Guillaume Dumas, Dominique Duval            *)
(*			 Burak Ekici, Damien Pous.                        *)
(**************************************************************************)

Require Import Relations Morphisms.
Require Import Program.
Require Memory.
Set Implicit Arguments.

Module Make(Import M: Memory.T).

 Inductive term: Type -> Type -> Type :=
  | kX: forall (X: Type), (X <> empty_set) -> term X unit
  | tpure:  forall {X Y: Type}, (X -> Y) -> term Y X  
  | comp: forall {X Y Z: Type}, term X Y -> term Y Z -> term X Z 
  | lookup: forall i:Loc, term (Val i) unit	
  | update: forall i:Loc, term unit (Val i).

 Infix "o" := comp (at level 70).

 Definition id  {X: Type}                     : term X X         := tpure id.
 Definition pi1 {X Y: Type}                   : term X (X*Y)     := tpure fst. 
 Definition pi2 {X Y: Type}                   : term Y (X*Y)     := tpure snd.
 Definition forget {X: Type}                  : term unit X      := tpure (fun _ => tt).
 Definition emptyfun (X: Type) (e: empty_set) : X                := match e with end.
 Definition empty (X: Type)                   : term X empty_set := tpure (emptyfun X).

End Make.

