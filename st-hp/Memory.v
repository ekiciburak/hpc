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
Require Import Le Gt Minus Bool Setoid.
Set Implicit Arguments.

Module Type T.
 Parameter Loc: Type.
 Parameter Val: Loc -> Type.
 Parameter Loc_dec: forall i j: Loc, {i=j}+{i<>j}.
 Inductive empty_set : Type :=.
End T.


