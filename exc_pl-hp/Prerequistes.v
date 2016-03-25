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
Require Import Le Gt Minus Bool Setoid.
Set Implicit Arguments.

Module Type T.

 Parameter EName: Type.
 Parameter Val: EName -> Type.
 Parameter Exc_dec: forall i j: EName, {i=j}+{i<>j}.
 Inductive empty_set : Type :=.
 Inductive unit: Type := unt.
 Parameter B: Type.

End T.


