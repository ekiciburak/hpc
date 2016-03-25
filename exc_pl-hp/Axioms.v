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
Require Prerequistes Terms Decorations.
Set Implicit Arguments.

Module Make(Import M: Prerequistes.T).
  Module Export AxiomsExp := Decorations.Make(M). 

 Reserved Notation "x *== y" (at level 80).

 Inductive pl_strong: forall X Y, relation (termpl X Y) := 
 | pl_refl: forall X Y (f: termpl X Y), f *== f 
 | pl_sym: forall X Y, Symmetric (@pl_strong X Y)
 | pl_trans: forall X Y, Transitive (@pl_strong X Y)
 | pl_assoc: forall X Y Z T (f: termpl X Y) (g: termpl Y Z) (h: termpl Z T), f O (g O h) *== (f O g) O h
 | pl_ids: forall X Y (f: termpl X Y), f O pl_id  *== f
 | pl_idt: forall X Y (f: termpl X Y), pl_id O f  *== f
(* | pl_s_empty: forall X (f: termpl X Empty_set), f  *== (@pl_empty X)  *)
 | pl_replsubs: forall X Y Z, Proper (@pl_strong X Y ==> @pl_strong Y Z  ==> @pl_strong X Z) (pl_comp) 
     (*for throw and try/catch*)
 | ppg : forall X Y e (f: termpl X Y), f O (@throw Y e)  *== (@throw X e)   
 | rcv : forall X Y e (f g: termpl (Val e) Y), (@throw X e) O f  *== (@throw X e) O g -> f  *== g 
 | try : forall X Y e (a1 a2: termpl X Y) (b: termpl X (Val e)), a1 *== a2 -> try_catch e a1 b  *== try_catch e a2 b (* FIXED *)
(* | try : forall X Y e, Proper (@pl_strong X Y  ==> @pl_strong X (Val e)  ==> @pl_strong X Y) (try_catch e) *)
 | try0: forall X Y e (u: termpl X Y) (g: termpl X (Val e)), PL_EPURE u -> try_catch e u g  *== u
 | try1: forall X Y e (v: termpl (Val e) Y) (g: termpl X (Val e)), PL_EPURE v ->
 		try_catch e ((@throw X e) O v) g  *== g O v
 | pl_tcomp: forall X Y Z (f: Z -> Y) (g: Y -> X), pl_tpure (compose g f) *== pl_tpure g O pl_tpure f
   where "x  *== y" := (pl_strong x y).

 Instance pl_strong_is_equivalence X Y: Equivalence (@pl_strong X Y).
 Proof. constructor; intro. apply pl_refl. apply pl_sym. apply pl_trans. Qed.

 Existing Instance pl_replsubs.
 (* Existing Instance try. *)

End Make.
