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
Require Prerequistes Terms Decorations.
Set Implicit Arguments.

Module Make(Import M: Prerequistes.T).
  Module Export AxiomsExp := Decorations.Make(M). 

 Reserved Notation "x == y" (at level 80).
 Reserved Notation "x ~ y" (at level 80).

 Definition pure_id X Y (x y: term X Y) := is epure x /\ x = y.
 Definition not_ (A:Prop) := A -> False.
 Definition idem X Y (x y: term X Y) := x = y.

 Inductive strong: forall X Y, relation (term X Y) := 
 | refl: forall X Y (f: term X Y), f == f 
 | sym: forall X Y, Symmetric (@strong X Y)
 | trans: forall X Y, Transitive (@strong X Y)
 | assoc: forall X Y Z T (f: term X Y) (g: term Y Z) (h: term Z T), f o (g o h) == (f o g) o h
 | ids: forall X Y (f: term X Y), f o id == f
 | idt: forall X Y (f: term X Y), id o f == f
 | replsubs: forall X Y Z, Proper (@strong X Y ==> @strong Y Z ==> @strong X Z) comp (*enables rewriting*)
 | wtos: forall  X Y (f g: term X Y), PPG f -> PPG g -> f ~ g -> f == g
 | eeffect: forall X (f g: term X empty_set), (forall t: EName, f o tag t ~ g o tag t) -> f == g (* dual to observation *)
 | elocal_global: forall X Y (f g: term Y X), f ~ g -> (f o (@empty X) == g o (@empty X)) -> f == g (* effect measure - Dumas et al.'12 *)
 | mono: forall {X Y: Type} (f g: term empty_set Y), (has_no_catcher f) /\ (has_no_catcher g) -> ((@empty X) o f == (@empty X) o g)-> f == g
 | tcomp: forall X Y Z (f: Z -> Y) (g: Y -> X), tpure (compose g f) == tpure g o tpure f
 with weak: forall X Y, relation (term X Y) := 
 | wsym: forall X Y, Symmetric (@weak X Y)
 | wtrans: forall X Y, Transitive (@weak X Y)
 | wrepl : forall A B C, Proper (@idem C B ==> @weak B A ==> @weak C A) comp
 | pwsubs : forall A B C, Proper (@weak C B ==> @pure_id B A ==> @weak C A) comp  
 | w_empty: forall X (f: term X empty_set), f ~ (@empty X)	
 | ax1: forall t: EName, untag t o tag t ~ (@id (Val t))
 | ax2: forall t1: EName, forall t2: EName, t1 <> t2 -> untag t2 o tag t1 ~ (@empty (Val t2)) o tag t1
 | stow: forall  X Y (f g: term X Y), f == g -> f ~ g
   where "x == y" := (strong x y)
   and "x ~ y" := (weak x y).

 Instance strong_is_equivalence X Y: Equivalence (@strong X Y).
 Proof. constructor; intro. apply refl. apply sym. apply trans. Qed.

 Instance weak_is_equivalence X Y: Equivalence (@weak X Y).
 Proof. constructor; intro. apply stow. apply refl. intros. apply wsym. assumption. apply wtrans. Qed.

 Instance strong_is_weak_equivalence: forall X Y, subrelation (@strong X Y) (@weak X Y).
 Proof. constructor. apply stow,sym. assumption. Qed.

 Lemma s_empty: forall X (f: term X empty_set), (PPG f) -> f == (@empty X).
 Proof. intros X f H. apply wtos; [exact H| edecorate| apply w_empty]. Qed.

 Existing Instance wrepl.
 Existing Instance pwsubs.
 Existing Instance replsubs.


End Make.