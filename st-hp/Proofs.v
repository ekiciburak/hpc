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
Require Memory Terms Decorations Axioms.
Set Implicit Arguments.

Module Make(Import M: Memory.T).
  Module Export ProofsExp := Axioms.Make(M).

(** **)
(* To simplify, there is a SINGLE location *)
Parameter i : Loc.
Parameter Loc_eq: forall i j: Loc, i=j.

(* --- Main Proofs --- *)

Lemma ALU: forall i: Loc, update i o lookup i == id.
 Proof.
     intro i. apply local_global. intro k. 
     destruct (Loc_dec i k) as [e|n]. rewrite <- e.
     (*Case k = i *)  
     rewrite assoc.
     rewrite ax1. 
     rewrite ids, idt. 
     reflexivity.
     (*Case k <> i *) 
     rewrite assoc.
     rewrite ax2;[| exact n].
     rewrite <- assoc.
     rewrite s_unit;[| decorate]. 
     cut (forget == id). 
       intro H1. rewrite H1. 
       reflexivity.
     (* 1st cut *) (* forget $==$ id *)
     symmetry. apply s_unit. decorate. (* (2.4) *)
 Qed.

Lemma ILL: forall i, lookup i o forget o lookup i == lookup i.
 Proof.
      intro i. rewrite <- assoc.
      rewrite s_unit; [| decorate]. (* (1) *) (*li o 1 == li *)
      cut (forget == id).
        intro H0. rewrite H0, ids. (* (2) *) (*li == li *)
        reflexivity.
      (*1st cut*) (* forget == id *)
      symmetry. apply s_unit; decorate. (* (3) *)
 Qed.

(** **)
(** Some intermediate properties used to prove the main theorem. **)

 Lemma Lemma_5_5_2P1_1: forall (Y: Type) (u1 u2: term Y (Val i)), is pure u1 -> is pure u2 -> 
                 ((u1 o lookup i) == (u2 o lookup i) <-> (u1 o lookup i o update i) == (u2 o lookup i o update i)).
 Proof. 
     intros Y u1 u2 H1 H2. split.
       intro H3. 
         apply replsubs; [| reflexivity]. apply H3.
       intro H3. apply stow in H3. setoid_rewrite <- assoc in H3.
         setoid_rewrite ax1 in H3. setoid_rewrite ids in H3.
         apply replsubs; [| reflexivity].
         apply wtos;[decorate| decorate| exact H3].
 Qed.

 Lemma Lemma_5_5_2P1_2: forall (Y: Type) (u1 u2: term Y (Val i)), is pure u1 -> is pure u2 -> 
                 ((u1 o lookup i o update i) == (u2 o lookup i o update i) <-> (u1 == u2)).
 Proof. 
     intros Y u1 u2 H1 H2. split.
       intro H3.
         apply stow in H3.
         setoid_rewrite <- assoc in H3. setoid_rewrite ax1 in H3.
         setoid_rewrite ids in H3.
         apply wtos; [decorate| decorate| exact H3].
       intro H3.
         rewrite H3; reflexivity.
 Qed.

 Lemma Lemma_5_5_2P1_3: forall (Y: Type) (u1 u2: term Y (Val i)), is pure u1 -> is pure u2 -> 
                 ((u1 o lookup i) == (u2 o lookup i) <-> (u1 == u2)).
 Proof. 
     intros Y u1 u2 H1 H2. split.
       intro H3.
         apply wtos; [decorate| decorate| ].
         setoid_rewrite <- ids. setoid_rewrite <- ax1.
         apply stow. setoid_rewrite assoc.
         apply replsubs; [exact H3| reflexivity].
       intro H3.
         rewrite H3; reflexivity.
 Qed.
            
 Lemma Lemma_5_5_2P2: forall (Y: Type) (u: term Y (Val i)) (v: term Y unit), is pure u -> is pure v -> 
               ((u o lookup i == v) <-> (u == v o forget)).
 Proof.
      intros Y u v H1 H2. split.
        intro H3.
          apply Lemma_5_5_2P1_2; [decorate| decorate| ].
          rewrite <- H3. do 2 setoid_rewrite <- assoc at 3.
          setoid_rewrite assoc at 2.
          rewrite ILL. reflexivity.
        intro H3.
          rewrite H3. setoid_rewrite <- ids at 6.
          rewrite <- assoc. apply replsubs; [reflexivity| ].
          setoid_rewrite s_unit; [reflexivity| decorate| decorate].
 Qed.

 Lemma Lemma_5_5_2P3: forall (X: Type) (f1 f2: term (Val i) X), (update i o f1 == update i o f2) <-> f1 ~ f2.
 Proof. intros X f1 f2. split.
          intro H1.
            setoid_rewrite <- idt. setoid_rewrite <- ax1.
            apply stow. setoid_rewrite <- assoc.
            apply replsubs; [reflexivity| exact H1].
          intro H1. apply local_global.
            intro j. destruct (Loc_eq i j).
            setoid_rewrite assoc.
            setoid_rewrite ax1. setoid_rewrite idt.
            exact H1.
 Qed.


(* -------------------- End of Main Proofs -------------------- *)

End Make.
