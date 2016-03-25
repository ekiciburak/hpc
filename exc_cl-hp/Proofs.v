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
Require Prerequistes Terms Decorations Axioms.
Set Implicit Arguments.

Module Make(Import M: Prerequistes.T).
  Module Export ProofsExp := Axioms.Make(M).

(** **)
(** For the sake of simplicity, suppose that there is only one exception name. **)


Parameter e : EName.
Parameter EName_eq: forall e f: EName, e=f.


 Lemma atu: forall l: EName,
  (tag l) o (untag l) == (@id empty_set).
 Proof.
    intros. remember eeffect.
    specialize(@eeffect _ (tag l o untag l) (@id empty_set)).
    intros. apply H. intros. destruct(Exc_dec t l). rewrite e0.
    (* case t = l *)
    setoid_rewrite idt. setoid_rewrite <- ids at 6.
    rewrite <- assoc. apply wrepl; [reflexivity| ]. apply ax1.
    (* case t <> l *)
    transitivity((tag l) o (@empty (Val l)) o (tag t)).
    rewrite <- assoc. rewrite <- assoc. apply wrepl; [reflexivity| ].
    apply ax2. assumption.
    apply stow. apply replsubs; [| reflexivity].
    setoid_rewrite s_empty; [reflexivity | edecorate | edecorate].
 Qed.

(** **)
(** Some intermediate properties used to prove the main theorem. **)

 Lemma Lemma_6_10_2_P1: tag e o untag e == id.
 Proof. apply atu. Qed.


 Lemma Lemma_6_10_2_P2_1: forall (Y: Type) (u1 u2: term (Val e) Y), EPURE u1 -> EPURE u2 -> 
                 ((untag e o tag e o u1) == (untag e o tag e o u2) <-> (u1 == u2)).
 Proof. intros Y u1 u2 H1 H2. split.
          intro H3.
            apply wtos. edecorate. edecorate.
              transitivity ((untag e o tag e) o u1). setoid_rewrite <- idt at 1.
              apply pwsubs. apply wsym, ax1. unfold pure_id. split; [assumption| reflexivity].
              apply wsym.
              transitivity ((untag e o tag e) o u2). setoid_rewrite <- idt at 1.
              apply pwsubs. apply wsym, ax1. unfold pure_id. split; [assumption| reflexivity].
              apply stow. apply sym, H3.
           intro H3.
             apply replsubs; [reflexivity| apply H3].
 Qed.

 Lemma Lemma_6_10_2_P2_2: forall (Y: Type) (u1 u2: term (Val e) Y), EPURE u1 -> EPURE u2 -> 
                 ((tag e o u1) == (tag e o u2) <-> (untag e o tag e o u1) == (untag e o tag e o u2)).
 Proof. intros Y u1 u2 H1 H2. split.
          intro H3. setoid_rewrite <- assoc. apply replsubs, H3; reflexivity.
          intro H3. apply stow in H3. 
            cut(u1 ~ u2). intro H4. apply replsubs; [reflexivity| ]. apply wtos.
              edecorate. edecorate. apply H4.
              transitivity (untag e o tag e o u1). setoid_rewrite <- idt at 1.
              apply pwsubs. apply wsym, ax1. unfold pure_id; split; [assumption| reflexivity] .
              apply wsym.
              transitivity ((untag e o tag e) o u2). setoid_rewrite <- idt at 1.
              apply pwsubs. apply wsym; rewrite ax1; reflexivity.
                unfold pure_id. split; [assumption| reflexivity].
              apply wsym, H3.
 Qed.

 Lemma Lemma_6_10_2_P2_3: forall (Y: Type) (u1 u2: term (Val e) Y), EPURE u1 -> EPURE u2 -> 
                 ((tag e o u1) == (tag e o u2) <-> (u1 == u2)).
 Proof. intros Y u1 u2 H1 H2. split.
          intro H3.
            apply wtos.
              edecorate. edecorate.
                apply Lemma_6_10_2_P2_2 in H3; [ |assumption | assumption].
              setoid_rewrite <- assoc in H3. apply stow in H3.
                transitivity ((untag e o tag e) o u1). setoid_rewrite <- idt at 1.
                apply pwsubs. apply wsym, ax1. unfold pure_id. split; [assumption| reflexivity]. 
                apply wsym.
                transitivity ((untag e o tag e) o u2). setoid_rewrite <- idt at 1.
                apply pwsubs. apply wsym, ax1. unfold pure_id. split; [assumption| reflexivity]. 
                setoid_rewrite <- assoc. apply wsym, H3.
           intro H3.
             apply replsubs; [reflexivity | apply H3].
 Qed.

 Lemma Lemma_6_10_2_P3: forall (Y: Type) (f1 f2: term Y (Val e)), (f1 o untag e == f2 o untag e) <-> f1 ~ f2.
 Proof. intros X f1 f2. split.
          intro H1. 
          setoid_rewrite <- ids. setoid_rewrite <- ax1.
          apply stow. setoid_rewrite assoc.
          apply replsubs; [exact H1| reflexivity].
          intro H1.
          apply eeffect. intro t. destruct (EName_eq e t). setoid_rewrite <- assoc.
          remember wrepl. setoid_rewrite ax1. setoid_rewrite ids. exact H1.
 Qed.

End Make.