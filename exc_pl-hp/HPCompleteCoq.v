(**************************************************************************)
(*  This is part of EXCEPTIONS-PL, it is distributed under the terms of   *)
(*         the GNU Lesser General Public License version 3                *)
(*              (see file LICENSE for more details)                       *)
(*                                                                        *)
(*       Copyright 2015: Jean-Guillaume Dumas, Dominique Duval            *)
(*			 Burak Ekici, Damien Pous.                        *)
(**************************************************************************)

Require Import Relations Morphisms Bool.
Require Import Program.
Require Prerequistes Terms Decorations Axioms.
Set Implicit Arguments.
Module Make(Import M: Prerequistes.T).
Module Export HPExp := Axioms.Make(M).
Axiom excludedmiddle: forall P, P \/ ~P.
Axiom dblnegelim    : forall P, ~~P -> P.

(** **)
(** For the sake of simplicity, suppose that there is only one exception name. **)
Parameter e : EName.
Parameter EName_eq: forall e f: EName, e=f.

(** **)
(** Canonical form for throwers: for an exception thrower f: Y -> X, either there exists a pure term u: Y -> X 
such that f is u or there exists a pure term v: Y -> (Val e) such that f is of the form: "tr o v". **)
Theorem Proposition_6_9_2: forall {X Y} (f: termpl X Y),
              (exists u: (termpl X Y), PL_EPURE u /\ f *== u)
                 \/
              (exists v: (termpl (Val e) Y), PL_EPURE v /\ f *== (@throw X e) O v).
Proof. intros X Y f.
         induction f.
           left. exists (@pl_tpure _ _ y). split. apply is_pl_tpure. reflexivity.
           destruct IHf1. destruct H as (u1&Ha&Hb).
           destruct IHf2. destruct H as (u2&H1a&H1b).
             left. exists (u1 O u2). split. pl_edecorate.
               remember pl_replsubs; rewrite Hb, H1b. reflexivity.
             destruct H as (u2&H1a&H1b).
               right. exists u2. split; auto.
                 remember pl_replsubs; rewrite H1b, pl_assoc. apply pl_replsubs; [apply ppg| reflexivity].
           destruct IHf2. destruct H as (u1&Ha&Hb). destruct H0 as (u2&H1a&H1b).
             right. exists (u1 O u2). split. pl_edecorate. 
               remember pl_replsubs; rewrite Hb, H1b. rewrite pl_assoc; reflexivity.
             destruct H as (u1&Ha&Hb). destruct H0 as (u2&H1a&H1b).
               right. exists u2. split; auto.
                 remember pl_replsubs; rewrite Hb, H1b, pl_assoc. apply pl_replsubs; [apply ppg| reflexivity].
           destruct (EName_eq e e0). right. exists (@pl_id (Val e)). 
             split. pl_edecorate. rewrite pl_ids. reflexivity.
           destruct (EName_eq e e0).
             destruct IHf1. destruct H as (u&Ha&Hb). 
               left. exists u. split. auto.
               specialize (@try Y X e f1 u f2). intro H.
               remember try0.
               specialize (@try0 Y X e u f2). intros. apply H0 in Ha. rewrite <- Ha.
               apply H. exact Hb.
             destruct IHf2. destruct H as (v&Ha&Hb). destruct H0 as (u&H1a&H1b).
               left. exists (u O v). split. pl_edecorate.
               remember try1.
               specialize (@try1 _ _ e v u). intro H.
               specialize (@try Y X e f1 (throw e O v) f2). intro H1.
                 apply H1 in Hb. rewrite Hb. rewrite <- H1b.
               apply try1. exact Ha.
               destruct H as (v1&Ha&Hb). destruct H0 as (v2&H1a&H1b).
                 right. exists (v2 O v1). split. pl_edecorate.
               specialize (@try Y X e f1 (throw e O v1) f2). intro H.
                apply H in Hb. rewrite Hb. rewrite pl_assoc. rewrite <- H1b.
                apply try1. exact Ha.
Qed.

(** **)
(** An equation between two exception throwers is equivalent to an equations between pure terms. **)
 Lemma Proposition_6_9_3: forall {X Y} (a1 a2: termpl X Y) (v1 v2: termpl (Val e) Y), 
                                (PL_EPURE v1) /\ (PL_EPURE v2) /\
                                (a1 = ((@throw X e) O v1)) /\ (a2 = ((@throw X e) O v2)) -> ((a1 *== a2) <-> (v1 *== v2)).
 Proof. intros X Y a1 a2 v1 v2 (H1&H2&H3&H4).
          split.
            intro H5.
              rewrite H3, H4 in H5. apply rcv in H5. apply H5.
            intro H5. rewrite H3, H4. remember pl_replsubs; rewrite H5.
              apply pl_replsubs; reflexivity.
 Qed.

 (** **)
 (**  An equality between an exception thrower and a pure term is absurd. **)

 Axiom Axiom_6_9_4: forall {X Y} (a1 v2: termpl X Y) (v1: termpl (Val e) Y), 
                     (PL_EPURE v1) /\ (PL_EPURE v2) /\ (a1 = ((@throw X e) O v1)) -> 
                     ((a1 *== v2) <-> (forall {X Y} (f g: termpl Y X), PL_EPURE f -> PL_EPURE g -> f *== g)).

(** **)
(** An equation between any two terms is either absurd or equivalent to an equation between pure terms.  **)

Theorem Theorem_6_9_5: forall {X Y} (a1 a2: termpl X Y),
              ((exists v1: (termpl (Val e) Y), exists v2: (termpl (Val e) Y), 
               PL_EPURE v1 /\ PL_EPURE v2 /\ (a1 = ((@throw X e) O v1)) /\ (a2 = ((@throw X e) O v2)) ->
               ((a1 *== a2) <-> v1 *== v2))
                \/
               (exists v1: (termpl (Val e) Y), exists v2: (termpl X Y), 
               PL_EPURE v1 /\ PL_EPURE v2 /\ (a1 = ((@throw X e) O v1)) ->
               ((a1 *== v2) <-> (forall {X Y} (f g: termpl Y X), PL_EPURE f -> PL_EPURE g -> f *== g)))
               \/
               (exists v1: (termpl X Y), exists v2: (termpl X Y), 
               PL_EPURE v1 /\ PL_EPURE v2 ->
               (a1 *== a2) <-> v1 *== v2))
               \/
               (a1 *== a2).
Proof. intros X Y a1 a2.
         left.
           specialize(@Proposition_6_9_2 X Y a1). intro H0. destruct H0. destruct H as (u1&Ha&Hb).
           specialize(@Proposition_6_9_2 X Y a2). intro H1. destruct H1. destruct H as (u2&H0a&H0b).
           right. right.             
             exists u1 u2.
               split. intro H1.
                 remember pl_replsubs; rewrite <- Hb. rewrite <- H0b.
                   apply H1. split; assumption.
                 intros H1 H2. rewrite H0b, Hb. apply H1.
           right. left.
             destruct H as (u2&H1b).
             exists u2 u1. intro H1. apply (@Axiom_6_9_4 _ _ a1 u1 u2).
             split. apply H1. split; apply H1. 
         specialize(@Proposition_6_9_2 X Y a2). intro H1. destruct H1; destruct H0 as (u2&H0a&H0b).
           right. left.
             destruct H as (u1&H1b).
             exists u1 u2. intro H1. apply (@Axiom_6_9_4 _ _ a1 u2 u1).
             split. apply H1. split; apply H1.
           left.
             destruct H as (u1&H1b). 
             exists u1 u2. intro H1. apply (@Proposition_6_9_3 _ _ a1 a2 u1 u2).
             split; apply H1.
Qed.

End Make.














