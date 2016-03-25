(**************************************************************************)
(*  This is part of EXCEPTIONS-CL, it is distributed under the terms of   *)
(*         the GNU Lesser General Public License version 3                *)
(*              (see file LICENSE for more details)                       *)
(*                                                                        *)
(*       Copyright 2015: Jean-Guillaume Dumas, Dominique Duval            *)
(*			 Burak Ekici, Damien Pous.                        *)
(**************************************************************************)

Require Import Relations Morphisms Bool.
Require Import Program.
Require Prerequistes Terms.
Set Implicit Arguments.

Module Make(Import M: Prerequistes.T).
  Module Export DecorationsExp := Terms.Make(M). 

 Inductive kind := epure | ppg | ctc. 

 Inductive is: kind -> forall X Y, term X Y -> Prop :=
 | is_tpure: forall X Y (f: X -> Y), is epure (tpure f)
 | is_comp: forall k X Y Z (f: term X Y) (g: term Y Z), is k f -> is k g -> is k (f o g)
 | is_tag: forall t, is ppg (tag t)	
 | is_untag: forall t, is ctc (untag t)
 | is_epure_ppg: forall X Y (f: term X Y), is epure f -> is ppg f 
 | is_ppg_ctc: forall X Y  (f: term X Y), is ppg f -> is ctc f.
 

 Hint Constructors is.

Fixpoint fix_has_no_catcher X Y (f: term X Y): bool :=
   match f with
     | untag _ => false
     | comp _ _ _ f g => (fix_has_no_catcher f) && (fix_has_no_catcher g)
     | _ => true
   end.

Definition has_no_catcher X Y (f : term X Y) : Prop := fix_has_no_catcher f = true.

Fixpoint fix_has_no_propagator X Y (f: term X Y): bool :=
   match f with
     | tag _ => false
     | comp _ _ _ f g => fix_has_no_propagator f && fix_has_no_propagator g
     | _ => true
   end.


Definition has_no_propogator X Y (f : term X Y) : Prop := fix_has_no_propagator f = true.

Definition has_only_pure X Y (f : term X Y) : Prop := fix_has_no_propagator f = true /\ fix_has_no_catcher f = true.


Lemma no_untag_ispropagator : forall X Y (g: term X Y), has_no_catcher g -> is ppg g.
Proof.
  induction g.
  (* tpure *)
  intros. auto.
  (* comp *)
  intros. apply is_comp. unfold has_no_catcher in H.
  simpl in H.
  rewrite ?andb_true_iff in H. 
  destruct H.
  auto. unfold has_no_catcher in H.
  simpl in H.
  rewrite ?andb_true_iff in H.
  destruct H as (H1&H2).
  auto.
  (* tag *)
  intros.  auto.
  (* untag *)
  intros. simpl in H.
  apply diff_false_true in H.
  contradiction H.
Qed.

Lemma onlypurecomp : forall X Y Z (f: term Y X) (g: term Z Y), 
      has_only_pure f /\ has_only_pure g -> has_only_pure (g o f).
Proof.
  intros. unfold has_only_pure. unfold has_only_pure in H.
  split. simpl. rewrite ?andb_true_iff. split. apply H. apply H.
  simpl. rewrite ?andb_true_iff. split. apply H. apply H.
Qed.

Lemma no_untag_tag_ispure : forall X Y (g: term X Y), 
	(has_only_pure g) -> is epure g.
Proof.
    intros. unfold has_only_pure in H. induction g. 
    (* tpure *)
    intros. auto.
    (* comp *) 
    apply is_comp.
    simpl in H.
    rewrite ?andb_true_iff in H.
    destruct H. destruct H. destruct H0.
    apply IHg1. split. apply H.
    apply H0.
    simpl in H.
    rewrite ?andb_true_iff in H.
    destruct H. destruct H. destruct H0.
    apply IHg2. split. apply H1.
    apply H2.
    (* tag *)
    simpl in H. destruct H. contradict H. auto.
    (* untag *)
    simpl in H. destruct H. contradict H0. auto.
Qed.

Lemma eq_catchers_eq_propags_lemma1 : forall {X Y} (f: term X Y),
	not (has_no_catcher f) -> not (has_only_pure f).
Proof.
intros. contradict H. unfold has_only_pure in H.
unfold has_no_catcher. apply H.
Qed.

Lemma eq_catchers_eq_propags_lemma2 : forall {X Y} (f: term X Y),
	not (is ctc f) -> not (has_no_catcher f).
Proof.
intros. contradict H. apply is_ppg_ctc. apply no_untag_ispropagator. 
assumption.
Qed.


 Ltac edecorate :=  solve[
                          repeat (apply is_comp)
                            ||
		                 (apply is_tpure || apply is_tag || apply is_untag || assumption)
                            ||
                                 (((apply no_untag_tag_ispure; assumption) || (apply no_untag_ispropagator; assumption))
			    || 
                                 ((apply is_epure_ppg; assumption)  || (apply is_ppg_ctc; assumption)))
                            ||
                                 (apply is_epure_ppg)
                            ||
                                 (apply is_ppg_ctc)
                        ].

 Class EPURE {A B: Type} (f: term A B) := isp : is epure f.
 Hint Extern 0 (EPURE _) => edecorate : typeclass_instances.

 Class PPG {A B: Type} (f: term A B) := ispropag : is ppg f.
 Hint Extern 0 (PPG _) => edecorate : typeclass_instances.

 Class CTC {A B: Type} (f: term A B) := ireplsubstc : is ctc f.
 Hint Extern 0 (CTC _) => edecorate : typeclass_instances.


End Make.
