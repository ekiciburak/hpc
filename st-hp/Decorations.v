(**************************************************************************)
(*  This is part of STATES-HP, it is distributed under the terms of the   *)
(*         GNU Lesser General Public License version 3                    *)
(*              (see file LICENSE for more details)                       *)
(*                                                                        *)
(*       Copyright 2015: Jean-Guillaume Dumas, Dominique Duval            *)
(*			 Burak Ekici, Damien Pous.                        *)
(**************************************************************************)

Require Import Relations Morphisms Bool.
Require Import Program.
Require Memory Terms.
Set Implicit Arguments.

Module Make(Import M: Memory.T).
  Module Export DecorationsExp := Terms.Make(M). 

 Inductive kind := pure | ro | rw. 

 Inductive is: kind -> forall X Y, term X Y -> Prop :=  
 | is_kX: forall (X: Type) (p: (X <> empty_set)), is pure (@kX X p)
 | is_tpure: forall X Y (f: X -> Y), is pure (@tpure X Y f)
 | is_comp: forall k X Y Z (f: term X Y) (g: term Y Z), is k f -> is k g -> is k (f o g)
 | is_lookup: forall i, is ro (lookup i)
 | is_update: forall i, is rw (update i)
 | is_pure_ro: forall X Y (f: term X Y), is pure f -> is ro f 
 | is_ro_rw: forall X Y  (f: term X Y), is ro f -> is rw f.

 Hint Constructors is.

 Fixpoint fix_has_no_update X Y (f: term X Y): bool :=
   match f with
     | update _ => false
     | comp _ _ _ f g => fix_has_no_update f && fix_has_no_update g
     | _ => true
   end.

 Definition has_no_update X Y (f : term X Y) : Prop := fix_has_no_update f = true.

 Fixpoint fix_has_no_lookup X Y (f: term X Y): bool := 
   match f with
     | lookup _ => false
     | comp _ _ _ f g => fix_has_no_lookup f && fix_has_no_lookup g     
     | _ => true
   end.

 Definition has_no_lookup X Y (f : term X Y) : Prop := fix_has_no_lookup f = true.

 Definition has_only_pure X Y (f : term X Y) : Prop := fix_has_no_lookup f = true /\ fix_has_no_update f = true.


Lemma no_upd_isro : forall X Y (g: term X Y), has_no_update g -> is ro g.
Proof.
induction g.
(* kX *)
auto.
(* tpure *)
auto.
(* comp *)
intros. apply is_comp. unfold has_no_update in H.
simpl in H.
rewrite ?andb_true_iff in H. 
destruct H.
auto. unfold has_no_update in H.
simpl in H.
rewrite ?andb_true_iff in H.
destruct H as (H1&H2).
 auto.
(* lookup *)
auto.
(* update *)
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

Lemma no_upd_lkp_ispure : forall X Y (g: term X Y), 
	(has_only_pure g) -> is pure g.
Proof.
    intros. unfold has_only_pure in H. induction g. 
    (* kX *)
    auto.
    (* tpure *)
    auto.
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
    (* lookup *)
    simpl in H. destruct H. contradict H. auto.
    (* update *)
    simpl in H. destruct H. contradict H0. auto.
Qed.

 Lemma neg_has_no_update : forall {X Y} (f: term Y X),
	not (has_no_update f) -> not (has_only_pure f).
 Proof.
   intros X Y f H. contradict H. unfold has_only_pure in H. apply H. Qed.

 Lemma neg_is_rw : forall {X Y} (f: term Y X),
	not (is rw f) -> not (has_no_update f).
 Proof.
   intros X Y f H. contradict H. apply is_ro_rw. apply no_upd_isro.  assumption. Qed.
 
 Ltac decorate :=  solve[
                          repeat (apply is_comp)
                            ||
		                 (apply is_kX || apply is_tpure || apply is_lookup || apply is_update || assumption)
                            ||
                                 (((apply no_upd_lkp_ispure; assumption) || (apply no_upd_isro; assumption))
			    || 
                                 ((apply is_pure_ro; assumption)  || (apply is_ro_rw; assumption)))
                            ||
                                 (apply is_pure_ro)
                            ||
                                 (apply is_ro_rw)
                        ].

 Class PURE {A B: Type} (f: term A B) := isp : is pure f.
 Hint Extern 0 (PURE _) => decorate : typeclass_instances.

 Class RO {A B: Type} (f: term A B) := isro : is ro f.
 Hint Extern 0 (RO _) => decorate : typeclass_instances.

 Class RW {A B: Type} (f: term A B) := isrw : is rw f.
 Hint Extern 0 (RW _) => decorate : typeclass_instances.


End Make.


