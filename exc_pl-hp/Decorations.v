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
Require Prerequistes Terms.
Set Implicit Arguments.

Module Make(Import M: Prerequistes.T).
  Module Export DecorationsExp := Terms.Make(M). 

 Inductive kindpl := pl_epure | pl_ppg.

 Inductive is_pl: kindpl -> forall X Y, termpl X Y -> Prop :=
 | is_pl_tpure: forall X Y (f: X -> Y), is_pl pl_epure (@pl_tpure X Y f)
 | is_pl_comp: forall k X Y Z (f: termpl X Y) (g: termpl Y Z), is_pl k f -> is_pl k g -> is_pl k (f O g)
 | is_throw: forall X (e: EName), is_pl pl_ppg (@throw X e)
 | is_try_catch: forall X Y (e: EName) (a: termpl Y X) (b: termpl Y (Val e)), is_pl pl_ppg (@try_catch _ _ e a b)
 | is_pl_pure_ppg: forall X Y (f: termpl X Y), is_pl pl_epure f -> is_pl pl_ppg f.

 Hint Constructors is_pl.

 Ltac pl_edecorate :=  solve[
                          repeat (apply is_pl_comp)
                            ||
		                 (apply is_pl_tpure || apply is_throw || apply is_try_catch || apply is_pl_pure_ppg || assumption)
			    || 
                                 (apply is_pl_pure_ppg)
                        ].
 Class PL_EPURE {A B: Type} (f: termpl A B) := isplp : is_pl pl_epure f.
 Class PL_PPG {A B: Type} (f: termpl A B) := isplthrw : is_pl pl_ppg f.

 Fixpoint fix_has_no_propagator X Y (f: termpl X Y): bool :=
   match f with
     | throw _ _         => false
     | try_catch _ _ _ _ _   => false
     | pl_comp _ _ _ f g => fix_has_no_propagator f && fix_has_no_propagator g
     | _ => true
   end.

 Definition has_no_propogator X Y (f : termpl X Y) : Prop := fix_has_no_propagator f = true.
 Definition has_only_pure X Y (f : termpl X Y) : Prop := fix_has_no_propagator f = true.


 Lemma onlypurecomp : forall X Y Z (f: termpl Y X) (g: termpl Z Y), 
      has_only_pure f /\ has_only_pure g -> has_only_pure (g O f).
 Proof.
  intros. unfold has_only_pure. simpl. rewrite andb_true_iff.
  split; apply H.
 Qed.

 Lemma no_untag_tag_ispure : forall X Y (g: termpl X Y), 
	(has_only_pure g) -> PL_EPURE g.
 Proof.
    intros. unfold has_only_pure in H. induction g. 
    (* tpure *)
    apply is_pl_tpure.
    (* comp *) 
    apply is_pl_comp. simpl in H.
    rewrite ?andb_true_iff in H.
    destruct H. destruct H. destruct H0.
    apply IHg1. reflexivity.
    simpl in H.
    rewrite ?andb_true_iff in H.
    destruct H. destruct H. destruct H0.
    apply IHg2. reflexivity.  
    (* throw *)
    simpl in H. contradict H. auto.
    (* try/catch *)
    simpl in H. contradict H. auto.
 Qed.


End Make.
