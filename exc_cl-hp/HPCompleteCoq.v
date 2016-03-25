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
Require Prerequistes Terms Decorations Axioms Proofs.
Set Implicit Arguments.

Module Make(Import M: Prerequistes.T).
Module Export ProofsExp := Proofs.Make(M).
Axiom excludedmiddle: forall P, P \/ ~P.
Axiom dblnegelim    : forall P, ~~P -> P.


(** **)
(** Canonical form for propagators: an exception propagator f: Y -> X is either a pure term or a term of the 
form: "empty_X o (tag e) o v" such that empty_X: empty_set -> X and v: Y -> (Val e) are both pure terms.   **)

Lemma Proposition_6_10_3_P1: forall X Y (f: term Y X), has_no_catcher f -> 
    (has_only_pure f)
        \/
        (exists u : (term (Val e) X), exists v : (term Y empty_set),
        (has_only_pure u) /\ (has_no_catcher v) /\ (f == v o (tag e) o u)).
Proof.
    intros. induction f.
    (* tpure *)
    left. unfold has_only_pure. auto.
    (* comp: f == f1 o f2 *)
    destruct IHf1 as [IHf1a|IHf1b]. unfold has_no_catcher in H. simpl in H.
    unfold has_no_catcher. rewrite ?andb_true_iff in H. apply H.
    destruct IHf2 as [IHf2a|IHf2b]. unfold has_no_catcher in H. simpl in H.
    unfold has_no_catcher. rewrite ?andb_true_iff in H. apply H.
    (* f1 and f2 are both pure *) (* (1.1) *)
    left.
      unfold has_only_pure. simpl. rewrite ?andb_true_iff.
      repeat split. apply IHf1a. apply IHf2a. apply IHf1a. apply IHf2a.
    (* f1 is pure and f2 has no catcher *) (* (1.2) *)
    right.
      destruct IHf2b as (u&v&H1).
      exists u (f1 o v).
      split. apply H1.
      split. unfold has_no_catcher. simpl. rewrite ?andb_true_iff.
      unfold has_no_catcher in H. simpl in H. rewrite ?andb_true_iff in H.
      split;[apply H|apply H1]. do 2 rewrite <- assoc. apply replsubs; [reflexivity| ]. 
      rewrite assoc. apply H1.
    destruct IHf2 as [IHf2a|IHf2b].
    simpl in H. rewrite ?andb_true_iff in H. unfold has_no_catcher in H. simpl in H.
    unfold has_no_catcher. rewrite ?andb_true_iff in H. apply H.
    (* f1 has no catcher and f2 is pure *) (* (1.3) *) 
    right.
    destruct IHf1b as (u&v&H1).
    exists (u o f2) v.
    unfold has_only_pure. simpl.
    rewrite ?andb_true_iff. repeat split. apply H1. apply IHf2a.
      apply H1. apply IHf2a. apply H1.
      rewrite assoc. apply replsubs; [| reflexivity]. easy.
    (* f1 and f2 have no catchers *) (* (1.4) *)
    right.
      destruct IHf1b as (u1&v1&(H1a&H1b&H1c)).
      destruct IHf2b as (u2&v2&(H2a&H2b&H2c)).
      exists u2 v1.
      split. assumption. split. assumption. remember replsubs. rewrite H1c, H2c.
      cut (u1 o v2 == (@empty (Val e))).
        intro H3. do 2 setoid_rewrite <- assoc at 3.
        setoid_rewrite assoc at 1. setoid_rewrite <- assoc at 2. rewrite H3.
        do 2 setoid_rewrite <- assoc. do 2 setoid_rewrite assoc at 2.
        cut(tag e o (@empty (Val e)) o tag e == tag e).
          intro H2. rewrite H2. reflexivity. 
        (* 2nd cut *)
        rewrite s_empty. setoid_rewrite <- idt at 4.
        apply replsubs. setoid_rewrite s_empty; [reflexivity| edecorate].
        reflexivity. edecorate.
      (* 1st cut *)
      setoid_rewrite s_empty; [reflexivity| edecorate].  
    (* tag *)
    right. destruct (EName_eq t e).
    exists (@id (Val t)) (@id empty_set).
    split. unfold has_only_pure. auto. split. auto.
    setoid_rewrite -> ids.
    setoid_rewrite -> idt at 1.
    apply refl.
    (* untag *)
    contradict H. unfold not. unfold has_no_catcher.
    intros. simpl in H. congruence.
Qed.

(* an propagator is either pure or of the form (empty o tag o v) *)
Lemma Corollary_6_10_4: forall {X Y} (a: term Y X), has_no_catcher a ->
    ( has_only_pure a
      \/
      (exists v :(term (Val e) X),
        (has_only_pure v) /\ (a == ((@empty Y) o tag e o v))
      )
    ).
Proof.
    intros X Y a H.
    specialize (@Proposition_6_10_3_P1 X Y a).
      intros. destruct H0. assumption. 
    left. assumption.
    right. destruct H0 as (u&v&H2).
      exists u.
        destruct H2 as (H2a&H2b&H2c).
        split. assumption.
        rewrite H2c. rewrite s_empty; [reflexivity| edecorate].
Qed.

(** **)
(** Canonical form for catchers: an exception catcher f: Y -> X is either a propagator or a term of the 
form: "a o (untag e) o (tag e) o u" such that a: (Val e) -> X is a propagator and u: Y -> (Val e) is a pure term.   **)
(* a catcher non propagator has the form (a o untag o tag o v) *)
Lemma Proposition_6_10_3_P2: forall {X Y} (f: term Y X), 
    (has_no_catcher f 
      \/
    (exists a: (term Y (Val e)), exists u: (term (Val e) X), 
    (has_no_catcher a) /\ (has_only_pure u) /\ (f == (a o untag e o tag e o u)))).
Proof.
    intros. induction f.
    (* tpure *)
    left. unfold has_no_catcher. auto.
    (* comp *)
    destruct IHf2 as [IHf2a|IHf2b].      
    destruct IHf1 as [IHf1a|IHf1b].
    (* f1 and f2 no untag *)
    left. simpl. unfold has_no_catcher. simpl. rewrite ?andb_true_iff. auto.
    (* f1 has no untag, f2 has untag *) (* (2.2) *)
    right. destruct IHf1b as (a1&v1&H2).
    specialize (@Proposition_6_10_3_P1 Z Y f2).
    intros. destruct H. assumption.
      (* f2 has only pure *)
      exists a1 (v1 o f2). split. apply H2.
      split. apply onlypurecomp. split. apply H. apply H2.      
      setoid_rewrite assoc. apply replsubs; [apply H2| reflexivity]. 
      (*f2 has tag*)
      destruct H as (u&v2&Ha&Hb&Hc).
      destruct H2 as (H2a&H2b&H2c).
      exists a1 u.
      split. apply H2a. split. apply Ha.
      rewrite H2c, Hc.
      do 2 setoid_rewrite assoc. do 2 setoid_rewrite <- assoc at 3.
      cut(v1 o v2 == (@empty (Val e))).
        intro H1. rewrite H1.
        cut((tag e o (@empty (Val e))) == (@id empty_set)). 
          intro H2. rewrite H2. rewrite ids. reflexivity.
        (* 2nd cut *)
        setoid_rewrite s_empty; [reflexivity| edecorate| edecorate].
      (* 1st cut *)
      setoid_rewrite s_empty; [reflexivity| edecorate].
    right. destruct IHf2b as (a2&v2&H2a&H2b&H2c).
    destruct IHf1 as [IHf1a|IHf1b].
    (* f1 has no untag *) (* (2.3) *)
    exists (f1 o a2) v2. split. unfold has_no_catcher. 
    simpl. rewrite ?andb_true_iff. split. apply IHf1a. apply H2a.
    split. apply H2b. rewrite H2c.
    do 3 setoid_rewrite <- assoc. 
    apply replsubs; [reflexivity| reflexivity].
    (* f1 and f2 has untag *) (* (2.4) *) 
    destruct IHf1b as (a1&v1&H3). 
    specialize (@Proposition_6_10_3_P1 (Val e) Y a2). intros.
    destruct H as [Ha|Hb]. apply H2a.
      (* a2 is pure *) (* (2.4.1) *)
      exists (a1 o v1 o a2) v2.
      split. unfold has_no_catcher. simpl. rewrite ?andb_true_iff.
      repeat split. apply H3. apply H3. apply H2a.
      split. apply H2b.
      destruct H3 as (H3a&H3b&H3c).
      rewrite H2c, H3c.
      do 3 setoid_rewrite assoc.
      do 2 (apply replsubs; [| reflexivity]).
      apply Lemma_6_10_2_P3. apply pwsubs; [| unfold pure_id; split; [apply no_untag_tag_ispure, Ha| reflexivity]].
        apply pwsubs; [| unfold pure_id; split; [apply no_untag_tag_ispure; apply H3b| reflexivity]].
        setoid_rewrite <- ids at 6. rewrite <- assoc.
        apply wrepl. reflexivity. apply ax1.
      (* a2 has tag *) (* (2.4.2) *)
      destruct Hb as (u&w&Hb1&Hb2&Hb3).
      exists (a1 o u) v2. split. 
        unfold has_no_catcher. simpl. rewrite ?andb_true_iff. 
        split. apply H3. apply Hb1.
        split. apply H2b.
        destruct H3 as (H3a&H3b&H3c).
        rewrite H3c, H2c.
        do 3 setoid_rewrite assoc. do 2 (apply replsubs; [| reflexivity]).
        apply Lemma_6_10_2_P3. rewrite Hb3. rewrite assoc.
        apply pwsubs; [| unfold pure_id; split; [apply no_untag_tag_ispure; apply Hb1| reflexivity]].
           do 1 rewrite assoc. setoid_rewrite <- assoc at 2.
           cut((v1 o w) == (@empty (Val e))).
             intro H1. rewrite H1.
             do 2 setoid_rewrite <- assoc at 1.
             setoid_rewrite assoc at 2. 
             cut(tag e o (@empty (Val e)) o tag e == tag e).
               intro H2. rewrite H2.
               setoid_rewrite <- ids at 6. rewrite <- assoc.
               apply wrepl. reflexivity. apply ax1. 
             (* 2nd cut *)
             rewrite s_empty. setoid_rewrite <- idt at 4.
             apply replsubs. setoid_rewrite s_empty; [reflexivity| edecorate].
             reflexivity. edecorate.
           (* 1st cut *)
           setoid_rewrite s_empty; [reflexivity| edecorate].
    (* tag *)
    left. unfold has_no_catcher. easy.
    (* untag *)
    right. destruct (EName_eq t e).
    exists (@id (Val t)) (@empty (Val t)).
      split. easy. split. easy. do 2 rewrite <- assoc.
      rewrite idt. setoid_rewrite <- ids at 1.
      apply replsubs. apply reflexivity.
      setoid_rewrite s_empty; [reflexivity| edecorate| edecorate].
Qed.


(** **)
(** An equation between a propagator and a pure term is absurd. **)
Axiom Assumption_6_10_5: forall {X Y e} (a1: term Y X) (v1: term (Val e) X), (X <> empty_set /\ EPURE a1 /\ EPURE v1 ->
                 a1 == (@empty Y) o (tag e) o v1) <-> (forall {X Y} (f g: term Y X), EPURE f -> EPURE g -> f == g).

(** **)
(** An equation between two strict catchers is equivalent to two equations between propagators.  **)

Lemma Proposition_6_10_7P1: forall {X Y} (a1 a2: term Y (Val e)) (u1 u2: term (Val e) X),
	has_no_catcher a1 /\ has_no_catcher a2 /\ 
        has_only_pure u1 /\ has_only_pure u2 ->
        (((a1 o (untag e) o (tag e) o u1)) ~ (a2 o (untag e) o (tag e) o u2) <-> ( a1 o u1 == a2 o u2 ))
          /\
	(((a1 o (untag e) o (tag e) o u1)) == (a2 o (untag e) o (tag e) o u2) <-> ( a1 == a2 /\ (a1 o u1 == a2 o u2))).
Proof.
      intros X Y a1 a2 u1 u2 (Ha&Hb&Hc&Hd). split.
      split. intro H.
      (* f1 ~ f2 -> a1 o u1 == a2 o u2 *) (* (1.1) *)
      setoid_rewrite <- ids at 2. setoid_rewrite <- ids at 7.
      apply wtos; [edecorate| edecorate| ].
      transitivity(((a1 o untag e) o tag e) o u1).
        repeat rewrite <- assoc.
        apply wrepl; [reflexivity| ].
        rewrite assoc.
        apply pwsubs; [symmetry; apply ax1| ].
          unfold pure_id. split; [apply no_untag_tag_ispure ; assumption| reflexivity].
          symmetry.
      transitivity(((a2 o untag e) o tag e) o u2).
        repeat rewrite <- assoc.
        apply wrepl; [reflexivity| ].
        rewrite assoc.
        apply pwsubs; [symmetry; apply ax1| ].
          unfold pure_id. split; [apply no_untag_tag_ispure ; assumption| reflexivity].
          symmetry.
      exact H.
      (* a1 o u1 == a2 o u2 -> f1 ~ f2 *) (* (1.2) *)
      intro H.
      transitivity(a1 o id o u1).
        apply pwsubs. rewrite <- assoc. apply wrepl.
          reflexivity. apply ax1.
          unfold pure_id. split; [apply no_untag_tag_ispure ; assumption| reflexivity].
          symmetry.
      transitivity(a2 o id o u2).
        apply pwsubs. rewrite <- assoc. apply wrepl.
          reflexivity. apply ax1.
          unfold pure_id. split; [apply no_untag_tag_ispure ; assumption| reflexivity].
          symmetry.
      setoid_rewrite ids. apply stow. exact H.
      (* f1 == f2 -> a1  == a2 and  a1 o u1 == a2 o u2 *) (* (1.3) *)
        split. intro H. split.
        (* f1 == f2 -> a1  == a2 *) (* (1.3.1) *)
        apply wtos; [edecorate| edecorate| ].
        apply Lemma_6_10_2_P3.
        cut(tag e o u1 o (@empty X) == (@id empty_set)).
          intro H1. setoid_rewrite <- ids at 1.
          rewrite <- H1.
          cut(tag e o u2 o (@empty X) == (@id empty_set)).
            intro H2. setoid_rewrite <- ids at 12.
            rewrite <- H2.
            repeat rewrite assoc. apply replsubs; [| reflexivity]. exact H.
          (*2nd cut*)
          setoid_rewrite s_empty; [reflexivity| edecorate| edecorate].
        (*1st cut*)
        setoid_rewrite s_empty; [reflexivity| edecorate| edecorate].
        (* f1 == f2 -> a1 o u1 == a2 o u2 *) (* (1.3.2) *)
        setoid_rewrite <- ids at 2. setoid_rewrite <- ids at 7.
        apply wtos; [edecorate| edecorate| ].
        transitivity(((a1 o untag e) o tag e) o u1).
          repeat rewrite <- assoc.
          apply wrepl; [reflexivity| ].
          rewrite assoc.
        apply pwsubs; [symmetry; apply ax1| ].
          unfold pure_id. split; [apply no_untag_tag_ispure ; assumption| reflexivity].
          symmetry.
        transitivity(((a2 o untag e) o tag e) o u2).
          repeat rewrite <- assoc.
          apply wrepl; [reflexivity| ].
          rewrite assoc.
          apply pwsubs; [symmetry; apply ax1| ].
            unfold pure_id. split; [apply no_untag_tag_ispure ; assumption| reflexivity].
            symmetry.
      apply stow. exact H.
      (* a1  == a2 and a1 o u1 == a2 o u2 -> f1 == f2   *) (* (1.4) *)
      intros (H1&H2).
      apply elocal_global.
        (* a1 == a2 and a1 o u1 == a2 o u2 -> f1 ~ f2   *) (* (1.4.1) *)
        transitivity(a1 o id o u1).
          apply pwsubs. rewrite <- assoc. apply wrepl.
            reflexivity. apply ax1.
            unfold pure_id. split; [apply no_untag_tag_ispure ; assumption| reflexivity].
            symmetry.
        transitivity(a2 o id o u2).
          apply pwsubs. rewrite <- assoc. apply wrepl.
            reflexivity. apply ax1.
            unfold pure_id. split; [apply no_untag_tag_ispure ; assumption| reflexivity].
            symmetry.
        setoid_rewrite ids. apply stow. exact H2.
        (* a1 == a2 and a1 o u1 == a2 o u2 -> f1 o empty == f2 o empty *) (* (1.4.2) *)
        cut(tag e o u1 o (@empty X) == (@id empty_set)).
          intro H3. do 2 setoid_rewrite <- assoc. setoid_rewrite assoc at 2.
          rewrite H3.
          cut(tag e o u2 o (@empty X) == (@id empty_set)).
            intro H4. setoid_rewrite assoc at 2.
            rewrite H4.
            setoid_rewrite ids.
            apply replsubs; [| reflexivity]. exact H1.
          (*2nd cut*)
          setoid_rewrite s_empty; [reflexivity| edecorate| edecorate].
        (*1st cut*)
        setoid_rewrite s_empty; [reflexivity| edecorate| edecorate].
Qed.


(** **)
(** An equation between a strict catcher and a propagator is equivalent to two equations between propagators. **)
Lemma Proposition_6_10_7P2: forall {X Y} (a2 : term Y X) (a1 : term Y (Val e)) (u1: term (Val e) X),
	 has_no_catcher a1 /\ has_only_pure u1 /\  has_no_catcher a2 -> 
             ((a1 o (untag e) o (tag e) o u1) ~ a2 <->  (a2 == a1 o u1))
                 /\
	     ((a1 o (untag e) o (tag e) o u1) == a2 <-> ((a2 == a1 o u1) /\ (a1 == (@empty Y) o tag e))).
Proof.
     intros X Y a2 a1 u1 (Ha&Hb&Hc). split.
     split. intro H.
     (* f1 ~ a2 -> a2 == (a1 o u1) *) (* (2.1) *)
     apply wtos; [edecorate| edecorate| ].
     symmetry. transitivity(((a1 o untag e) o tag e) o u1).
       apply pwsubs. rewrite <- ids at 1. rewrite <- assoc.
         apply wrepl; [reflexivity| symmetry; apply ax1].
       unfold pure_id. split; [apply no_untag_tag_ispure ; assumption| reflexivity].
     exact H.
     (* a2 == (a1 o u1) -> f1 ~ a2  *) (* (2.2) *)
     intro H.
     transitivity(a1 o id o u1).
        apply pwsubs. rewrite <- assoc. apply wrepl.
          reflexivity. apply ax1.
          unfold pure_id. split; [apply no_untag_tag_ispure ; assumption| reflexivity].
          rewrite ids. apply stow. symmetry. exact H.
     split. intro H.
     (* f1 == a2 -> a2 == (a1 o u1) and (empty o tag == a1) *) (* (2.3) *)
       split.
       (* f1 == a2 -> a2 == (a1 o u1) *) (* (2.3.1) *)
       apply wtos; [edecorate| edecorate| ].
         symmetry. transitivity(((a1 o untag e) o tag e) o u1).
         apply pwsubs. rewrite <- ids at 1. rewrite <- assoc.
           apply wrepl; [reflexivity| symmetry; apply ax1].
         unfold pure_id. split; [apply no_untag_tag_ispure ; assumption| reflexivity].
       apply stow. exact H. 
       (* f1 == a2 -> a2 == (empty o tag == a1) *) (* (2.3.2) *)
       apply wtos; [edecorate| edecorate| ].
       setoid_rewrite <- ids at 1.
       rewrite <- ax1. apply stow. rewrite assoc.
       apply replsubs; [| reflexivity].    
       cut(tag e o u1 o (@empty X) == (@id empty_set)).
        intro H1. setoid_rewrite <- ids at 1. setoid_rewrite <- H1.
          cut(a2 o (@empty X) == (@empty Y)).
            intro H2. rewrite <- H2.
            repeat rewrite assoc. apply replsubs; [| reflexivity]. exact H.
          (*2nd cut*)
          setoid_rewrite s_empty; [reflexivity| edecorate].
        (*1st cut*)
        setoid_rewrite s_empty; [reflexivity| edecorate| edecorate].
     (* a2 == (a1 o u1) and (empty o tag == a1) -> f1 == a2 *) (* (2.4) *)
     intros (H1&H2).
     apply elocal_global.
       (* a2 == (a1 o u1) and (empty o tag == a1) -> f1 ~ a2 *) (* (2.4.1) *)
       transitivity(a1 o id o u1).
       apply pwsubs. rewrite <- assoc. apply wrepl.
         reflexivity. apply ax1.
         unfold pure_id. split; [apply no_untag_tag_ispure ; assumption| reflexivity]. 
         symmetry. apply stow. rewrite ids. exact H1.
       (* a2 == (a1 o u1) and (empty o tag == a1) -> f1 o empty == a2 o empty *) (* (2.4.2) *)
       cut(tag e o u1 o (@empty X) == (@id empty_set)).
          intro H3. do 2 setoid_rewrite <- assoc. setoid_rewrite assoc at 2.
          rewrite H3. rewrite ids.
          setoid_rewrite <- ids at 4.
          rewrite <- Lemma_6_10_2_P1. rewrite assoc.
          apply replsubs; [| reflexivity].
          cut(a2 o (@empty X) == (@empty Y)).
            intro H4. rewrite H4. exact H2.
          (*2nd cut*)
          setoid_rewrite s_empty; [reflexivity| edecorate].
        (*1st cut*)
        setoid_rewrite s_empty; [reflexivity| edecorate| edecorate].
Qed.


(** **)
(** An equation between two strict propagators is equivalent to an equation between pure terms. **)
Lemma Proposition_6_10_7P3: forall {X Y} (v1 v2: term (Val e) X),
	has_only_pure v1 /\ has_only_pure v2 ->
             ((((@empty Y) o (tag e) o v1)) == ((@empty Y) o (tag e) o v2) <-> v1 == v2).
Proof.
     intros X Y v1 v2 (Ha&Hb). split. intro H.
     (* a1 == a2 -> v1 == v2 *)
     setoid_rewrite <- assoc in H.
     apply mono in H.
       apply Lemma_6_10_2_P2_3 in H;[exact H| edecorate| edecorate].
       split. unfold has_no_catcher. simpl. apply Ha.
       unfold has_no_catcher. simpl. apply Hb.
     (* v1 == v2 -> a1 == a2 *)
     intro H. apply replsubs, H. reflexivity.
Qed.


(** **)
(** An equation between catchers is equivalent to at most two equations between propagators. **)

(** An equation between propagators is either absurd or equivalent to an equation between pure terms. **)
(** domain is inhabited (Y <> empty_set) **)
Lemma Corollary_6_8_10P1_1: forall {X Y} (a1 a2: term Y X), (X <> empty_set) /\ has_no_catcher a1 /\ has_no_catcher a2 -> 
        ((a1 == a2) <-> (forall {X Y} (f g: term Y X), EPURE f -> EPURE g -> f == g))
         \/
 	(exists v1: (term (Val e) X), exists v2 : (term (Val e) X),
	(has_only_pure v1 /\ has_only_pure v2 /\ 
        (a1 == a2 <-> v1 == v2)))
         \/        	
 	(exists v1: (term Y X), exists v2 : (term Y X),
	(has_only_pure v1 /\ has_only_pure v2 /\ 
        (a1 == a2 <-> v1 == v2))
).
Proof. intros X Y a1 a2 (Ha&Hb&Hc).
        destruct(excludedmiddle (not (has_only_pure a1))).
        destruct(excludedmiddle (not (has_only_pure a2))).
          (* f1 and f2 are propagators *) (* (1.1) *)     
          destruct(@Corollary_6_10_4 X Y a1). auto. contradiction.
          destruct(@Corollary_6_10_4 X Y a2). auto. contradiction.
            destruct H1 as (v1&H1a&H1b).
            destruct H2 as (v2&H2a&H2b).
            right. left. exists v1 v2.
              split. auto. split. auto. rewrite H1b, H2b.
                apply (@Proposition_6_10_7P3 X Y v1 v2). auto.
          (* f1 is a propagator while f2 is pure *) (* (1.2) *)   
          apply dblnegelim in H0.
          destruct(@Corollary_6_10_4 X Y a1). auto. contradiction.
          destruct H1 as (v1&H1a&H1b).
          (* absurd case *)
            left. rewrite H1b. split. intro H2.
            specialize (@Assumption_6_10_5 X Y e a2 v1). intro H1. 
              apply H1. intro H3. apply H1.
              apply H1. intros. apply H1. intros. apply H1. intros.
            symmetry. exact H2. apply H5. apply H6.
            apply H3. apply H3.
            intros. symmetry. apply Assumption_6_10_5.
              intros. apply H1. apply H2. apply H3.
              split. apply Ha. split. apply no_untag_tag_ispure, H0.
                apply no_untag_tag_ispure, H1a.
        destruct(excludedmiddle (not (has_only_pure a2))).
          (* f2 is a propagator while f1 is pure *) (* (1.3) *)   
          apply dblnegelim in H.
          destruct(@Corollary_6_10_4 X Y a2). auto. contradiction.
          destruct H1 as (v2&H2a&H2b).
          (* absurd case *)
            left. rewrite H2b.
             specialize (@Assumption_6_10_5 X Y e a1 v2). intros H1. 
             split. intro H2. apply H1. intro H3. exact H2.
            intros. apply Assumption_6_10_5. intros. apply H2. apply H3. apply H4.
            split. exact Ha. split. apply no_untag_tag_ispure, H.
            apply no_untag_tag_ispure, H2a.
          (* f1 and f2 are pure terms *) (* (1.4) *) 
          apply dblnegelim in H. apply dblnegelim in H0.
            right. right. exists a1 a2.
              split. auto. split. auto. easy.
Qed.

(** An equation between propagators is either absurd or equivalent to an equation between pure terms. **)
(** domain is empty_set (Y = empty_set) **)
Lemma Corollary_6_8_10P1_2: forall {X} (a1 a2: term X empty_set), has_no_catcher a1 /\ has_no_catcher a2 -> (a1 == a2).
Proof. intros X a1 a2 H.
         apply wtos.
           apply no_untag_ispropagator, H.
           apply no_untag_ispropagator, H.
         setoid_rewrite w_empty; reflexivity.
Qed.

(** **)
(** An equation between catchers is equivalent to at most two equations between propagators. **)
Lemma Corollary_6_8_10P2: forall {X Y} (f1 f2: term Y X),
	((exists a1 : (term Y (Val e)), exists a2 : (term Y (Val e)), 
        exists b1 : (term Y X), exists b2 : (term Y X),
	(has_no_catcher a1 /\ has_no_catcher a2 /\ 
         has_no_catcher b1 /\ has_no_catcher b2 /\
	(f1 == f2 <-> ( a1 == a2 /\ (b1 == b2)))))
         \/        	
        (exists a1: (term Y X), exists a2 : (term Y X),  
	(has_no_catcher a1 /\ has_no_catcher a2 /\ 	
	((f1 == f2) <-> (a1 == a2)) ))).
Proof. intros X Y f1 f2.
         destruct(excludedmiddle (not (has_no_catcher f1))).
         destruct(excludedmiddle (not (has_no_catcher f2))).
         (* f1 and f2 are catchers *) (* (2.1) *)     
           specialize(@Proposition_6_10_3_P2 X Y f1). intros.
           destruct H1. contradiction.
           destruct H1 as (a1). 
           destruct H1 as (u1&H1a&H1b&H1c).
           specialize(@Proposition_6_10_3_P2 X Y f2). intros.
           destruct H1. contradiction.
           destruct H1 as (a2). 
           destruct H1 as (u2&H2a&H2b&H2c).
             left. exists a1 a2 (a1 o u1) (a2 o u2).
             split. auto. split. auto. split.
               unfold has_no_catcher. simpl. apply andb_true_iff. split. auto. apply H1b. split.
               unfold has_no_catcher. simpl. apply andb_true_iff. split. auto. apply H2b.
             rewrite H1c. rewrite H2c.
             apply(@Proposition_6_10_7P1 X Y a1 a2 u1 u2). auto.
           (* f1 is a catcher while f2 is a propagator *) (* (2.2) *) 
           apply dblnegelim in H0.
           specialize(@Proposition_6_10_3_P2 X Y f1). intros.
           destruct H1. contradiction.
           destruct H1 as (a1). 
           destruct H1 as (u1&H1a&H1b&H1c).           
             left. exists ((@empty Y) o (tag e)) a1 f2 (a1 o u1).
             split. unfold has_no_catcher. simpl. auto. split. auto. split. auto. split.
               unfold has_no_catcher. simpl. apply andb_true_iff. split. auto. apply H1b.               
             rewrite H1c.
             specialize(@Proposition_6_10_7P2 X Y f2 a1 u1). intro H1.
               split. intro H2. split.
               symmetry. apply H1. split. apply H1a. split; assumption. exact H2.
               apply H1. split. apply H1a. split; assumption. exact H2.
               intro H2. apply H1. split. apply H1a. split; assumption. split. apply H2. symmetry; apply H2.
          destruct(excludedmiddle (not (has_no_catcher f2))).
           (* f2 is a catcher while f1 is a propagator *) (* (2.3) *)  
           apply dblnegelim in H.
           specialize(@Proposition_6_10_3_P2 X Y f2). intros.
           destruct H1. contradiction.
           destruct H1 as (a2).
           destruct H1 as (u2&H2a&H2b&H2c).
             left. exists ((@empty Y) o (tag e)) a2 f1 (a2 o u2).
             split. unfold has_no_catcher. simpl. auto. split. auto. split. auto. split.
               unfold has_no_catcher. simpl. apply andb_true_iff. split. auto. apply H2b.
             rewrite H2c. specialize(@Proposition_6_10_7P2 X Y f1 a2 u2). intros.
               destruct H1. auto. split. intros. split. symmetry; apply H2. apply sym, H3.
               intros. apply H2, sym, H3.
           intro H3. apply sym, H2. split. apply H3. apply sym, H3.
           (* f1 and f2 are propagators *) (* (2.4) *)  
           apply dblnegelim in H0. apply dblnegelim in H.
             right. exists f1 f2.
             split. auto. split. auto. easy.
Qed.


(** **)
(** An equation between any two terms is either absurd or equivalent to two equations between pure terms.  **)
Theorem Theorem_6_10_9: forall {X Y} (f1 f2: term Y X), (Val e <> empty_set) -> 
         (((f1 == f2) <-> (forall {X Y} (f g: term Y X), EPURE f -> EPURE g -> f == g))
         \/
         (exists a1: (term Y X), exists a2: (term Y X),
          exists b1: (term (Val e) (Val e)), exists b2: (term (Val e) (Val e)),
	 (has_only_pure a1 /\ has_only_pure a2 /\
          has_only_pure b1 /\ has_only_pure b2 /\ 
	 (f1 == f2 <-> (a1 == a2 /\ b1 == b2))))
         \/
         (exists a1: (term (Val e) X), exists a2: (term (Val e) X),
          exists b1: (term (Val e) (Val e)), exists b2: (term (Val e) (Val e)),
	 (has_only_pure a1 /\ has_only_pure a2 /\
          has_only_pure b1 /\ has_only_pure b2 /\ 
	 (f1 == f2 <-> (a1 == a2 /\ b1 == b2))))
         \/
         (exists a1: (term (Val e) X), exists a2: (term (Val e) X),
          exists b1: (term Y (Val e)), exists b2: (term Y (Val e)),
	 (has_only_pure a1 /\ has_only_pure a2 /\
          has_only_pure b1 /\ has_only_pure b2 /\ 
	 (f1 == f2 <-> (a1 == a2 /\ b1 == b2))))
         \/
         (exists a1: (term Y X), exists a2: (term Y X),
          exists b1: (term Y (Val e)), exists b2: (term Y (Val e)),
	 (has_only_pure a1 /\ has_only_pure a2 /\
          has_only_pure b1 /\ has_only_pure b2 /\ 
	 (f1 == f2 <-> (a1 == a2 /\ b1 == b2))))
).
Proof. intros X Y f1 f2 Hb.
         destruct(excludedmiddle (X = empty_set)).
           revert f1 f2. rewrite H.
             intros f1 f2.
         specialize(@Corollary_6_8_10P2 empty_set Y f1 f2). intro H2.
           destruct H2 as [H0|H2]. destruct H0 as (a1&a2&b1&b2&H0).
           specialize (@Corollary_6_8_10P1_1 (Val e) Y a1 a2).
           specialize (@Corollary_6_8_10P1_2 Y b1 b2).
         intros H1 H2.
           destruct H2. split. apply Hb. split; apply H0.
         left. split; intro H5. 
             apply H2, H0, H5.
             apply H0. split. apply H2, H5. apply H1. split; apply H0.
           destruct H2. destruct H2  as (a3&a4&H2).
             right. right. left.
               exists (@empty (Val e)) (@empty (Val e)) a3 a4.
                 split. unfold has_only_pure. auto.
                 split. unfold has_only_pure. auto.
                 split. apply H2. split. apply H2.
                 split.
                   intro H3.
                     split. reflexivity.
                     apply H2, H0, H3.
                   intro H3. apply H0. split. apply H2, H3. apply H1. split; apply H0.
             right. right. right. left.
               destruct H2  as (a3&a4&H2).
               exists (@empty (Val e)) (@empty (Val e)) a3 a4.
                 split. unfold has_only_pure. auto.
                 split. unfold has_only_pure. auto.
                 split. apply H2. split. apply H2.
                 split.
                   intro H3.
                     split. reflexivity.
                     apply H2, H0, H3.
                   intro H3. apply H0. split. apply H2, H3. apply H1. split; apply H0.
           destruct H2 as (a1&a2&H0).
             specialize (@Corollary_6_8_10P1_2 Y a1 a2).
             intro H1. 
             right. left. exists (@empty Y) (@empty Y) (@id (Val e)) (@id (Val e)).
               split. unfold has_only_pure; auto.
               split. unfold has_only_pure; auto.
               split. unfold has_only_pure; auto.
               split. unfold has_only_pure; auto.
               split. intro H2. split.
                 reflexivity. reflexivity.
               intro H2. apply H0, H1. split; apply H0.
               (**)
         specialize(@Corollary_6_8_10P2 X Y f1 f2). intro H2.
           destruct H2 as [H0|H2]. destruct H0 as (a1&a2&b1&b2&H0).
           specialize (@Corollary_6_8_10P1_1 (Val e) Y a1 a2).
           specialize (@Corollary_6_8_10P1_1 X Y b1 b2).
         destruct H0 as (H1a&H1b).
         intros H1 H2.
           destruct H1. split. apply H. split. apply H1b. apply H1b.
           destruct H2. split. apply Hb.
             split. apply H1a. apply H1b.
         left. split; intro H5. intros.
             apply H1. apply H1b. apply H5. apply H2. apply H3.
             apply H1b. split. apply H1. intros. apply H5. apply H2. apply H3.
             apply H0. intros. apply H5. apply H2. apply H3.
             (* absurd case *)
         left. split; intro H5. 
             intros. apply H0. apply H1b. apply H5. apply H2. apply H3.
             destruct H1. destruct H1. destruct H1.
             apply H1b. split. apply H1. apply H5. apply no_untag_tag_ispure, H1.
             apply no_untag_tag_ispure, H1.
             apply H0. intros. apply H5. apply H2. apply H3.
             destruct H1. destruct H1. apply H1b.
             split. apply H1. apply H5. apply no_untag_tag_ispure, H1.
             apply no_untag_tag_ispure, H1.
             apply H0. intros. apply H5. apply H2. apply H3.
           destruct H2. split. apply Hb.
             split. apply H1a. apply H1b.
             (*absurd case*)
         left. split; intro H5. intros.
              apply H1. apply H1b, H5. apply H2. apply H3.
              apply H1b. split. apply H1. apply H5. 
              destruct H0. destruct H0. destruct H0.
              apply H0. apply H5. apply no_untag_tag_ispure, H0. apply no_untag_tag_ispure, H0.
              destruct H0. destruct H0. apply H0. apply H5. apply no_untag_tag_ispure, H0.
              apply no_untag_tag_ispure, H0.
           destruct H0; destruct H1; destruct H0  as (a3&a4&H0); destruct H1 as (b3&b4&H1).
             right. right. left.
               exists a3 a4 b3 b4.
                 split. apply H0. split. apply H0. split. apply H1. split. apply H1.
                 split.
                   intro H3.
                     split. apply H0, H1b, H3.
                     apply H1, H1b, H3.
                   intro H3. apply H1b. split. apply H1, H3. apply H0, H3.
             right. right. right. left.
               exists a3 a4 b3 b4.
                 split. apply H0. split. apply H0. split. apply H1. split. apply H1.
                 split.
                   intro H3.
                     split. apply H0, H1b, H3.
                     apply H1, H1b, H3.
                   intro H3. apply H1b. split. apply H1, H3. apply H0, H3.
             right. left. exists a3 a4 b3 b4.
               split. apply H0. split. apply H0.
                 split. apply H1.
                 split. apply H1.
               split; intro H3.
                 split. apply H0, H1b, H3. apply H1, H1b, H3.
               apply H1b. split. apply H1, H3. apply H0, H3.
             right. right. right. right.
               exists a3 a4 b3 b4.
                 split. apply H0. split. apply H0. split. apply H1. split. apply H1.
                 split.
                   intro H3.
                     split. apply H0, H1b, H3.
                     apply H1, H1b, H3.
                   intro H3. apply H1b. split. apply H1, H3. apply H0, H3.
           destruct H2 as (b1&b2&H0).
             specialize (@Corollary_6_8_10P1_1 X Y b1 b2).
             intro H1. destruct H1.
               split. apply H. split. apply H0. apply H0.
             left. split; intro H5. intros. 
             apply H1. apply H0. apply H5. apply H2. apply H3.
             (**) apply H0, H1, H5. (**)
           destruct H1. destruct H1 as (a1&a2&H1).
             right. right. left. exists a1 a2 (@id (Val e)) (@id (Val e)).
               split. apply H1. split. apply H1. split. unfold has_only_pure; auto. split. unfold has_only_pure; auto.
               split. intro H2. split.
                 apply H1, H0, H2.
                 reflexivity.
               intro H2. apply H0, H1, H2.
           destruct H1 as (a1&a2&H1).
             right. left. exists a1 a2 (@id (Val e)) (@id (Val e)).
               split. apply H1. split. apply H1. split. unfold has_only_pure; auto. split. unfold has_only_pure; auto.
               split. intro H2. split.
                 apply H1, H0, H2.
                 reflexivity.
               intro H2. apply H0, H1, H2.
Qed.


End Make.
