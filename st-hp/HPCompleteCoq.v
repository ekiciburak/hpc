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
Require Memory Terms Decorations Axioms Proofs.
Set Implicit Arguments.
Module Make(Import M: Memory.T).
Module Export HPCompleteCoqExp := Proofs.Make(M).

Axiom excludedmiddle: forall P, P \/ ~P.
Axiom dblnegelim    : forall P, ~~P -> P.


(** **)
(** Canonical form for accessors: an accessor term f: X -> Y is either or a term of the 
form: "v o (lookup i) o < >"   **)
Lemma Proposition_5_5_3P1: forall X Y (f: term Y X), has_no_update f -> 
    (has_only_pure f)
        \/
        (exists u : (term Y (Val i)), exists v : (term unit X),
        (has_only_pure u) /\ (has_no_update v) /\
        (f == u o lookup i o v)).
Proof.
    intros. induction f.
    (* kX *)
    left. unfold has_only_pure. auto.
    (* tpure *)
    left. unfold has_only_pure. auto.   
    (* comp: f == f1 o f2 *)
    destruct IHf1 as [IHf1a|IHf1b]. unfold has_no_update in H. simpl in H.
    rewrite ?andb_true_iff in H. apply H. destruct IHf2 as [IHf2a|IHf2b].
    simpl in H. rewrite ?andb_true_iff in H. unfold has_no_update in H. simpl in H.
    unfold has_no_update. rewrite ?andb_true_iff in H. apply H.
    (* f1 and f2 are both pure *) (* (1.1) *)
    left.
      unfold has_only_pure. split. simpl. rewrite ?andb_true_iff.
      unfold has_only_pure in IHf1a. unfold has_only_pure in IHf2a.
      split. apply IHf1a. apply IHf2a. auto.
    (* f1 is pure and f2 has no update *) (* (1.2) *)
    right.    
      destruct IHf2b as (u&v&H2).
      exists (f1 o u) v.
      split. unfold has_only_pure. unfold has_only_pure in H2.
      unfold has_only_pure in IHf1a. split. simpl. rewrite ?andb_true_iff. 
      split. apply IHf1a. apply H2. simpl. rewrite ?andb_true_iff.
      split. apply IHf1a. apply H2. split. apply H2. do 2 rewrite <- assoc.
      apply replsubs; [reflexivity| ]. rewrite assoc. apply H2.
    destruct IHf2 as [IHf2a|IHf2b].
    simpl in H. rewrite ?andb_true_iff in H. unfold has_no_update in H. simpl in H.
    unfold has_no_update. rewrite ?andb_true_iff in H. apply H.
    (* f1 has no update and f2 is pure *) (* (1.3) *)
    right.
      destruct IHf1b as (u&v&H1).
      exists u (v o f2).
      split. split. apply H1. apply H1. split. simpl. rewrite ?andb_true_iff.
      unfold has_no_update in H. simpl in H. unfold has_no_update.
      rewrite ?andb_true_iff in H. simpl. rewrite ?andb_true_iff. 
      split. apply H1. apply H. rewrite assoc.
      apply replsubs; [| reflexivity ].  apply H1.
    (* f1 and f2 have no update *) (* (1.4) *)
    right.
      destruct IHf1b as (u1&v1&(H1a&H1b&H1c)).
      destruct IHf2b as (u2&v2&(H2a&H2b&H2c)).
      exists u1 v2.
      split. assumption. split. assumption. rewrite H1c, H2c.
      cut (v1 o u2 == (@forget (Val i))).
        intro H3. do 2 setoid_rewrite <- assoc at 3.
        setoid_rewrite assoc at 1. setoid_rewrite <- assoc at 2. rewrite H3.
        do 2 setoid_rewrite <- assoc. do 2 setoid_rewrite assoc at 2.
        rewrite ILL. reflexivity.
      (* 1st cut *)
      setoid_rewrite s_unit; [reflexivity| decorate].     
    (* lookup *)
    right.
      destruct (Loc_eq i i0).
      exists (@id (Val i)) (@id unit).
      split. unfold has_only_pure. auto. split. auto.
      setoid_rewrite -> ids. setoid_rewrite -> idt at 1. apply refl.
    (* update *)
    contradict H. unfold not. unfold has_no_update.
    intros. simpl in H. congruence.
Qed.

(* an accessor is either pure or of the form (v o lookup i o < >) *)
Lemma Corollary_5_5_4: forall {X Y} (a: term Y X), has_no_update a ->
   (has_only_pure a
   \/
   (exists v : (term Y (Val i)), (has_only_pure v) /\ (a == (v o lookup i o (@forget X))))).
Proof.
    intros X Y a H.
      specialize (@Proposition_5_5_3P1 X Y a).
      intro H0. destruct H0.
        assumption.
        left. assumption.
        right. destruct H0 as (u&v&H2).
          exists u.
          destruct H2 as (H2a&H2b&H2c).
          split. assumption.
        rewrite H2c. rewrite s_unit; [reflexivity| decorate].
Qed.


(** **)
(** Canonical form for modifiers: an modifier term
f: X -> Y is either an accessor or a term of the form: "(v o lookup i o update i o a)". **)

Lemma Proposition_5_5_3P2: forall {X Y} (f: term Y X), 
    (has_no_update f 
      \/
      (exists a : (term (Val i) X), exists u : (term Y (Val i)),
        (has_no_update a) /\ (has_only_pure u) 
        /\ (f == (u o lookup i o update i o a)))
    ).
Proof.
    intros. induction f.
    (* kX *)
    left. unfold has_no_update. auto.
    (* tpure *)
    left. unfold has_no_update. auto.
    (* comp *)
    destruct IHf1 as [IHf1a|IHf1b].
    destruct IHf2 as [IHf2a|IHf2b].
    (* f1 and f2 have no update *) (* (2.1) *)
    left. simpl. unfold has_no_update. simpl. rewrite ?andb_true_iff. auto.
    (* f1 has no update, f2 has update *) (* (2.2) *)
    right. destruct IHf2b as (a2&u2&H2).
    specialize (@Proposition_5_5_3P1 Y X f1).
    intros. destruct H. assumption.
      (* f1 has only pure *)
      exists a2 (f1 o u2). split. apply H2.
      split. apply onlypurecomp. split. apply H2. assumption.
      do 3 rewrite <- assoc. apply replsubs; [reflexivity| ]. 
      do 2 rewrite -> assoc. apply H2.
      (* f1 has lookup *) 
      destruct H as (w1&v1&(H1a&H1b&H1c)).
      destruct H2 as (H2a&H2b&H2c).
      exists a2 w1.
      split. apply H2a. split. apply H1a.
      rewrite H1c, H2c.
      do 2 setoid_rewrite <- assoc at 3.
      setoid_rewrite assoc. setoid_rewrite <- assoc at 2.
      cut (v1 o u2 == (@forget (Val i))).
        intro H. rewrite H.
        rewrite assoc. do 2 setoid_rewrite <- assoc at 2.
        setoid_rewrite assoc at 3. rewrite ILL.
        rewrite assoc. reflexivity.
      (*1st cut*)
      setoid_rewrite s_unit;[reflexivity| decorate].
    right. destruct IHf1b as (a1&u1&H2).
    destruct IHf2 as [IHf2a|IHf2b].
    (* f2 has no update *) (* (2.3) *)
    exists (a1 o f2) u1. split. unfold has_no_update. 
    simpl. rewrite ?andb_true_iff. split. apply H2. apply IHf2a.
    split. apply H2. rewrite assoc. apply replsubs; [ |reflexivity]. apply H2.
    (* f1 and f2 has update *) (* (2.4) *) 
    destruct IHf2b as (a2&u2&H3). 
    specialize (@Proposition_5_5_3P1 Y (Val i) a1). intros.
    destruct H as [Ha|Hb]. apply H2.
      (* a is pure *) (* (2.4.1) *)
      exists (a1 o u2 o a2) u1.
      split. unfold has_no_update. simpl. rewrite ?andb_true_iff.
      repeat split. apply H2. apply H3. apply H3.
      split. apply H2.
      destruct H2 as (H2a&H2b&H2c).
      destruct H3 as (H3a&H3b&H3c).
      rewrite H2c, H3c.
      do 3 setoid_rewrite <- assoc. 
      do 2 (apply replsubs; [reflexivity| ]).
      apply Lemma_5_5_2P3. setoid_rewrite <- assoc at 2.
      rewrite ax1, ids. reflexivity.
      (* a has a lookup *) 
      destruct Hb as (w1&v1&Hb1&Hb2).
      exists (w1 o a2) u1.
      split. unfold has_no_update. simpl. rewrite ?andb_true_iff.
      split. apply Hb1. apply H3. split. apply H2.
      destruct H2 as (H2a&H2b&H2c).
      destruct H3 as (H3a&H3b&H3c).
      destruct Hb2 as (Hb2a&Hb2b).
      rewrite H2c, H3c, Hb2b.
      do 3 setoid_rewrite <- assoc at 5.
      setoid_rewrite assoc at 2. rewrite assoc.
      setoid_rewrite <- assoc at 2.
      cut (v1 o u2 == (@forget (Val i))).
        intro H. rewrite H.
        rewrite assoc. setoid_rewrite assoc at 2.
        setoid_rewrite <- assoc at 3. setoid_rewrite <- assoc at 2.
        rewrite ILL.
        do 3 rewrite <- assoc.
        apply replsubs; [reflexivity|].
        apply Lemma_5_5_2P3.
        setoid_rewrite assoc at 2.
        rewrite ax1, idt. reflexivity.
      (*1st cut*)
      rewrite s_unit; [reflexivity| decorate].
    (* lookup *)
    left. unfold has_no_update. simpl.
    rewrite ?andb_true_iff. auto. 
    (* update *)
    right. destruct (Loc_eq i i0).
    exists (@id (Val i)) (@forget (Val i)).
    split. auto. split. split. unfold has_only_pure. simpl.
    auto. rewrite ids. setoid_rewrite <- idt at 1.
    apply replsubs; [setoid_rewrite s_unit; [reflexivity| decorate| decorate]| reflexivity].
Qed.


(** **)
(** An equation between two strict modifiers is equivalent to two equations between accessors.  **)

Lemma Proposition_5_5_5P1: forall {X Y} (a1 a2: term (Val i) X) (u1 u2: term Y (Val i)),
	has_no_update a1 /\ has_no_update a2 /\ has_only_pure u1 /\ has_only_pure u2 ->
	((u1 o lookup i o update i o a1) ~ (u2 o lookup i o update i o a2) <->  (u1 o a1 == u2 o a2))
            /\
 	((u1 o lookup i o update i o a1) == (u2 o lookup i o update i o a2) <->  (a1 == a2) /\  (u1 o a1 == u2 o a2)).
Proof.
   intros X Y a1 a2 u1 u2 H. split. destruct H as (Ha&Hb&Hc&Hd).
     split. intro H.
     (* f1 ~ f2 -> u1 o a1 == u2 o a2 *) (* (1.1) *)
     setoid_rewrite <- assoc at 2 in H. setoid_rewrite <- assoc at 3 in H.
     setoid_rewrite ax1 in H. setoid_rewrite ids in H.
     apply wtos; [decorate| decorate| exact H].
     (* u1 o a1 == u2 o a2 -> f1 ~ f2 *) (* (1.2) *)
     intro H. apply stow in H.
     setoid_rewrite <- ids at 2 in H. setoid_rewrite <- ids at 7 in H.
     setoid_rewrite <- ax1 in H. 
     setoid_rewrite assoc in H. exact H.
   split. intro H1.
     (* f1 == f2 ->  a1 == a2  /\ u1 o a1 == u2 o a2 *) (* (1.3) *)
     split.
       (* f1 == f2 ->  a1 == a2 *) (* (1.3.1) *)
       destruct H as (Ha&Hb&Hc&Hd).
       cut (forget o ((u1 o lookup i) o update i) o a1 == forget o ((u2 o lookup i) o update i) o a2).
         intro H2. setoid_rewrite assoc in H2.
         cut((forget o (u1 o lookup i)) == (@id unit)).
           intro H3. rewrite H3 in H2.
           cut((forget o (u2 o lookup i)) == (@id unit)).
             intro H4. rewrite H4 in H2.
             setoid_rewrite idt in H2.
             apply Lemma_5_5_2P3 in H2.
             apply wtos; [decorate| decorate| exact H2].
           (*1st cut*)
           setoid_rewrite s_unit; [reflexivity| decorate| decorate].
         (*2nd cut*)
         setoid_rewrite s_unit; [reflexivity| decorate| decorate].
       (*3rd cut*)
       setoid_rewrite <- assoc. rewrite H1. reflexivity.
     (* f1 == f2 ->  u1 o a1 == u2 o a2 *) (* (1.3.2) *)
     destruct H as (Ha&Hb&Hc&Hd).    
     apply stow in H1.
     setoid_rewrite <- assoc at 2 in H1. setoid_rewrite <- assoc at 3 in H1.           
     setoid_rewrite ax1 in H1. setoid_rewrite ids in H1.
     apply wtos; [decorate| decorate| exact H1].   
   intro H1.
     (* a1 == a2 /\ u1 o a1 == u2 o a2 -> f1 == f2 *) (* (1.4) *)
     destruct H as (Ha&Hb&Hc&Hd).   
     apply effect.
     (* a1 == a2 /\ u1 o a1 == u2 o a2 ->  < > o f1 == < > o f2 *) (* (1.4.1) *)
     do 2 setoid_rewrite assoc.
       cut ((forget o (u1 o lookup i)) == (@id unit)).
         intro H2. rewrite H2, idt.
         cut ((forget o (u2 o lookup i)) == (@id unit)).
           intro H3. rewrite H3, idt. (* update i o a1 == update i o a2 *)
           destruct H1 as (H1a&H1b). rewrite H1a; reflexivity.
         (*2nd cut*)
        setoid_rewrite s_unit; [reflexivity| decorate| decorate].
      (*1st cut*)
      setoid_rewrite s_unit; [reflexivity| decorate| decorate].
      (* a1 == a2 /\ u1 o a1 == u2 o a2 -> f1 ~ f2 *) (* (1.4.2) *)
      setoid_rewrite <- assoc at 2. setoid_rewrite <- assoc at 3.
      setoid_rewrite ax1. setoid_rewrite ids.
     apply stow. apply H1.
Qed.   

(** **)
(** An equation between a strict modifier and an accessor is equivalent to at most two equations between accessors. **)
Lemma Proposition_5_5_5P2: forall {X Y} (a2 : term Y X) (a1: term (Val i) X) (u1: term Y (Val i)),
	has_no_update a2 /\ has_no_update a1 /\ has_only_pure u1 ->
	((u1 o lookup i o update i o a1) ~ a2 <->  (a2 == u1 o a1))
                                        /\
        ((u1 o lookup i o update i o a1) == a2 <-> ((lookup i o (@forget X) == a1) /\ (a2 == u1 o a1))).
Proof.
    intros X Y a2 a1 u1 H. destruct H as (Ha&Hb&Hc).
      split. split.
        (* f1 == a2 -> a2 ~ u1 o a1 *) (* (2.1) *)
        intro H1.
          setoid_rewrite <- assoc at 2 in H1.
          rewrite ax1, ids in H1.
          apply wtos in H1; [symmetry; exact H1| decorate| decorate].
        (* a2 == u1 o a1 -> f1 ~ a2 *) (* (2.2) *)
        intro H1.
          setoid_rewrite <- assoc at 2. 
          rewrite ax1, ids.
          apply stow; symmetry; exact H1.
      split.
    (* f1 == a2 -> (lookup i o forget == a1) /\ a2 == u1 o a1 *) (* (2.3) *)
    intro H1.
      split.
      (* f1 == a2 -> (lookup i o forget == a1) *) (* (2.3.1) *)
      apply wtos; [decorate| decorate| ].
      cut ((forget o (u1 o lookup i) o update i) o a1 == forget o a2).
        intro H2.
        cut(forget o (u1 o lookup i) == (@id unit)).
          intro H3; rewrite H3, idt in H2.
          setoid_rewrite s_unit at 3 in H2; [| decorate].          
          rewrite <- H2. rewrite assoc.
          rewrite ax1, idt. reflexivity.
        (*1st cut*)
        setoid_rewrite s_unit; [reflexivity| decorate| decorate].
      (*2nd cut*)
      rewrite <- H1. repeat rewrite assoc. reflexivity.
      (* f1 == a2 -> a2 == u1 o a1 *)
      setoid_rewrite <- assoc at 2 in H1.
      apply stow in H1.
      rewrite ax1, ids in H1.
      apply wtos in H1; [symmetry; exact H1| decorate| decorate].
    (* (lookup i o forget == a1) /\ a2 == u1 o a1 -> f1 == a2 *) (* (2.4) *)
    intro H1. destruct H1 as (H1a&H1b).
    rewrite <- H1a. setoid_rewrite <- assoc.
    setoid_rewrite assoc at 2. 
    rewrite ALU, idt.
    rewrite H1b. rewrite <- H1a.
    rewrite assoc. reflexivity.
Qed.

(** **)
(** An equality between two strict accessors is equivalent to an equality between pure terms. **)
Lemma Proposition_5_5_5P3: forall {X Y} (v1 v2 : term Y (Val i)),
	(has_only_pure v1 /\ has_only_pure v2) -> 
              ((v1 o lookup i o (@forget X)) ==  (v2 o lookup i o (@forget X)) <-> v1 == v2).
Proof.
   intros X Y v1 v2 H. destruct H as (Ha&Hb).
     split.
     (* a1 == a2 -> v1 == v2 *)
     intro H.
       apply epi in H; [| split; decorate].
       apply Lemma_5_5_2P1_3 in H; [apply H| decorate| decorate].
     (* v1 == v2 -> a1 == a2 *)
     intro H. 
       do 2 (apply replsubs; [ |reflexivity]).
       exact H.
Qed.


(** **)
(** An equation between a strict accessor and a pure term is equivalent to two equations between pure terms. **)

Lemma Proposition_5_5_5P4: forall {X Y} (v2 : term Y X) (v1: term Y (Val i)) (p: X <> empty_set), has_only_pure v2  /\ has_only_pure v1 ->
	 (((v1 o lookup i o (@forget X)) == v2) <-> (v1 == v2 o (@kX X p) o (@forget (Val i))) /\ (v2 == v2 o (@kX X p) o (@forget X))).
Proof.
  intros X Y v2 v1 p H. destruct H as (H1a&H1b). 
    split. intro H4.
    (* a1 == v2 -> (v1 == (v2 o kX p) o forget) /\ v2 == (v2 o kX p) o forget *) (* (4.1) *)
    split.
    (* a1 == v2 -> (v1 == (v2 o kX p) o forget) *) (* (4.1.1) *)
    cut((v1 o lookup i) o forget o ((kX p) o (@forget (Val i))) == v2 o ((kX p) o (@forget (Val i)))).
      intro H5. setoid_rewrite assoc at 1 in H5. setoid_rewrite <- assoc at 2 in H5. 
      cut (forget o (kX p) == id).
        intro H6. rewrite H6, ids in H5.
        rewrite assoc in H5. apply epi in H5; [| split; decorate]. 
        apply Lemma_5_5_2P2 in H5; [apply H5| decorate| decorate]. 
      (*2nd cut*)
      setoid_rewrite s_unit; [reflexivity| decorate| decorate].
    (*1st cut*)
    rewrite H4. reflexivity.
  (* a1 == v2 -> v2 == (v2 o kX p) o forget *) (* (4.1.2) *)
  rewrite <- assoc.
  rewrite <- H4. setoid_rewrite <- assoc at 2.
  setoid_rewrite s_unit at 2; [reflexivity| decorate].
  (* conversely: (v1 == (v2 o kX p) o forget) /\ v2 == (v2 o kX p) o forget -> a1 == v2*) (* (4.2) *)
  intro H. destruct H as (Ha&Hb).
  rewrite Ha. do 2 rewrite <- assoc.
  setoid_rewrite s_unit; [symmetry; exact Hb | decorate].
Qed.


(** **)
(** An equation between accessors is equivalent to at most two equations between pure terms. **)

Lemma Corollary_5_5_8P1: forall {X Y} (f1 f2: term Y X) (p: X <> empty_set),
	((exists a1 : (term (Val i) X), exists a2 : (term (Val i) X), 
        exists b1 : (term Y X), exists b2 : (term Y X),
	(has_no_update a1 /\ has_no_update a2 /\ 
         has_no_update b1 /\ has_no_update b2 /\
	(f1 == f2 <-> ( a1 == a2 /\ (b1 == b2)))))
         \/        	
        (exists a1: (term Y X), exists a2 : (term Y X),  
	(has_no_update a1 /\ has_no_update a2 /\ 	
	((f1 == f2) <-> (a1 == a2)) ))).
Proof. intros X Y f1 f2 H.
         destruct(excludedmiddle (not (has_no_update f1))).
         destruct(excludedmiddle (not (has_no_update f2))).
           (* f1 and f2 are modifiers *) (* 2.1 *)
           destruct(@Proposition_5_5_3P2 X Y f1) as [a1| H2].
             contradiction. 
             destruct H2 as (a1&u1&H2a&H2b&H2c).
           destruct(@Proposition_5_5_3P2 X Y f2) as [a2| H3].
             contradiction.
             destruct H3 as (a2&u2&H3a&H3b&H3c).
               left. exists a1 a2 (u1 o a1) (u2 o a2).
                 split. auto. split. auto. split. unfold has_no_update. 
                   simpl. rewrite andb_true_iff.
                   split. apply H2b. apply H2a. split. unfold has_no_update. 
                   simpl. rewrite andb_true_iff.
                   split. apply H3b. apply H3a. rewrite H2c, H3c. 
                   split. intro H2.
                   apply (@Proposition_5_5_5P1 X Y a1 a2 u1 u2).
                     auto. exact H2.
                   intros (H4a&H4b).
                     apply effect.
                       rewrite H4a. repeat rewrite assoc.
                       do 3 (apply replsubs; [| reflexivity]).
                       setoid_rewrite s_unit; [reflexivity| decorate| decorate].
                     setoid_rewrite <- assoc at 2. setoid_rewrite <- assoc at 3. 
                     setoid_rewrite ax1. setoid_rewrite ids.
                     apply stow, H4b.  
           (* f1 is a modifier whilst f2 is an accessor *) (* 2.2 *)                  
           apply dblnegelim in H1.
           destruct(@Proposition_5_5_3P2 X Y f1) as [a1| H2].
             contradiction.
             destruct H2 as (a1&u1&H2a&H2b&H2c).
               left. exists (lookup i o (@forget X)) a1 f2 (u1 o a1).
                 split. unfold has_no_update. simpl. auto. split. auto. split. auto.
                 split. unfold has_no_update. simpl. rewrite andb_true_iff. 
                   split. apply H2b. apply H2a.
                 rewrite H2c. apply(@Proposition_5_5_5P2 X Y f2 a1 u1). auto.
           apply dblnegelim in H0. 
         destruct(excludedmiddle (not (has_no_update f2))).
           (* f2 is a modifier whilst f1 is an accessor *) (* 2.3 *)   
           destruct(@Proposition_5_5_3P2 X Y f2) as [a2 | H2].
             contradiction.
             destruct H2 as (a2&u2&H2a&H2b&H2c).
               left. exists (lookup i o (@forget X)) a2 f1 (u2 o a2).
                 split. unfold has_no_update. simpl. auto. split. auto. split. auto.
                 split. unfold has_no_update. simpl. rewrite andb_true_iff. 
                   split. apply H2b. apply H2a.
                 rewrite H2c. specialize(@Proposition_5_5_5P2 X Y f1 a2 u2). intros.
                   destruct H2. auto. split. intros. apply H3, sym, H4.
                     intros. apply sym, H3, H4.
           (* f1 an f2 are accessors *) (* 2.4 *)   
           apply dblnegelim in H1.
             right. exists f1 f2. split. auto. split. auto. easy.
Qed.

(** **)
(** An equation between modifiers is equivalent to at most two equations between accessors. **)
Lemma Corollary_5_5_8P2: forall {X Y} (f1 f2: term Y X) (p: X <> empty_set),
         has_no_update f1 /\ has_no_update f2 -> 
	(exists a1 : (term Y (Val i)), exists a2 : (term Y (Val i)), 
        exists b1 : (term Y X), exists b2 : (term Y X),
	(has_only_pure a1 /\ has_only_pure a2 /\ 
         has_only_pure b1 /\ has_only_pure b2 /\
	(f1 == f2 <-> ( a1 == a2 /\ (b1 == b2)))))
         \/
 	(exists a1: (term Y (Val i)), exists a2 : (term Y (Val i)),
	(has_only_pure a1 /\ has_only_pure a2 /\ 
        (f1 == f2 <-> a1 == a2)))
         \/        	
 	(exists a1: (term Y X), exists a2 : (term Y X),
	(has_only_pure a1 /\ has_only_pure a2 /\ 
        (f1 == f2 <-> a1 == a2))).
Proof. intros X Y f1 f2 p (Ha&Hb). 
        destruct(excludedmiddle (not (has_only_pure f1))).
        destruct(excludedmiddle (not (has_only_pure f2))).
          destruct(@Corollary_5_5_4 X Y f1). auto. contradiction.
          destruct(@Corollary_5_5_4 X Y f2). auto. contradiction.
            (* f1 and f2 are accessors *) (* 1.1 *)
            destruct H1 as (v1&H2a&H2b).
            destruct H2 as (v2&H3a&H3b).
              right. left. exists v1 v2. split. auto. split. auto.
                rewrite H2b, H3b.
                apply Proposition_5_5_5P3. auto.
          apply dblnegelim in H0.
            (* f1 is an accessor whilst f2 is pure *) (* 1.2 *)
            destruct(@Corollary_5_5_4 X Y f1). auto. contradiction.
            destruct H1 as (v1&H1a&H1b).
              left. exists v1 (f2 o (@kX X p) o (@forget (Val i))) f2 (f2 o (@kX X p) o (@forget X)).
                split. auto. split. unfold has_only_pure. 
                  simpl. repeat rewrite andb_true_iff.
                repeat split. apply H0. apply H0. split. auto. 
                  split. unfold has_only_pure. simpl.
                repeat rewrite andb_true_iff. repeat split. apply H0. apply H0.
                rewrite H1b.
                apply (@Proposition_5_5_5P4 X Y f2 v1 p). auto.
          destruct(excludedmiddle (not (has_only_pure f2))).
            (* f1 is pure whilst f2 is an accessor *) (* 1.3 *)
            destruct(@Corollary_5_5_4 X Y f2). auto. contradiction.
            apply dblnegelim in H.
            destruct H1 as (v2&H1a&H1b).
            left. exists v2 (f1 o (@kX X p) o (@forget (Val i))) f1 (f1 o (@kX X p) o (@forget X)).
              split. auto. split. unfold has_only_pure.
                simpl. repeat rewrite andb_true_iff.
              repeat split. apply H. apply H. split. auto. 
                split. unfold has_only_pure. simpl.
              repeat rewrite andb_true_iff. repeat split. apply H. apply H.
                rewrite H1b.
                specialize (@Proposition_5_5_5P4 X Y f1 v2 p). intros.
                  destruct H1. auto. split. intros. apply H1.
                    apply sym, H3. intros. apply sym, H2, H3.
            (* f1 and f2 are pure *) (* 1.4 *)
            apply dblnegelim in H. apply dblnegelim in H0.
              right. right. exists f1 f2. split. auto. split. auto. easy.
Qed.


(** **)
(** An equation between any two terms is equivalent to at most two equations between pure terms.  **)
Theorem Theorem_5_5_9: forall {X Y} (f1 f2: term Y X) (p1: X <> empty_set) (p2: (Val i) <> empty_set), 
       (exists a1 : (term (Val i) X), exists a2 : (term (Val i) X), 
        exists b1 : (term (Val i) (Val i)), exists b2 : (term (Val i) (Val i)),
        exists c1 : (term Y (Val i)), exists c2 : (term Y (Val i)),
        exists d1 : (term Y X), exists d2 : (term Y X),
	(has_only_pure a1 /\ has_only_pure a2 /\ 
         has_only_pure b1 /\ has_only_pure b2 /\
         has_only_pure c1 /\ has_only_pure c2 /\
         has_only_pure d2 /\ has_only_pure d2 /\
	(f1 == f2 <-> ( a1 == a2 /\ b1 == b2 /\ c1 == c2 /\ d1 == d2 )))).
Proof.
  intros X Y f1 f2 p1 p2.
    specialize(@Corollary_5_5_8P1 X Y f1 f2). intro H2.
    destruct H2. assumption.
    destruct H as (a1&a2&b1&b2&H2).
    specialize (@Corollary_5_5_8P2 X (Val i) a1 a2).
    specialize (@Corollary_5_5_8P2 X Y b1 b2).
    (* f1 and f2 are modifiers *)
    (* a1 and a2 are accessors *)
    (* b1 and b2 are accessors *)
    intros H3 H4. destruct H3. apply p1.
      split. apply H2. apply H2.
      destruct H as (a3&a4&b3&b4&H). 
      destruct H4. apply p1. split. apply H2. apply H2.
      destruct H0 as (a5&a6&b5&b6&H0). 
      exists b5 b6 a5 a6. 
      exists a3 a4 b3 b4.
        split. apply H0. split. apply H0. split. apply H0. split. apply H0.
        split. apply H. split. apply H. split. apply H. split. apply H.
        split. intro H3. 
        split. apply H0, H2, H3. split. apply H0, H2, H3.
        split. apply H, H2, H3. apply H, H2, H3.
        intro H3. apply H2. split. apply H0. split; apply H3. apply H, H3.
      destruct H0. destruct H0 as (a5&a6&H0). 
      exists ( (@kX (Val i) p2) o (@forget X)) ((@kX (Val i) p2) o (@forget X)) a5 a6.
      exists a3 a4 b3 b4.
        split. unfold has_only_pure. split; simpl. auto. auto.
        split. unfold has_only_pure. split; simpl. auto. auto.
        split. apply H0. split. apply H0. split. apply H.
        split. apply H. split. apply H. split. apply H.
        split. intro H3. split. reflexivity.
        split. apply H0, H2, H3. split. apply H, H2, H3.
        apply H, H2, H3.
        intro H3. apply H2. split. apply H0, H3. apply H. split; apply H3.
      destruct H0 as (a5&a6&H0).
      exists a5 a6 (@id (Val i)) (@id (Val i)).
      exists a3 a4 b3 b4. 
        split. apply H0. split. apply H0. split. unfold has_only_pure; auto.
        split. unfold has_only_pure; auto. split. apply H. split. apply H.
        split. apply H. split. apply H.
        split. intro H3. split. apply H0, H2, H3.
          split. reflexivity. split. apply H, H2, H3. apply H, H2, H3.
          intro H3. apply H2. split. apply H0, H3. apply H. split; apply H3.                   
      destruct H. destruct H as (a3&a4&H).
      destruct H4. apply p1. split. apply H2. apply H2.
      destruct H0 as (a5&a6&b3&b4&H0).
      exists b3 b4 a5 a6.
      exists a3 a4 (a4 o (@kX (Val i) p2) o (@forget X)) (a4 o (@kX (Val i) p2) o (@forget X)).
        split. apply H0. split. apply H0. split. apply H0.
        split. apply H0. split. apply H. split. apply H.
        split. unfold has_only_pure. split; simpl.
          rewrite andb_true_iff. split. rewrite andb_true_iff.
          split. apply H. auto. auto. rewrite andb_true_iff. 
          split. rewrite andb_true_iff. split. apply H. auto. auto.
          split. unfold has_only_pure. split; simpl.
          rewrite andb_true_iff. split. rewrite andb_true_iff. split. apply H. auto. auto.
          rewrite andb_true_iff. split. rewrite andb_true_iff. split. apply H. auto. auto.
          split. intro H3. split. apply H0, H2, H3. split. apply H0, H2, H3.
          split. apply H, H2, H3. reflexivity.
          intro H3. apply H2. split. apply H0. split; apply H3. apply H, H3.
      destruct H0. destruct H0 as (a5&a6&H0). 
      exists ((@kX (Val i) p2) o (@forget X)) ((@kX (Val i) p2) o (@forget X)) a5 a6.
      exists a3 a4 (a4 o (@kX (Val i) p2) o (@forget X)) (a4 o (@kX (Val i) p2) o (@forget X)).
        split. unfold has_only_pure; simpl. split. auto. auto.
        split. unfold has_only_pure; simpl. split. auto. auto.                     
        split. apply H0. split. apply H0. split. apply H. split. apply H.
        split. unfold has_only_pure; simpl. split.
          do 2 rewrite andb_true_iff. do 2 split.
          apply H. auto. do 2 rewrite andb_true_iff. do 2 split. apply H. auto.
          split. unfold has_only_pure; simpl. split.
          do 2 rewrite andb_true_iff. do 2 split.
          apply H. auto. do 2 rewrite andb_true_iff. do 2 split. apply H. auto.
          split. intro H3. split. reflexivity.
          split. apply H0, H2, H3. split. apply H, H2, H3. reflexivity.
            intro H3. apply H2. split. apply H0, H3. apply H, H3.
     destruct H0 as (a5&a6&H0).
     exists a5 a6 (@id (Val i)) (@id (Val i)). 
     exists a3 a4 (a4 o (@kX (Val i) p2) o (@forget X)) (a4 o (@kX (Val i) p2) o (@forget X)).
       split. apply H0. split. apply H0. split. unfold has_only_pure; auto.
       split. unfold has_only_pure; auto. split. apply H. split. apply H.
       split. unfold has_only_pure; simpl. split.
       do 2 rewrite andb_true_iff. do 2 split.
       apply H. auto. do 2 rewrite andb_true_iff. do 2 split. apply H. auto.
       split. unfold has_only_pure; simpl. split.
       do 2 rewrite andb_true_iff. do 2 split.
       apply H. auto. do 2 rewrite andb_true_iff. do 2 split. apply H. auto.
       split. intro H3. split. apply H0, H2, H3. split. reflexivity.
       split. apply H, H2, H3. reflexivity. intro H3. apply H2. split. apply H0, H3. apply H, H3.
     destruct H as (a3&a4&H).
     destruct H4. apply p1. split. apply H2. apply H2.
     destruct H0 as (a5&a6&b3&b4&H0).
     exists b3 b4 a5 a6. 
     exists (a3 o (@kX X p1) o (@forget (Val i))) (a3 o (@kX X p1) o (@forget (Val i))) a3 a4. 
       split. apply H0. split. apply H0. split. apply H0. split. apply H0.
       split. unfold has_only_pure; simpl. split.  do 2 rewrite andb_true_iff. do 2 split.
       apply H. auto. do 2 rewrite andb_true_iff. do 2 split. apply H. auto.
       split. unfold has_only_pure; simpl. split.
       do 2 rewrite andb_true_iff. do 2 split.
       apply H. auto. do 2 rewrite andb_true_iff. do 2 split. apply H. auto.
       split. apply H. split. apply H. split.
       intro H3. split. apply H0, H2, H3. split. apply H0, H2, H3. split. reflexivity.
       apply H, H2, H3. intro H3. apply H2. split. apply H0. split; apply H3. apply H, H3.
     destruct H0. destruct H0 as (a5&a6&H0).
     exists ((@kX (Val i) p2) o (@forget X)) ((@kX (Val i) p2) o (@forget X)) a5 a6.
     exists (a3 o (@kX X p1) o (@forget (Val i))) (a3 o (@kX X p1) o (@forget (Val i))) a3 a4.
       split. unfold has_only_pure; simpl. split. auto. auto.
       split. unfold has_only_pure; simpl. split. auto. auto.
       split. apply H0. split. apply H0.
       split. unfold has_only_pure; simpl. split.
       do 2 rewrite andb_true_iff. do 2 split.
       apply H. auto. do 2 rewrite andb_true_iff. do 2 split. apply H. auto.
       split. unfold has_only_pure; simpl. split.
       do 2 rewrite andb_true_iff. do 2 split.
       apply H. auto. do 2 rewrite andb_true_iff. do 2 split. apply H. auto.
       split. apply H. split. apply H. split.
       intro H3. split. reflexivity. split. apply H0, H2, H3. split. reflexivity.
       apply H, H2, H3. intro H3. apply H2. split. apply H0, H3. apply H, H3.
     destruct H0 as (a5&a6&H0). 
     exists a5 a6 (@id (Val i)) (@id (Val i)).
     exists (a3 o (@kX X p1) o (@forget (Val i))) (a3 o (@kX X p1) o (@forget (Val i))) a3 a4. 
       split. apply H0. split. apply H0. split. unfold has_only_pure; auto.
       split. unfold has_only_pure; auto. split. unfold has_only_pure; simpl. split.
       do 2 rewrite andb_true_iff. do 2 split.
       apply H. auto. do 2 rewrite andb_true_iff. do 2 split. apply H. auto.
       split. unfold has_only_pure; simpl. split.
       do 2 rewrite andb_true_iff. do 2 split.
       apply H. auto. do 2 rewrite andb_true_iff. do 2 split. apply H. auto.
       split. apply H. split. apply H.
       split. intro H3. split. apply H0, H2, H3.
       split. reflexivity. split. reflexivity. apply H, H2, H3.
       intro H3. apply H2. split. apply H0, H3. apply H, H3.
       destruct H as (a1&a2&H).
       specialize (@Corollary_5_5_8P2 X Y a1 a2).
       intro H2. destruct H2. apply p1. split. apply H. apply H.
     destruct H0 as (a3&a4&b1&b2&H0). 
     exists  ((@kX (Val i) p2) o (@forget X)) ((@kX (Val i) p2) o (@forget X)) (@id (Val i)) (@id (Val i)).
     exists a3 a4 b1 b2.
       split. unfold has_only_pure; simpl. split. auto. auto.
       split. unfold has_only_pure; simpl. split. auto. auto.
       split. unfold has_only_pure; auto. split. unfold has_only_pure; auto.
       split. apply H0. split. apply H0. split. apply H0. split. apply H0.
       split. intro H3. split. reflexivity.
       split. reflexivity. split. apply H0, H, H3. apply H0, H, H3.
       intro H3. apply H, H0. split; apply H3.
     destruct H0. destruct H0 as (a3&a4&H0).
     exists  ((@kX (Val i) p2) o (@forget X)) ((@kX (Val i) p2) o (@forget X)) (@id (Val i)) (@id (Val i)).
     exists a3 a4  (a3 o (@kX (Val i) p2) o (@forget X)) (a3 o (@kX (Val i) p2) o (@forget X)). 
       split. unfold has_only_pure; simpl. split. auto. auto.
       split. unfold has_only_pure; simpl. split. auto. auto.
       split. unfold has_only_pure; auto.  split. unfold has_only_pure; auto.
       split. apply H0. split. apply H0.
       split. unfold has_only_pure; simpl. split.
       do 2 rewrite andb_true_iff. do 2 split.
       apply H0. auto. do 2 rewrite andb_true_iff. do 2 split. apply H0. auto.
       split. unfold has_only_pure; simpl. split.
       do 2 rewrite andb_true_iff. do 2 split.
       apply H0. auto. do 2 rewrite andb_true_iff. do 2 split. apply H0. auto.
       split. intro H3. split. reflexivity.
       split. reflexivity. split. apply H0, H, H3. reflexivity.
       intro H3. apply H, H0. apply H3.
     destruct H0 as (a3&a4&H0). 
     exists  ((@kX (Val i) p2) o (@forget X)) ((@kX (Val i) p2) o (@forget X)) (@id (Val i)) (@id (Val i)).
     exists (a3 o (@kX  X p1) o (@forget (Val i))) (a3 o (@kX X p1) o (@forget (Val i))) a3 a4.                   
       split. unfold has_only_pure; simpl. split. auto. auto.
       split. unfold has_only_pure; simpl. split. auto. auto.
       split. unfold has_only_pure; auto. split. unfold has_only_pure; auto.
       split. unfold has_only_pure; simpl. split.
       do 2 rewrite andb_true_iff. do 2 split.
       apply H0. auto. do 2 rewrite andb_true_iff. do 2 split. apply H0. auto.
       split. unfold has_only_pure; simpl. split.
       do 2 rewrite andb_true_iff. do 2 split.
       apply H0. auto. do 2 rewrite andb_true_iff. do 2 split.
       apply H0. auto. split. apply H0. split. apply H0.
       split. intro H3. split. reflexivity. split. reflexivity. split. reflexivity.
       apply H0, H, H3. intro H3. apply H, H0. apply H3.
Qed.

End Make.






