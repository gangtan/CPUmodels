(* Copyright (c) 2011. Greg Morrisett, Gang Tan, Joseph Tassarotti, 
   Jean-Baptiste Tristan, and Edward Gan.

   This file is part of RockSalt.

   This file is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of
   the License, or (at your option) any later version.
*)

(** * DFA Construction *)
Require Import Coq.Program.Equality.
Require Import Coq.Init.Logic.
Require Import List.
Require Import Arith.
Require Import Bool.
Require Import Eqdep.
Require Import Parser.
Import X86_PARSER_ARG.
Set Implicit Arguments.
Unset Automatic Introduction.

(** In this section, we build a table-driven DFA recognizer for a [grammar].  
    This is very similar to the table-driven parser we build in Parser.v 
    except we don't need any semantic actions.  In essence, we just translate
    the grammar to an [astgram] (and throw away the semantic action function),
    then build a DFA structure very similar to, but much simpler than, the 
    DFA structure constructed in Parser.v.  In particular, what we build is:
        - A list of states which are really derivatives of the original astgram.
          The position of the astgram determines an identity (i.e., index) for the 
          state.  The initial astgram is always at position 0.  
        - A transition table as a list of list of nats.  If [T(i,j) = k], then 
          this says that in state [i], if we see an input list of characters 
          corresponding to the [token_id] [j], then we can transition to state [k].
          Obviously, [i] and [k] should be indexes of astgrams in the
          list of [states].  Furthermore, it should be that [states(k)] is the
          derivative of [states(i)] with respect to the token_id [j].
        - An accept table as a list of booleans.  [dfa_accepts(i) = true] iff 
          [states(i)] accepts the empty string.
        - A reject table as a list of booleans.  [dfa_rejects(i) = true] iff
          [states(i)] rejects all strings.

    It may be worth rewriting this to use the table construction (and proofs) 
    we already have in Parser.v.  For instance, we could take the Parser DFA
    structure and erase the stuff we don't need.  But it was simpler for now
    to just take the old code and adapt it to the new environment.  
*)
    

    Record DFA := { 
      dfa_num_states : nat ; 
      dfa_states : list astgram ; 
      dfa_transition : list (list nat) ; 
      dfa_accepts : list bool ;
      dfa_rejects : list bool
    }.

    (** Our DFA states correspond to nth derivatives of a starting regexp.  We take
        the position of a regexp in the [states] list to be its name. *)
    Definition states := list astgram.

    (* Poorly named, but basically calculates the derivative of an [astgram] and
       throws away the adjustment function. *)
    Definition unit_derivs r s := let (r', _) := derivs_and_split r s in r'.
    
    (** Generate the transition matrix row for the state corresponding to the
        regexp [r].  In general, this will add new states. *)
    Fixpoint gen_row' n (r:astgram) (s:states) token_id : (states * list nat) := 
      match n with 
        | 0 => (s, nil)
        | S n' => 
          let (s1, d) := find_or_add (unit_derivs r (token_id_to_chars token_id)) s in
          let (s2, row) := gen_row' n' r (s ++ s1) (1 + token_id) in
            (s2, d::row)
      end.
    Definition gen_row (r:astgram) (s:states) : (states * list nat) := 
      gen_row' num_tokens r s 0.

    (** Build a transition table by closing off the reachable states.  The invariant
        is that we've closed the table up to the [next_state] and have generated the
        appropriate transition rows for the states in the range 0..next_state-1.
        So we first check to see if [next_state] is outside the range of states, and
        if so, we are done.  Otherwise, we generate the transition row for the
        derivative at the position [next_state], add it to the list of rows, and
        then move on to the next position in the list of states.  Note that when 
        we generate the transition row, we may end up adding new states.  
     *)
    Fixpoint build_table' n (s:states) (rows:list (list nat)) (next_state:nat) : 
      option (states * list (list nat)) := 
      match n with 
        | 0 => None
        | S n' => 
          match nth_error s next_state with 
            | None => Some (s, rows)
            | Some r => 
              let (s1, row) := gen_row r s in 
                build_table' n' s1 (rows ++ (row::nil)) (1 + next_state)
          end
      end.

    (** We start with the initial [astgram] in state 0 and then try to close 
        off the table. *)
    Definition build_transition_table n (r:astgram) := build_table' n (r::nil) nil 0.

    Definition build_accept_table (s:states) : list bool := List.map accepts_null s.
    Definition build_rejects (s:states) : list bool := List.map always_rejects s.

    Definition build_dfa n (r:astgram) : option DFA := 
      match build_transition_table n r with 
        | None => None
        | Some (states, table) => 
          Some {| dfa_num_states := length states ; 
                  dfa_states := states ; 
                  dfa_transition := table ;
                  dfa_accepts := build_accept_table states ; 
                  dfa_rejects := build_rejects states |}
      end.

    Section DFA_RECOGNIZE.
      Variable d : DFA.
      (** This loop is intended to find the shortest match (if any) for
          a sequence of tokens, given a [DFA].  It returns [(Some (n,
          ts'))] when there is a match and where [ts'] is the
          unconsumed input and n is the length of the consumed input.
          If there is no match, it returns [None].  This is just one
          example of a recognizer that can be built with the DFA. *)

      Fixpoint dfa_loop state (count: nat) (ts : list token_id) : 
        option (nat * list token_id) := 
        if nth state (dfa_accepts d) false then Some (count, ts)
        else 
          match ts with 
          | nil => None
          | t::ts' => let row := nth state (dfa_transition d) nil in 
                      let new_state := nth t row num_tokens in
                      dfa_loop new_state (S count) ts'
        end.

      Definition dfa_recognize (ts:list token_id) : option (nat * list token_id) := 
        dfa_loop 0 0 ts.
    End DFA_RECOGNIZE.

    (** In what follows, we try to give some lemmas for reasoning about the
        DFA constructed from a parser. *)
    Require Import Omega.

    Lemma nth_error_app : forall A (xs ys:list A), 
      nth_error (xs ++ ys) (length xs) = nth_error ys 0.
    Proof.
      induction xs ; mysimp.
    Qed.

    Ltac s := repeat (mysimp ; subst).

    Lemma find_index'_prop : forall r s2 s1, 
      match find_index' r (length s1) s2 with
        | Some i => nth_error (s1 ++ s2) i = Some r
        | _ => True
      end.
    Proof.
      induction s2. mysimp. simpl. intros.
      destruct (astgram_dec r a). s. rewrite nth_error_app. auto.
      generalize (IHs2 (s1 ++ (a::nil))).
      assert (length (s1 ++ a::nil) = S (length s1)). rewrite app_length. simpl. omega.
      rewrite H. rewrite app_ass. simpl. auto.
    Qed.

    Lemma nth_error_ext : forall A n (xs ys:list A) (v:A), 
      Some v = nth_error xs n -> nth_error (xs ++ ys) n = Some v.
    Proof.
      induction n. destruct xs. simpl. unfold error. intros. congruence. 
      simpl. intros. auto. simpl. destruct xs ; simpl ; unfold error ; intros.
      congruence. auto.
    Qed.

    Lemma nth_error_lt : forall A (xs ys:list A) n, 
      n < length xs -> nth_error (xs ++ ys) n = nth_error xs n.
    Proof.
      induction xs ; mysimp. assert False. omega. contradiction. 
      destruct n. auto. simpl. apply IHxs. omega.
    Qed.

    (** Calling [find_or_add_prop r s] yields a well-formed state, ensures that
        if we lookup the returned index, we get [r], and that the state is only
        extended. *)
    Lemma find_or_add_prop : forall r s, 
      match find_or_add r s with 
        | (s',i) => nth_error (s ++ s') i = Some r 
      end.
    Proof.
      unfold find_or_add, find_index. intros. generalize (find_index'_prop r s nil). 
      simpl. intros. destruct (find_index' r 0 s).  mysimp. 
      rewrite nth_error_app. auto.
    Qed.

    (** This is the main loop-invariant for [gen_row'].  Given a 
        astgram [r], a list of states [s], and a token number [n], 
        running [gen_row' n r s (num_tokens - n)] yields a list of states [s2]
        and transition-table [row2] such that the
        length of [row2] is [n], [s2] is an extension of [s], and for all
        [m], the [mth] element of [s2] is the [unit_derivs] of [r] with 
        respect to the token [m+num_tokens-n]. *)
    Lemma gen_row'_prop n r s : 
      n <= num_tokens -> 
      match gen_row' n r s (num_tokens - n) with 
        | (s2, row2) => 
          length row2 = n /\ 
          (exists s1, s2 = s ++ s1) /\ 
          forall m, 
            m < n -> 
            match nth_error s2 (nth m row2 num_tokens) with 
              | Some r' => r' = unit_derivs r (token_id_to_chars (m + num_tokens - n)) 
              | None => False
            end
      end.
    Proof.
      induction n. mysimp. exists nil. apply app_nil_end. intros. assert False. omega.
      contradiction. Opaque token_id_to_chars. Opaque num_tokens. simpl. intros.
      remember (find_or_add (unit_derivs r (token_id_to_chars (num_tokens - S n))) s).
      destruct p. remember (gen_row' n r (s ++ s0) (S (num_tokens - S n))). destruct p.
      generalize (find_or_add_prop 
        (unit_derivs r (token_id_to_chars (num_tokens - S n))) s).
      rewrite <- Heqp.
      assert (n <= num_tokens). omega. intros. 
      specialize (IHn r (s ++ s0) H0). 
      assert (S (num_tokens - S n) = num_tokens - n). omega. rewrite <- H2 in IHn.
      rewrite <- Heqp0 in IHn. mysimp. rewrite app_ass in H4. exists (s0 ++ x). auto.
      destruct m. intros. simpl. subst. 
      rewrite (nth_error_ext n0 (s ++ s0) x (eq_sym H1)). auto.
      intros. assert (m < n). omega. specialize (H5 _ H7).
      assert (S m + num_tokens - S n = m + num_tokens - n). omega.
      rewrite H8. auto.
   Qed.

   (** This is the main invariant for the [build_table] routine.  Given a well-formed
       list of states [s] and a list of transition-table rows [ros], then for 
       all [i < n], [s(i)] and [r(i)] are defined, and the row [r(i)] is well-formed
       with respect to the state [s(i)]. *)
   Definition build_table_inv s rows n := 
     forall i, i < n -> 
       match nth_error s i, nth_error rows i with 
         | Some r, Some row => 
           length row = num_tokens /\ 
           forall t, t < num_tokens -> 
             match nth_error s (nth t row num_tokens) with 
               | Some r' => r' = unit_derivs r (token_id_to_chars t)
               | None => False
             end
         | _, _ => False
       end.

   Lemma nth_error_some : forall A (xs:list A) n (v:A), 
     Some v = nth_error xs n -> n < length xs.
   Proof.
     induction xs ; destruct n ; simpl in * ; unfold error, value in * ; mysimp ; 
     try congruence. omega. generalize (IHxs n v H). intros. omega.
   Qed.

   Lemma build_table_inv_imp s rows n : 
     build_table_inv s rows n -> n <= length s /\ n <= length rows.
   Proof.
     unfold build_table_inv ; destruct n. intros. auto with arith.
     intros. assert (n < S n). auto with arith. generalize (H n H0).
     remember (nth_error s n) as e1. remember (nth_error rows n) as e2.
     destruct e1; destruct e2 ; try tauto. intros. 
     generalize (nth_error_some _ _ Heqe1).
     generalize (nth_error_some _ _ Heqe2). intros. omega.
   Qed.

   Lemma nth_error_none A n (xs:list A) : None = nth_error xs n -> length xs <= n.
   Proof.
     induction n ; destruct xs ; simpl in * ; 
     unfold error, value in * ; intros ; auto with arith ; congruence.
   Qed.

   (** This lemma establishes that the [build_table'] loop maintains the
       [build_table_inv] and only adds to the states and rows of the table. *)
   Lemma build_table'_prop n s rows : 
     build_table_inv s rows (length rows) -> 
     match build_table' n s rows (length rows) with 
       | None => True
       | Some (s', rows') => 
         length rows' = length s' /\ 
         build_table_inv s' rows' (length rows') /\ 
         (exists s1, s' = s ++ s1) /\ 
         (exists rows1, rows' = rows ++ rows1)
     end.
   Proof.
     induction n. simpl. auto.
     intros. generalize (build_table_inv_imp H). intros. destruct H0. simpl.
     remember (nth_error s (length rows)). destruct e.
     Focus 2. mysimp. generalize (nth_error_none _ _ Heqe). intros. 
     apply le_antisym ; auto.
     exists nil. apply app_nil_end. exists nil. apply app_nil_end.
     unfold gen_row.
     assert (num_tokens <= num_tokens). omega. 
     generalize (gen_row'_prop a s H2). rewrite minus_diag.
     remember (gen_row' num_tokens a s 0) as p. destruct p. mysimp.
     match goal with 
       | [ |- match build_table' n s0 ?e1 ?e2 with | Some _ => _ | None => _ end ] => 
         specialize (IHn s0 e1) ; remember (build_table' n s0 e1 e2) as popt ; 
         assert (length e1 = S (length rows))
     end.
     rewrite app_length ; simpl ; rewrite plus_comm ; auto.
     rewrite <- H6 in Heqpopt. unfold token_id in *. 
     rewrite <- Heqpopt in IHn.
     destruct popt ; auto. destruct p.
           
     assert (build_table_inv s0 (rows ++ l ::nil) (S (length rows))).
     Focus 2. rewrite <- H6 in H7. specialize (IHn H7). s ; rewrite app_ass. 
     exists (x ++ x1). auto.  simpl. exists (l::x0). auto. clear IHn.

     unfold build_table_inv. intros. 
     assert (i < length rows \/ i = length rows).
     omega. destruct H8. generalize (H i H8). subst. 
     remember (nth_error s i) as e. destruct e ; simpl ; try tauto.
     remember (nth_error rows i) as e. destruct e ; simpl ; try tauto. intros.
     rewrite (nth_error_ext i s x Heqe0). unfold token_id.
     rewrite (nth_error_ext i rows (l::nil) Heqe1). 
     intros. unfold token_id in *.  rewrite <- Heqe1 in H4. destruct H4. split. auto. 
     intros.
     specialize (H9 _ H10). 
     remember (nth_error s (nth t l1 num_tokens)) as e. destruct e ; try contradiction.
     remember (nth_error_ext (nth t l1 num_tokens) s x Heqe2). rewrite e. auto.
     subst. unfold token_id in *. rewrite <- Heqe1. intro ; contradiction.
     subst.
     rewrite (nth_error_ext (length rows) s x Heqe). unfold token_id in *.
     rewrite (nth_error_app rows (l::nil)). simpl. mysimp.
     intros. generalize (H5 _ H4). assert (t + num_tokens - num_tokens = t).
     omega. rewrite H8. auto.
  Qed.

  (** This predicate captures the notion of a correct [DFA] with respect to
      an initial astgram [r].  In essence, it says that the lengths of all of
      the lists is equal to [dfa_num_states d], that [r] is at [dfa_states(0)],
      each row of the [dfa_transition] table is well-formed, that 
      [accepts(i)] holds iff the corresponding state accepts the empty string,
      and when [rejects(i)] is true, the corresponding state rejects all strings. *)
  Definition wf_dfa (r:astgram) (d:DFA) := 
    let num_states := dfa_num_states d in
    let states := dfa_states d in 
    let transition := dfa_transition d in 
    let accepts := dfa_accepts d in 
    let rejects := dfa_rejects d in 
    num_states = length states /\ 
    num_states = length transition /\ 
    num_states = length accepts /\ 
    num_states = length rejects /\ 
    nth_error states 0 = Some r /\ 
    forall i, i < num_states -> 
      let r' := nth i states aZero in
      let acc := nth i accepts false in 
      let rej := nth i rejects false in 
      let row := nth i transition nil in 
        length row = num_tokens /\ 
        (acc = true <-> exists v:interp (astgram_type r'), in_astgram r' nil v) /\ 
        (rej = true -> forall s, ~(exists v, in_astgram r' s v)) /\ 
        (forall t, t < num_tokens -> 
          nth t row num_tokens < num_states /\
          nth (nth t row num_tokens) states aZero = 
          unit_derivs r' (token_id_to_chars t)).

    Lemma nth_error_nth A (xs:list A) n (v dummy:A) : 
      Some v = nth_error xs n -> nth n xs dummy = v.
    Proof.
      induction xs ; destruct n ; simpl in * ; unfold error, value in * ; mysimp ; 
        try congruence.
    Qed.

    (** These next few lemmas establish the correctness of [accepts_null]. *)
    Lemma accepts_null_corr1' (r:astgram) : 
      accepts_null r = true -> 
      exists v, in_astgram r nil v.
    Proof.
      induction r ; mysimp ; try congruence. exists tt. constructor. auto. auto.
      generalize (andb_prop _ _ H). mysimp. generalize (IHr1 H0) (IHr2 H1). mysimp.
      exists (x0,x). econstructor ; eauto. generalize (orb_prop _ _ H). mysimp.
      generalize (IHr1 H0). mysimp. exists (inl _ x). econstructor ; auto. auto.
      generalize (IHr2 H0). mysimp. exists (inr _ x). eapply InaAlt_r ; auto. auto.
      exists nil. constructor ; auto. 
    Qed.

    Lemma accepts_null_corr1 (r:astgram) : 
      accepts_null r = true -> exists v, in_astgram r nil v.
    Proof.
      intros. generalize (accepts_null_corr1' _ H). mysimp. exists x ; eauto.
    Qed.

    Lemma accepts_null_corr2' (r:astgram) v : 
      in_astgram r nil v -> 
      accepts_null r = true.
    Proof.
      intros r v H. dependent induction H ; s ; try congruence.
      generalize (app_eq_nil _ _ (eq_sym H1)). mysimp. subst.
      rewrite (IHin_astgram2 (eq_refl _)). rewrite (IHin_astgram1 (eq_refl _)). auto.
      rewrite IHin_astgram. auto. rewrite IHin_astgram. 
      destruct (accepts_null a1) ; auto.
    Qed.

    Lemma accepts_null_corr2 (r:astgram) v : 
      in_astgram r nil v -> accepts_null r = true.
    Proof.
      intros. apply (@accepts_null_corr2' r v H).
    Qed.

    (** [accepts_null] is correct. *)
    Lemma accepts_null_corr (r:astgram) : 
      accepts_null r = true <-> (exists v, in_astgram r nil v).
    Proof.
      intros. split. apply accepts_null_corr1 ; auto. mysimp. 
      apply (accepts_null_corr2 H).
    Qed.

    (** [always_rejects] is correct. *)
    Lemma always_rejects_corr (r:astgram) : 
      always_rejects r = true -> forall s v, ~ in_astgram r s v.
    Proof.
      induction r ; mysimp ; try congruence. destruct v ; auto.
      generalize (orb_prop _ _ H). mysimp. generalize (IHr1 H0). intros.
      intro. generalize (inv_acat H2). mysimp. subst. apply (H1 x x1). auto.
      generalize (IHr2 H0). intros. intro. generalize (inv_acat H2).
      mysimp. s. apply (H1 x0 x2) ; auto.
      generalize (andb_prop _ _ H). mysimp. intro. generalize (inv_aalt H2). mysimp.
      eapply IHr1 ; eauto. eapply IHr2 ; eauto. 
    Qed.

    (** [build_dfa] is (partially) correct.  Note that we do not show that there's
        always an [n], hence the partiality. *)
    Lemma build_dfa_wf (r:astgram) (d:DFA) :
      forall n, build_dfa n r = Some d -> wf_dfa r d.
    Proof.
      unfold build_dfa, build_transition_table. intros.
      assert (build_table_inv (r::nil) nil 0). 
      unfold build_table_inv. intros. 
      destruct i. simpl. assert False. omega. contradiction. simpl.
      assert False. omega.
      contradiction. generalize (build_table'_prop n H0). simpl. intros. 
      unfold token_id in *.
      destruct (build_table' n (r::nil) nil 0) ; try congruence.
      destruct p as [s' rows']. injection H ; clear H ; intros ; mysimp. 
      unfold wf_dfa. simpl. mysimp ; try (subst ; simpl ;  auto ; fail).
      subst. simpl. unfold build_accept_table.
      rewrite map_length. auto. subst. simpl. unfold build_rejects. 
      rewrite map_length. auto.
      (*rewrite H1. unfold value. auto. intros. rewrite <- H0 in H5. *)
      unfold build_table_inv in H2. rewrite H1 in H2. intros.
      rewrite <- H in H5 ; simpl in H5.
      specialize (H2 _ H5). 
      remember (nth_error s' i) as e. destruct e ; try contradiction. 
      unfold token_id in *.
      remember (nth_error rows' i) as e. destruct e ; try contradiction. destruct H2.
      split. assert (i < length x). subst. omega. rewrite <- H. simpl. rewrite <- H2.
      rewrite (nth_error_nth rows' i _ Heqe0). auto. 
      (* split. rewrite (nth_error_nth rows' i nil Heqe0). auto. 
      rewrite (nth_error_nth s' i (Zero _) Heqe). *)
      rewrite <- H ; simpl.
      unfold build_accept_table. unfold build_rejects. unfold token_id.
      generalize (map_nth accepts_null s' aZero i). intro. simpl in H7. rewrite H7.
      generalize (map_nth always_rejects s' aEps i). intro. simpl in H8. rewrite H8.
      rewrite (nth_error_nth s' i _ Heqe). 
      rewrite (nth_error_nth s' i _ Heqe). split. apply accepts_null_corr. split.
      intros. intro. mysimp. eapply always_rejects_corr ; eauto. 
      intros. subst.
      rewrite (nth_error_nth x i _ Heqe0). 
      generalize (H6 _ H9). 
      remember (nth_error (r::x0) (nth t l num_tokens)). destruct e ; try tauto. intros.
      subst. unfold token_id in *.
      rewrite (nth_error_nth (r::x0) (nth t l num_tokens) _ Heqe1).
      split ; auto. generalize Heqe1. clear Heqe1.  rewrite <- H2.
      generalize (nth t l (length l)) (r::x0). induction n0 ; destruct l0 ; simpl ; 
      unfold error, value ; intros ; try congruence. omega. generalize (IHn0 _ Heqe1).
      intros. omega.
   Qed.

  (** ** Building a recognizer which ignores semantic actions. *)
  Definition par2rec t (g:grammar t) : astgram := 
    let (ag, _) := split_astgram g in ag.

  (** The translation from parsers to regexps which throws away the maps is correct. *)
  Lemma par2rec_corr1 t (g:grammar t) cs v : 
    in_grammar g cs v -> exists v, in_astgram (par2rec g) cs v.
  Proof.
    unfold par2rec.
    induction 1 ; s ; eauto ; unfold ag_and_fn, fixfn ; 
    try (remember (split_astgram g1) as e1 ; remember (split_astgram g2) as e2 ; 
         destruct e1 ; destruct e2 ; eauto) ; 
    try (remember (split_astgram g) as e ; destruct e ; eauto).
  Qed.

  Lemma par2rec_corr2 t (g:grammar t) cs v1 : 
    in_astgram (par2rec g) cs v1 -> exists v2, in_grammar g cs v2.
  Proof.
    unfold par2rec.
    induction g ; mysimp ; unfold ag_and_fn, fixfn in * ; 
    try (remember (split_astgram g) as e ; destruct e) ; 
    try (remember (split_astgram g1) as e1 ; destruct e1 ; 
         remember (split_astgram g2) as e2 ; destruct e2) ; 
    ainv ; subst ; mysimp ; eauto ; repeat 
    match goal with 
        | [ H1 : forall cs v, in_astgram ?x _ _ -> _ ,
            H2 :  in_astgram ?x _ _ |- _ ] => specialize (H1 _ _ H2) ; mysimp ; eauto
    end.
    dependent induction H. eauto. clear IHin_astgram1.
    specialize (IHin_astgram2 _ _ _ Heqe IHg v2 (eq_refl _) (JMeq_refl _)). mysimp.
    specialize (IHg _ _ H). mysimp.
    econstructor ; eapply InStar_cons ; eauto. 
  Qed.

  (** A simple recognizer -- given a grammar [g] and string [cs], returns a 
     proof that either either [cs] matches the grammar [g] (i.e., there is
     some semantic value that [cs] would parse into) or else there is no 
     match (i.e., there is no value that it can parse into.)  I don't think
     we actually use this anywhere.  Just here for fun.  *)
  Definition recognize t (g:grammar t) cs : 
    {exists v, in_grammar g cs v} + {forall v, ~ in_grammar g cs v}.
    intros.
    remember (derivs_and_split (par2rec g) cs) as p.
    destruct p as [a f].
    remember (accepts_null a) as b.
    destruct b ; [ left | right ].
    unfold par2rec in *. generalize (split_astgram_corr1 g). intro.
    remember (split_astgram g) as e. destruct e.
    generalize (accepts_null_corr1' a (eq_sym Heqb)). intro. destruct H0.
    generalize (@derivs_and_split_corr2 cs x (xinterp f x0)). unfold in_agxf.
    rewrite <- Heqp. intros. 
    assert (in_astgram x cs (xinterp f x0)). apply H1. eauto.
    specialize (H _ _ H2). eauto.
    intros. intro. unfold par2rec in *. generalize (split_astgram_corr2 g).
    intro. remember (split_astgram g) as e ; destruct e. specialize (H0 _ _ H).
    destruct H0. destruct H0. subst.
    generalize (@derivs_and_split_corr1 cs x x0 H0). unfold in_agxf. simpl.
    rewrite <- Heqp. mysimp. subst. generalize (accepts_null_corr2 H1). intro.
    rewrite H2 in Heqb. discriminate Heqb.
  Defined.

   (** This is a simple function which runs a DFA on an entire string, returning
       true if the DFA accepts the string, and false otherwise.  In what follows,
       we prove that [run_dfa] is correct... *)
   Fixpoint run_dfa (d:DFA) (state:nat) (ts:list token_id) : bool := 
     match ts with 
       | nil => nth state (dfa_accepts d) false
       | t::ts' => run_dfa d (nth t (nth state (dfa_transition d) nil) num_tokens) ts'
     end.

   (** This lifts the [unit_deriv_corr1] to strings. *)
   Lemma unit_derivs_corr1 cs1 (r:astgram) cs2 v : 
     in_astgram (unit_derivs r cs1) cs2 v -> 
     exists v, in_astgram r (cs1 ++ cs2) v.
   Proof.
     unfold unit_derivs. 
     induction cs1 ; simpl ; eauto. intros.
     generalize (@deriv_and_split_corr2 r a (cs1 ++ cs2)). unfold in_agxf. intro.
     remember (deriv_and_split r a) as e ; destruct e.
     specialize (IHcs1 x cs2). remember (derivs_and_split x cs1) as e ; destruct e.
     unfold agxf in *. specialize (IHcs1 _ H). destruct IHcs1 as [v' IHcs1]. 
     exists (xinterp x0 v'). apply H0. exists v'. auto.
   Qed.

   (** Lifts [unit_deriv_corr2] to strings. *)
   Lemma unit_derivs_corr2 cs t (g:grammar t) v : 
     in_grammar g cs v -> 
     let (a,_) := split_astgram g in 
     let a' := unit_derivs a cs in
     exists v', in_astgram a' nil v'.
   Proof.
     intros. generalize (split_astgram_corr2 g). remember (split_astgram g) as e.
     destruct e. intro. specialize (H0 _ _ H). mysimp. subst.
     unfold unit_derivs. remember (derivs_and_split x cs) as e. destruct e.
     generalize (derivs_and_split_corr1 H0). unfold in_agxf. rewrite <- Heqe0.
     mysimp. subst. eauto.
   Qed.

   Definition list_all(A:Type)(P:A->Prop) : list A -> Prop := 
     fold_right (fun x a => P x /\ a) True.

   Lemma lt_nth_error : forall A (xs:list A) n dummy v, 
     n < length xs -> nth n xs dummy = v -> nth_error xs n = Some v.
   Proof.
     induction xs ; destruct n ; mysimp ; try (assert False ; [ omega | contradiction] ); 
       unfold error, value in * ; s. apply (IHxs n dummy). omega. auto.
   Qed.

   Lemma flat_map_app A B (f:A->list B) (ts1 ts2:list A) : 
     flat_map f (ts1 ++ ts2) = (flat_map f ts1) ++ (flat_map f ts2).
   Proof.
     induction ts1 ; mysimp. rewrite app_ass. rewrite IHts1. auto.
   Qed.
   
   Lemma unit_derivs_flat_map r ts1 ts2 : 
     unit_derivs r (flat_map token_id_to_chars (ts1 ++ ts2)) = 
     unit_derivs (unit_derivs r (flat_map token_id_to_chars ts1)) 
     (flat_map token_id_to_chars ts2).
   Proof.
     intros. rewrite flat_map_app. generalize (flat_map token_id_to_chars ts1) r
     (flat_map token_id_to_chars ts2). unfold unit_derivs. induction l ; mysimp. 
     remember (deriv_and_split r0 a) as e ; destruct e. 
     specialize (IHl x l0). remember (derivs_and_split x (l ++ l0)) as e ; destruct e.
     remember (derivs_and_split x l) as e ; destruct e. subst. unfold agxf. auto.
   Qed.

   (** This lemma tells us that if we start with a grammar [g], build a [DFA],
       and then run the [DFA] on a list of tokens, then we get [true] iff
       the grammar would've accepted the string and produced a value.  *)
   Lemma dfa_corr' : forall t (g:grammar t) n (d:DFA), 
     build_dfa n (par2rec g) = Some d -> 
     forall ts2 ts1 state, 
       nth_error (dfa_states d) state = 
       Some (unit_derivs (par2rec g) (flat_map token_id_to_chars ts1)) -> 
       list_all (fun t => t < num_tokens) ts2 ->
       if run_dfa d state ts2 then
         exists v, in_grammar g (flat_map token_id_to_chars (ts1 ++ ts2)) v
       else 
         forall v, ~ in_grammar g (flat_map token_id_to_chars (ts1 ++ ts2)) v.
   Proof.
     intros t p n d H. assert (wf_dfa (par2rec p) d). eapply build_dfa_wf ; eauto.
     unfold wf_dfa in H0. induction ts2 ; mysimp.
     assert (state < dfa_num_states d). rewrite H0. generalize H1. 
     generalize (unit_derivs (par2rec p) (flat_map token_id_to_chars ts1)).
     generalize (dfa_states d) state. 
     induction l ; destruct state0 ;  mysimp ; unfold error, value in * ; try congruence. 
     subst. omega. subst. generalize (IHl _ _ H8). intros. omega. 
     generalize (H7 _ H8). mysimp. remember (nth state (dfa_accepts d) false) as e.
     destruct e. generalize (H10 (eq_refl _)).
     rewrite (nth_error_nth (dfa_states d) state _ (eq_sym H1)). intros. mysimp.
     generalize (unit_derivs_corr1 _ _ H14).
     rewrite <- app_nil_end. mysimp. apply (par2rec_corr2 p H15).
     unfold not. intros. assert (false = true).
     apply H13. rewrite (nth_error_nth (dfa_states d) state _ (eq_sym H1)).
     generalize (@par2rec_corr1 t p (flat_map token_id_to_chars ts1) v H14). intro.
     generalize (unit_derivs_corr2 H14). unfold par2rec. 
     remember (split_astgram p) as e. destruct e. auto. congruence.
     
     generalize (IHts2 (ts1 ++ a::nil) 
       (nth a (nth state (dfa_transition d) nil) num_tokens)). 
     rewrite app_ass. simpl. intros. apply H9 ; auto. clear H9 IHts2.
     assert (state < dfa_num_states d). rewrite H0. generalize H1.
     generalize (unit_derivs (par2rec p) (flat_map token_id_to_chars ts1)).
     generalize (dfa_states d) state. induction l ; destruct state0 ; mysimp ; 
     unfold error, value in * ; try congruence; try omega. 
     generalize (IHl _ _ H9). intros. omega.
     generalize (H8 _ H9) ; mysimp. generalize (H13 _ H2). mysimp.
     rewrite unit_derivs_flat_map. simpl. rewrite <- app_nil_end.
     generalize (H13 _ H2). mysimp. (*rewrite H0 in H18.*)
     apply (lt_nth_error (dfa_states d) aZero). omega. rewrite H18.
     rewrite (nth_error_nth _ _ aZero (eq_sym H1)). auto.
  Qed.

  (** Here is the key correctness property for the DFAs. *)
  Lemma dfa_corr t (g:grammar t) n (d:DFA) :
    build_dfa n (par2rec g) = Some d -> 
    forall ts, 
      list_all (fun t => t < num_tokens) ts -> 
      if run_dfa d 0 ts then 
        exists v, in_grammar g (flat_map token_id_to_chars ts) v
      else 
        forall v, ~ in_grammar g (flat_map token_id_to_chars ts) v.
  Proof.
    intros. assert (ts = nil ++ ts) ; auto. rewrite H1. eapply dfa_corr' ; eauto.
    assert (wf_dfa (par2rec g) d). eapply build_dfa_wf ; eauto.
    unfold wf_dfa in H2. mysimp.
  Qed.

  Definition accepts_at_most_one_null (a:astgram) : bool := 
    if le_gt_dec (List.length (astgram_extract_nil a)) 1 then true else false.

  Fixpoint enum_tokens (f:token_id -> bool) (n:nat) : bool := 
    match n with 
      | 0 => true
      | S m => (f m) && enum_tokens f m
    end.

  Definition forall_tokens (f:token_id -> bool) : bool := enum_tokens f num_tokens.

  (** Properties of dfa_recognize *)
  Lemma dfa_loop_run : forall ts d state count count2 ts2,
    dfa_loop d state count ts = Some (count2, ts2) -> 
    exists ts1, 
      ts = ts1 ++ ts2 /\ count2 = length ts1 + count /\ 
      run_dfa d state ts1 = true /\
      forall ts1' ts2',
        ts = ts1' ++ ts2' -> 
        length ts1' < length ts1 -> 
        ~ run_dfa d state ts1' = true.
  Proof.
    induction ts ; mysimp ; remember (nth state (dfa_accepts d) false) ; 
    destruct y ; try congruence ; try (injection H ; mysimp ; clear H ; subst). 
    exists nil. rewrite Heqy. repeat split ; auto. intros. simpl in H0.
    assert False. omega. contradiction.
    exists nil. simpl. rewrite Heqy. repeat split ; auto.
    intros. assert False. omega. contradiction.
    specialize (IHts d _ _ _ _ H). mysimp. exists (a::x). simpl.
    split. subst ; auto. split ; subst ; auto. split ; auto. intros.
    destruct ts1'. simpl in *. rewrite <- Heqy. auto. simpl in H0.
    injection H0 ; intros ; subst; clear H0. 
    specialize (H3 _ _ H4). assert (length ts1' < length x). simpl in *.
    omega. specialize (H3 H0). simpl. congruence.
  Qed.

  Lemma list_all_app : forall A (f:A->Prop) (xs ys:list A), 
    list_all f (xs ++ ys) -> list_all f xs /\ list_all f ys.
  Proof.
    induction xs ; mysimp ; specialize (IHxs _ H0) ; mysimp.
  Qed.

  Lemma dfa_recognize_corr :
    forall t (g:grammar t) n (d:DFA),
    build_dfa n (par2rec g) = Some d -> 
    forall ts, 
      list_all (fun t => t < num_tokens) ts -> 
      match dfa_recognize d ts with 
        | None => True
        | Some (count,ts2) => 
          exists ts1, exists v, 
            ts = ts1 ++ ts2 /\ count = length ts1 /\ 
            in_grammar g (flat_map token_id_to_chars ts1) v /\
            forall ts3 ts4,
              length ts3 < length ts1 ->
              ts = ts3 ++ ts4 -> 
              forall v, ~ in_grammar g (flat_map token_id_to_chars ts3) v
      end.
  Proof.
    intros. unfold dfa_recognize. remember (dfa_loop d 0 0 ts) as e.
    destruct e ; auto. destruct p. 
    generalize (dfa_loop_run _ _ _ _ (eq_sym Heqe)). mysimp. subst.
    exists x. generalize (list_all_app _ _ _ H0).  mysimp.
    generalize (dfa_corr _ _ H _ H1).  rewrite H3. mysimp. 
    rewrite plus_comm. simpl. exists x0. repeat split ; auto.
    intros. specialize (H4 _ _ H7 H6). intro. apply H4.
    rewrite H7 in H0. generalize (list_all_app _ _ _ H0). mysimp.
    generalize (@dfa_corr _ g n d H ts3 H9).
    destruct (run_dfa d 0 ts3). auto. intros. assert False.
    eapply H11. eauto. contradiction.
  Qed.
