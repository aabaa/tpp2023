(* TPPmark2023 solution by Mitsuharu Yamamato *)
(* Developed on Coq 8.18.0 and MathComp 2.1.0 *)

(* https://aabaa.github.io/tpp2023/

   In N-in-a-row game, the first and second players take turns placing
   stones on a Go board, and the winner being the player who first
   places its own N stones in a row in either vertical, horizontal, or
   diagonal direction. In the following, the Go board is assumed to be
   infinite.

   1. Formalize N-in-a-row game.
   2. Prove that there is no winning strategy for the second player in
      N-in-a-row game.
   3. Prove that if N is sufficiently large, the first player has no
      winning strategy.
      * Hint: The pairing strategy shows that if N ≧ 9, then there is
        no winning strategy for the first player.
      * Reference: L Győrffy, G Makay, A Pluhár: The pairing
        strategies of the 9-in-a-row game
        https://www.math.u-szeged.hu/~lgyorffy/predok/9_pairings.pdf *)

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Abstract version: strong positional game *)

Section StrongPositionalGame.

(* 1. Formalize strong positional games. *)

Variable position : eqType.
Definition moves : Type := seq position.
Variable winmoves : pred moves.
Hypothesis empty_not_winmoves : ~~ winmoves [::].
Hypothesis winmoves_supset_closed :
  forall s s' : moves, {subset s <= s'} -> winmoves s -> winmoves s'.

Definition player := bool. (* false ... player 0, true ... player 1 *)
Definition oppo : player -> player := negb.

Definition turn (s : moves) : player := odd (size s).

Lemma turn_nil : turn [::] = false.
Proof. by []. Qed.

Lemma turn_cons (pos : position) (s : moves) : turn (pos :: s) = negb (turn s).
Proof. by []. Qed.

Fixpoint player_moves (p : player) (s : moves) : moves :=
  if s is pos :: s' then
    if turn s' == p then pos :: player_moves p s' else player_moves p s'
  else [::].

Lemma suffix_player_moves (s1 s2 : moves) (p : player) :
  suffix s1 s2 -> suffix (player_moves p s1) (player_moves p s2).
Proof.
  case/suffixP=> s ->; elim: s => /= [|pos s IHs]; first by rewrite suffix_refl.
  by case: ifP => //; rewrite (suffix_trans IHs) // suffix_cons.
Qed.

Lemma perm_cat_player_moves (s : moves) :
  perm_eql s (player_moves false s ++ player_moves true s).
Proof.
  apply/permPl; elim: s => //= pos s; case: turn; last by rewrite perm_cons.
  by move/(perm_catl [:: pos]) => ->; rewrite perm_catCA.
Qed.

Lemma player_movesP (p : player) (pos : position) (s : moves) :
  reflect (exists (s1 s2 : moves), s = s1 ++ pos :: s2 /\ turn s2 = p)
    (pos \in player_moves p s).
Proof.
  apply: (iffP idP).
    elim: s => [|pos' s IHs] //= in p *.
    case: ifPn => [/eqP<-|_]; last first.
      by case/IHs=> s1 [s2 [-> <-]]; exists (pos' :: s1), s2.
    rewrite inE => /predU1P[->|]; first by exists [::], s.
    by case/IHs=> s1 [s2 [-> <-]]; exists (pos' :: s1), s2.
  case=> s1 [s2 [-> <-]].
  elim: s1 => [|pos' s1 IHs1] /=; first by rewrite eqxx inE eqxx.
  by case: ifP; rewrite ?inE IHs1 ?orbT.
Qed.

Definition win (p : player) (s : moves) : bool := winmoves (player_moves p s).

Lemma win_nil (p : player) : ~~ win p [::].
Proof. by case: p. Qed.

Lemma win_oppo_turn (s : moves) (pos : position) :
  ~~ win (oppo (turn s)) s -> ~~ win (oppo (turn s)) (pos :: s).
Proof. by rewrite /win /=; case turn. Qed.

Lemma win_suffix p (s1 s2  : moves) : suffix s1 s2 -> win p s1 -> win p s2.
Proof.
  rewrite /win => /(suffix_player_moves p) suf.
  by apply/winmoves_supset_closed/mem_infix/suffixW.
Qed.

Definition full (s : moves) : Prop := forall pos : position, pos \in s.
Variable fullb : moves -> bool.
Hypothesis fullP : forall (s : moves), reflect (full s) (fullb s).

Lemma subset_fullb (s1 s2 : moves) : {subset s1 <= s2} -> fullb s1 -> fullb s2.
Proof. by move=> subs1s2 /fullP-full_s1; apply/fullP=> pos; apply: subs1s2. Qed.

Lemma fullb_cons (pos : position) (s : moves) : fullb s -> fullb (pos :: s).
Proof.
  by apply: subset_fullb => pos'; rewrite inE => ->; rewrite orbT.
Qed.

Lemma fullb_size_leq (s1 s2 : moves) :
  fullb s1 -> uniq s2 -> size s1 <= size s2 -> fullb s2.
Proof.
  move/fullP=> full_s1 uniq_s2 size_leq; apply/fullP=> pos.
  have [/allP-s2_sub_s1|] := boolP (all [mem s1] s2).
    by rewrite (uniq_min_size _ s2_sub_s1).
  by rewrite -has_predC => /hasP[pos'] /=; rewrite full_s1.
Qed.

Definition deadend (s : moves) : bool :=
  fullb s || [exists p : player, win p s].

Lemma deadend_cons (pos : position) (s : moves) :
  deadend s -> deadend (pos :: s).
Proof.
  rewrite /deadend; case/orP=>[full_s|]; first by rewrite fullb_cons.
  case/existsP=> p win_p; apply/orP; right; apply/existsP; exists p.
  by apply: win_suffix win_p; rewrite suffix_cons.
Qed.

Definition strategy : Type := moves -> position.

Definition valid_strategy (st : strategy) : Prop :=
  forall s : moves, ~~ fullb s -> st s \notin s.

Definition play (st : strategy) (s : moves) k : moves :=
  iter k (fun s => if deadend s then s else st s :: s) s.

Lemma play_leq_deadend (st : strategy) (s : moves) k k' :
  k <= k' -> deadend (play st s k) -> deadend (play st s k').
Proof.
  move/subnK<-; rewrite /play iterD -/(play _ _ _).
  elim: {k'}(k' - k) => // k' IHk'.
  by rewrite iterS; case: ifP => // _ /IHk'; apply: deadend_cons.
Qed.

Lemma size_play_leqif (st : strategy) (s : moves) k :
  size (play st s k) <= size s + k ?= iff (if k is k'.+1
                                           then ~~ deadend (play st s k')
                                           else true).
Proof.
  elim: k => /= [|k IHk]; first by rewrite addn0; apply/leqif_refl.
  apply/leqifP; rewrite if_neg.
  case: ifPn => [->|nde]; first by rewrite addnS ltnS IHk.
  rewrite (negPf nde) addnS /= eqSS {}IHk; case: k nde => // k.
  by apply/contraNN/play_leq_deadend.
Qed.

Lemma play_uniq (st : strategy) (s : moves) k :
  valid_strategy st -> uniq s -> uniq (play st s k).
Proof.
  move=> valid_st uniq_s; elim: k => //= k IHk.
  case: ifPn => //; rewrite /deadend negb_or.
  by case/andP=> not_full _ /=; rewrite valid_st.
Qed.

Lemma play_not_both_win (st : strategy) (s : moves) k :
  ~~ [forall p : player, win p s]
  -> ~~ [forall p : player, win p (play st s k)].
Proof.
  move=> both_not_win; elim: k => //= k IHk.
  case: ifPn => //; rewrite /deadend negb_or.
  case/andP=> _; apply: contraNN; move/forallP=> win_both.
  apply/existsP; exists (oppo (turn (play st s k))).
  exact: (contraTT (win_oppo_turn (st (play st s k)))).
Qed.

Lemma play_leq_suffix (st : strategy) (s : moves) k k' :
  k <= k' -> suffix (play st s k) (play st s k').
Proof.
  move/subnK<-; rewrite /play iterD.
  elim: {k'}(k' - k) => [|k' IHk']; first by rewrite suffix_refl.
  rewrite (suffix_trans IHk') // iterS.
  case: ifP; first by rewrite suffix_refl.
  by rewrite suffix_cons.
Qed.

Lemma play_leq_win (st : strategy) (s : moves) k k' p :
  k <= k' -> win p (play st s k) -> win p (play st s k').
Proof. by move/play_leq_suffix=> /(_ st s); apply: win_suffix. Qed.

Lemma suffix_play (s : moves) (st : strategy) k :
  suffix s (play st [::] k) = (s == play st [::] (size s)) && (size s <= k).
Proof.
  apply/idP/idP; last first.
    by case/andP=> /eqP{2}->; apply: play_leq_suffix.
  elim: k => [|k IHk /=] in s *; first by rewrite suffixs0 => /eqP->.
  case: ifPn => [_ /IHk|not_de]; first by case: (_ == _) => //; apply: leqW.
  move/suffixP=> [[|x s']] /=; last first.
    case=> _ /(ex_intro (fun s' => play st [::] k = s' ++ s) s')/suffixP/IHk.
    by case: (_ == _) => //; apply: leqW.
  move => <- /=.
  suff/eqP->: size (play st [::] k) == k by rewrite (negPf not_de) eqxx /=.
  rewrite size_play_leqif; case: (k) not_de => // k'; apply: contraNN.
  exact: play_leq_deadend.
Qed.

Definition alternate_strategy (st0 st1 : strategy) : strategy :=
  fun s : moves => if turn s then st1 s else st0 s.

Lemma alternate_strategy_valid (st0 st1 : strategy) :
  valid_strategy st0 -> valid_strategy st1
  -> valid_strategy (alternate_strategy st0 st1).
Proof.
  move=> valid_st0 valid_st1 s not_full; rewrite /alternate_strategy.
  by case: ifP => _; rewrite (valid_st0, valid_st1).
Qed.

Lemma play_alternate_strategyS (st0 st1 : strategy) (s : moves) k :
  play (alternate_strategy st0 st1) s k.+1 =
    let s' := play (alternate_strategy st0 st1) s k in
    if deadend s' then s'
    else if odd (size s + k) then st1 s' :: s' else st0 s' :: s'.
Proof.
  rewrite /=; case: ifPn => // nde; rewrite {1}/alternate_strategy /turn.
  suff/eqP->: size (play (alternate_strategy st0 st1) s k) == size s + k.
    by rewrite [in LHS]fun_if if_arg.
  rewrite size_play_leqif; case: k nde => // k.
  by apply: contraNN; apply: play_leq_deadend.
Qed.

Lemma player_moves_play_alternate_strategyS (p : player) (st0 st1 : strategy)
  (s : moves) k :
  player_moves p (play (alternate_strategy st0 st1) s k.+1) =
    let s' := play (alternate_strategy st0 st1) s k in
    if deadend s' || (odd (size s + k) != p) then player_moves p s'
    else if p then st1 s' :: player_moves p s'
         else st0 s' :: player_moves p s'.
Proof.
  rewrite play_alternate_strategyS /=; case: ifPn => //= nde.
  rewrite (fun_if (player_moves p)) /= /turn.
  suff/eqP->: size (play (alternate_strategy st0 st1) s k) == size s + k.
    by case: odd; case: p.
  rewrite size_play_leqif; case: k nde => // k.
  by apply: contraNN; apply: play_leq_deadend.
Qed.

Definition winning_strategy (p : player) (st : strategy) (s : moves) : Prop :=
  valid_strategy st
  /\ forall st' : strategy, valid_strategy st' -> exists k,
        win p (play (alternate_strategy
                       (if p then st' else st) (if p then st else st')) s k).

Lemma winning_strategies_not_both (s : moves) :
  ~~ [forall p : player, win p s]
  -> (exists st0 : strategy, winning_strategy false st0 s)
  -> (exists st1 : strategy, winning_strategy true st1 s)
  -> False.
Proof.
  move=> not_both_win [st0 [valid_st0 win_st0]] [st1 [valid_st1 win_st1]].
  have [k0 win_0] := win_st0 st1 valid_st1.
  have [k1 win_1] := win_st1 st0 valid_st0.
  pose k := maxn k0 k1.
  suff: forall p, win p (play (alternate_strategy st0 st1) s k).
    by apply/forallP; rewrite play_not_both_win.
  case; first by rewrite (play_leq_win (leq_maxr k0 k1)).
  by rewrite (play_leq_win (leq_maxl k0 k1)).
Qed.

(* 2. Prove that there is no winning strategy for the second player in
      strong positional games. *)

Variable fresh : strategy.
Hypothesis fresh_valid : valid_strategy fresh.

Fixpoint stolen_moves (s : moves) : moves * position :=
  if s is pos :: s' then
    let: (ss, ghost) := stolen_moves s' in
    if pos == ghost then let ghost' := fresh ss
                         in (ghost' :: ss, ghost')
    else (pos :: ss, ghost)
  else let ghost := fresh [::] in ([:: ghost], ghost).

Lemma stolen_moves_perm (s : moves) :
  let: (ss, ghost) := stolen_moves s in perm_eq ss (ghost :: s).
Proof.
  elim: s => /= [|pos s]; first by rewrite perm_refl.
  case: stolen_moves => ss ghost.
  case: ifP => [/eqP->|pos_ne]; first by rewrite perm_cons.
  rewrite -(perm_cons pos) => /permPl->.
  rewrite -/([:: pos; ghost] ++ s) -/([:: ghost; pos] ++ s) perm_cat2r.
  by rewrite -/([:: pos] ++ [:: ghost]) perm_catC.
Qed.

Lemma size_stolen_moves (s : moves) : size (stolen_moves s).1 = (size s).+1.
Proof.
  by move: (stolen_moves_perm s); case: stolen_moves => ? ?; apply: perm_size.
Qed.

Lemma stolen_moves_uniq (s : moves) :
  ~~ fullb s -> uniq s -> uniq (stolen_moves s).1.
Proof.
  elim: s => //= pos s IHs not_full.
  have not_full_s : ~~ fullb s by apply: contraNN not_full; apply: fullb_cons.
  case/andP=> pos_notin uniq_s.
  move: (IHs not_full_s) (stolen_moves_perm s).
  case: stolen_moves => ss ghost /= /(_ uniq_s)-uniq_ss.
  case: ifP => [/eqP<-|pos_ne] perm_ss /=; last first.
    by rewrite uniq_ss (perm_mem perm_ss) inE pos_ne pos_notin.
  have not_full_ss : ~~ fullb ss.
    apply: contraNN not_full; apply: subset_fullb => pos'.
    by rewrite (perm_mem perm_ss).
  by rewrite fresh_valid ?uniq_ss.
Qed.

Lemma stolen_moves_fullb (s : moves) : fullb s -> fullb (stolen_moves s).1.
Proof.
  apply: subset_fullb => pos pos_in_s; move: (stolen_moves_perm s).
  by case: stolen_moves => ss ghost; move/perm_mem->; rewrite inE pos_in_s orbT.
Qed.

Definition steal_strategy (st : strategy) : strategy :=
  fun s : moves => if uniq s then let: (ss, ghost) := stolen_moves s in
                                  if fullb ss then ghost else st ss
                   else fresh s (* dummy *).

Lemma steal_strategy_valid (st : strategy) :
  valid_strategy st -> valid_strategy (steal_strategy st).
Proof.
  move=> valid_st s; rewrite /steal_strategy.
  case: ifP => [|_]; last by apply: fresh_valid.
  case: s => [//|pos s uniq_pos_s not_full].
  move: (stolen_moves_perm (pos :: s)) (stolen_moves_uniq not_full uniq_pos_s).
  case: stolen_moves => ss ghost perm_ss.
  case: ifPn => [_|not_full_ss uniq_ss].
    by rewrite (perm_uniq perm_ss) => /andP[].
  move: (valid_st _ not_full_ss).
  by rewrite (perm_mem perm_ss) inE negb_or => /andP[].
Qed.

Definition oppo_stolen_strategy (st : strategy) : strategy :=
  fun s => let: (ss, ghost) := stolen_moves (play st [::] (size s))
           in if uniq s && (s == behead ss) then head ghost ss
              else fresh s (* dummy *).

Lemma oppo_stolen_strategy_valid (st : strategy) :
  valid_strategy st -> valid_strategy (oppo_stolen_strategy st).
Proof.
  move=> valid_st s not_full; rewrite /oppo_stolen_strategy.
  have /= [uniq_s|] := boolP (uniq s); last first.
    by case: stolen_moves => *; apply: fresh_valid.
  set s' := play _ _ _.
  have uniq_s': uniq s' by apply: play_uniq.
  have not_full_s' : ~~ fullb s'.
    apply: contraNN not_full => /fullb_size_leq; apply => //.
    by rewrite size_play_leqif.
  move: (stolen_moves_uniq not_full_s' uniq_s') (size_stolen_moves s').
  case: stolen_moves => ss ghost /=.
  case: ifP => [|_]; first by case: ss => //= pos _ /eqP<- /andP[].
  by rewrite fresh_valid.
Qed.

Lemma play_win_minstep (p : player) (st : strategy) k :
  win p (play st [::] k) ->
  exists k', [/\ k' <= k, win p (play st [::] k') &
              forall k'', k'' < k' -> ~~ deadend (play st [::] k'')].
Proof.
  elim: k => [|k IHk]; first by rewrite (negPf (win_nil _)).
  rewrite /=; case: ifP => [_|not_deadend win_p].
    by case/IHk=> k' [? ? ?]; exists k'; split=> //; apply: leqW.
  exists k.+1; split=> //=; first by rewrite not_deadend.
  move=> k'; rewrite ltnS => k'_le_k; move/negbT: not_deadend.
  by apply/contraNN/play_leq_deadend.
Qed.

Lemma steal_stolen_consistent (st st1 : strategy)
  (valid_st : valid_strategy st) (valid_st1 : valid_strategy st1)
  (st_steal := alternate_strategy (steal_strategy st) st1)
  (st_stolen := alternate_strategy (oppo_stolen_strategy st_steal) st) k :
  ~~ deadend (play st_stolen [::] k) ->
  (player_moves true (play st_stolen [::] k.+1)
   = player_moves false (play st_steal [::] k))
  /\ play st_stolen [::] k.+1 = (stolen_moves (play st_steal [::] k)).1.
Proof.
  elim: k => [|k IHk] not_de_stolen.
    rewrite /=; split; first by case: ifP.
    by case: ifP => // de; move: not_de_stolen; rewrite /= !de.
  have valid_st_steal: valid_strategy st_steal.
    rewrite /st_steal; apply: alternate_strategy_valid => //.
    exact: steal_strategy_valid.
  have{}/IHk[etf est]: ~~ deadend (play st_stolen [::] k).
    by apply: contraNN not_de_stolen; apply: play_leq_deadend.
  have not_de_steal: ~~ deadend (play st_steal [::] k).
    move: not_de_stolen; rewrite est !negb_or !negb_exists.
    move=> /andP[not_full /forallP-not_win].
    rewrite (contraNN (@stolen_moves_fullb _)) //=.
    apply/forallP => -[]; last first.
      by move: (not_win true); rewrite /win /= -est etf.
    move: (not_win false); rewrite /win /= -est; apply: contraNN.
    apply: winmoves_supset_closed => pos; rewrite est.
    move: (stolen_moves_perm (play st_steal [::] k)).
    rewrite {1}[stolen_moves _]surjective_pairing.
    rewrite (perm_cat_player_moves (stolen_moves (play st_steal [::] k)).1).
    rewrite perm_sym.
    rewrite (perm_cat_player_moves ((stolen_moves (play st_steal [::] k)).2
                                      :: play st_steal [::] k)).
    rewrite perm_sym perm_catC -{1}est etf /=.
    case: turn => /=.
      by rewrite perm_cat2l => /perm_mem->; rewrite inE => ->; rewrite orbT.
    rewrite perm_sym -/([:: _] ++ _ ++ _) perm_catCA perm_cat2l => /perm_mem<-.
    by rewrite inE => ->; rewrite orbT.
  have size_play_steal: size (play st_steal [::] k) = k.
    apply/eqP; rewrite size_play_leqif.
    by case: (k) not_de_steal => // k''; apply/contraNN/play_leq_deadend.
  rewrite [k.+1 in X in X.+1]lock !player_moves_play_alternate_strategyS !add0n.
  rewrite -/st_steal -/st_stolen /= -lock.
  rewrite (negPf not_de_stolen) (negPf not_de_steal) [odd k.+1]/=.
  rewrite [k.+1]lock /= [stolen_moves _]surjective_pairing.
  have play_steal_uniq : uniq (play st_steal [::] k) by rewrite play_uniq.
  case kpari: (odd k); rewrite /= -lock etf est.
    split=> //.
    have uniq_ss : uniq (stolen_moves (play st_steal [::] k)).1.
      rewrite stolen_moves_uniq //; move: not_de_steal.
      by rewrite negb_or => /andP[].
    rewrite /st_stolen /alternate_strategy /turn size_stolen_moves.
    rewrite size_play_steal /= kpari /=.
    rewrite /oppo_stolen_strategy size_stolen_moves size_play_steal /=.
    rewrite (negPf not_de_steal) /=.
    rewrite {1}[stolen_moves _]surjective_pairing /=.
    by case: ifP; rewrite uniq_ss eqxx.
  split.
    rewrite /steal_strategy [stolen_moves _]surjective_pairing /=.
    rewrite play_steal_uniq ifN // -est; move: not_de_stolen.
    by rewrite negb_or => /andP[].
  rewrite /st_stolen /alternate_strategy /turn size_stolen_moves.
  rewrite size_play_steal /= kpari /=.
  rewrite [st_steal _]/st_steal /alternate_strategy /turn.
  rewrite size_play_steal kpari /steal_strategy // play_steal_uniq.
  rewrite [stolen_moves _]surjective_pairing /=.
  have not_full_ss : ~~ fullb (stolen_moves (play st_steal [::] k)).1.
    by rewrite -est; move: not_de_stolen; rewrite negb_or => /andP[].
  rewrite (negPf not_full_ss) ifN //; apply/negP=> /eqP-st_ss.
  move: (valid_st (stolen_moves (play st_steal [::] k)).1).
  rewrite not_full_ss st_ss; case/(_ isT)/negP.
  move: (stolen_moves_perm (play st_steal [::] k)).
  rewrite [stolen_moves _]surjective_pairing => /perm_mem->.
  by rewrite inE eqxx.
Qed.

Theorem player1_no_winning_strategy :
  ~ exists st : strategy, winning_strategy true st [::].
Proof.
  case=> st [valid_st win_st].
  apply: (@winning_strategies_not_both [::]); last by exists st.
    by rewrite negb_forall; apply/existsP; exists false; rewrite win_nil.
  exists (steal_strategy st); split; first by apply: steal_strategy_valid.
  move=> st1 valid_st1.
  set st_steal : strategy := alternate_strategy _ _.
  have st_steal_valid : valid_strategy st_steal.
    by apply: alternate_strategy_valid => //; apply: steal_strategy_valid.
  case: (win_st (oppo_stolen_strategy st_steal)) => k.
    by apply: oppo_stolen_strategy_valid.
  set st_stolen : strategy := alternate_strategy _ _.
  case/play_win_minstep => -[|k' [_ {k} win_true_k' not_de_lt_k']].
    by rewrite /= (negPf (win_nil _)) => -[].
  exists k'.
  suff [play_eq _]:
    (player_moves true (play st_stolen [::] k'.+1)
     = player_moves false (play st_steal [::] k'))
    /\ play st_stolen [::] k'.+1 = (stolen_moves (play st_steal [::] k')).1.
    by move: win_true_k'; rewrite /win [k'.+1]lock /= -lock play_eq.
  by apply: steal_stolen_consistent => //; apply: not_de_lt_k'.
Qed.

(* 3. Prove that if there is a good pairing, the first player has no
      winning strategy. *)

Variable pairf : position -> position.
Hypothesis pairfK : involutive pairf.

Definition pairrel : rel position := [rel x y | (x != y) && (y == pairf x)].

Lemma pairrel_irrefl : irreflexive pairrel.
Proof. by move=> ?; rewrite /pairrel /= eqxx. Qed.

Lemma pairrel_sym : symmetric pairrel.
Proof.
  move=> p1 p2; rewrite /pairrel /= eq_sym; case: (_ != _) => //=.
  by rewrite eq_sym inv_eq.
Qed.

Hypothesis pair_good :
  forall s : moves, winmoves s ->
                    exists (p1 p2 : position),
                      [&& p1 \in s, p2 \in s & pairrel p1 p2].

Definition pair_strategy : strategy :=
  fun s : moves => if s is pos :: s' then
                     let pos' := pairf pos in
                     if (pos' != pos) && (pos' \notin s') then pos'
                     else fresh s
                   else fresh s.

Lemma pair_strategy_valid : valid_strategy pair_strategy.
Proof.
  case=> // pos s' not_full; rewrite /pair_strategy.
  case: ifP => [|_]; last by apply: fresh_valid.
  by rewrite inE negb_or.
Qed.

Theorem pair_good_player0_no_winning_strategy :
  ~ exists st : strategy, winning_strategy false st [::].
Proof.
  case=> st [st_valid /(_ _ pair_strategy_valid)[k]]; rewrite /win /=.
  set st_pair := alternate_strategy _ _.
  set play_k := play _ _ _.
  have uniq_k : uniq play_k.
    rewrite play_uniq //; apply: alternate_strategy_valid => //.
    exact: pair_strategy_valid.
  case/pair_good=> pos1 [pos2 /and3P[pos1_in pos2_in pair_pos1_pos2]].
  case/(player_movesP false): pos1_in => s1f [s1r].
  case/(player_movesP false): pos2_in => s2f [s2r].
  wlog: pos1 pos2 pair_pos1_pos2 s1f s1r s2f s2r
          / size s2f <= size s1f => [th_sym|].
    case/orP: (leq_total (size s2f) (size s1f)); first by apply: th_sym.
    by rewrite pairrel_sym in pair_pos1_pos2; move=> ? /[swap]; apply: th_sym.
  move=> size_s2f_s1f [play_k2 turn_s2r] [play_k1 turn_s1r].
  case: ltngtP size_s2f_s1f => // size_s2f_s1f _; last first.
    move: play_k1 play_k2 => -> /eqP; rewrite eqseq_cat // eqseq_cons.
    by case/andP: pair_pos1_pos2 => /negPf->; rewrite andbF.
  have [s1rf s2r_e]: exists s2rf, s2r = s2rf ++ pos1 :: s1r.
    move: play_k1 play_k2 => -> /eqP.
    rewrite -(cat_take_drop (size s2f) s1f) -catA eqseq_cat; last first.
      by rewrite size_take size_s2f_s1f.
    case E: drop => [|x s] /=.
      by move/(congr1 size): E size_s2f_s1f; rewrite size_drop -subn_gt0 => ->.
    by rewrite eqseq_cons => /and3P[_ _ /eqP<-]; exists s.
  have st_pair_pos1 : st_pair (pos1 :: s1r) = pos2.
    rewrite /st_pair /alternate_strategy /= turn_cons turn_s1r /=.
    case/andP: pair_pos1_pos2 => pos1_pos2 /eqP<-; rewrite eq_sym pos1_pos2.
    rewrite ifT //=; move: uniq_k; rewrite play_k2 s2r_e cat_uniq /=.
    by rewrite mem_cat inE; case: (pos2 \in s1r) => //; rewrite !orbT !andbF.
  case/lastP: s1rf s2r_e => [| s1rf pos2'] /= s2r_e.
    by move: turn_s1r turn_s2r; rewrite s2r_e turn_cons => ->.
  have suffix_p2'p1s1r: suffix (pos2' :: pos1 :: s1r) play_k.
    rewrite play_k2 s2r_e cat_rcons -/([:: pos2] ++ _) 2!catA.
    exact: suffix_suffix.
  have: suffix (pos1 :: s1r) play_k.
    by move: suffix_p2'p1s1r; rewrite -/([:: _] ++ _); apply: catl_suffix.
  rewrite suffix_play [size _]/= => /andP[/eqP-p1s1r _]; move: suffix_p2'p1s1r.
  rewrite suffix_play [size _]/= [X in X.+1]lock /= -lock -p1s1r => /andP[/eqP].
  case: ifP => _; first by move/(congr1 size) => /= /eqP; rewrite eqn_leq ltnn.
  rewrite st_pair_pos1 => -[] pos2'_e; move: uniq_k; rewrite play_k2 s2r_e.
  by rewrite pos2'_e cat_rcons cat_uniq /= mem_cat inE eqxx /= orbT !andbF.
Qed.

End StrongPositionalGame.

(* Concrete version: N-in-a-row game *)

From mathcomp Require Import all_algebra.

Import Num.Def Order.Theory GRing.Theory Num.Theory.

Section N_in_a_row.

(* 1. Formalize N-in-a-row game. *)

Variable n : nat.

(* Actually, (n.+1)-in-a-row game *)
Definition position : Type := int * int.
Definition winmoves (s : moves position) : bool :=
  has [pred pos : position |
        has [pred v : int * int | [forall i : 'I_n, pos + v *+ i.+1 \in s]]
          [:: (1, 0); (0, 1); (1, 1); (1,-1)]]%R s.

Lemma empty_not_winmoves : ~~ winmoves [::].
Proof. by apply/hasP => -[?]; rewrite in_nil. Qed.

Lemma winmoves_supset_closed (s s' : moves position) :
  {subset s <= s'} -> winmoves s -> winmoves s'.
Proof.
  by move=> subss' /hasP/=[pos pos_in_s]; rewrite orbF => /or4P[] /forallP;
     move/(fun top (x : 'I_n) => subss' _ (top x))/forallP => ins';
     (apply/hasP; exists pos; first by apply: subss'); rewrite /= ins' ?orbT.
Qed.

Definition fullb : moves position -> bool := xpred0.

Definition fresh : strategy position :=
  fun (s : moves position) => (1 + (\big[maxr/0]_(p <- s) p.1), 0)%R.

Lemma fresh_valid : valid_strategy fullb fresh.
Proof.
  move=> s _; apply: (contraNN (@map_f _ _ fst _ _)) => /=.
  rewrite -(big_map_id _ _ _ _ predT) /=.
  suff /=: forall x : int, (x > \big[maxr/0]_(i <- [seq i.1 | i <- s]) i)%R
                           -> x \notin [seq i.1 | i <- s].
    by move=> -> //; rewrite ltz1D lexx.
  elim: s => // p s IHs x; rewrite /= big_cons inE negb_or gt_max.
  by case: ltgtP => //= _; apply: IHs.
Qed.

Lemma fullP (s : moves position) : reflect (full s) (fullb s).
Proof. by apply: ReflectF => /(_ (fresh s)); apply/negP/fresh_valid. Qed.

(* 2. Prove that there is no winning strategy for the second player in
      N-in-a-row game. *)

Theorem N_in_a_row_player1_no_winning_strategy :
  ~ (exists st : strategy position,
        winning_strategy winmoves fullb true st [::]).
Proof.
  exact: (player1_no_winning_strategy empty_not_winmoves winmoves_supset_closed
            fullP fresh_valid).
Qed.

(* 3. Prove that if N is sufficiently large, the first player has no
      winning strategy. *)

Definition hales_jewett : seq (seq (int * int)) :=
  [:: [:: ( 1, 1);(-1, 1);( 1,-1);( 1, 0);(-1, 0);( 0, 1);( 0, 1);(-1,-1)];
      [:: ( 1,-1);(-1,-1);( 1, 1);( 1, 0);(-1, 0);( 0,-1);( 0,-1);(-1, 1)];
      [:: (-1, 0);( 0, 1);( 0, 1);(-1,-1);( 1, 1);(-1, 1);( 1,-1);( 1, 0)];
      [:: (-1, 0);( 0,-1);( 0,-1);(-1, 1);( 1,-1);(-1,-1);( 1, 1);( 1, 0)];
      [:: ( 1, 1);(-1, 1);( 1,-1);( 0, 1);( 0, 1);( 1, 0);(-1, 0);(-1,-1)];
      [:: ( 1,-1);(-1,-1);( 1, 1);( 0,-1);( 0,-1);( 1, 0);(-1, 0);(-1, 1)];
      [:: ( 0, 1);( 1, 0);(-1, 0);(-1,-1);( 1, 1);(-1, 1);( 1,-1);( 0, 1)];
      [:: ( 0,-1);( 1, 0);(-1, 0);(-1, 1);( 1,-1);(-1,-1);( 1, 1);( 0,-1)]]%R.

Definition gyorffy_et_al_1 : seq (seq (int * int)) :=
  [:: [:: ( 1, 1);( 1, 1);( 1, 1);( 1, 0);(-1, 0);(-1, 1);(-1, 1);(-1, 1)];
      [:: (-1, 0);(-1,-1);(-1,-1);(-1,-1);( 1,-1);( 1,-1);( 1,-1);( 1, 0)];
      [:: ( 0, 1);( 1, 1);(-1, 1);( 1, 0);(-1, 0);( 1, 1);(-1, 1);( 0, 1)];
      [:: ( 0,-1);( 1,-1);(-1,-1);( 1, 0);(-1, 0);( 1,-1);(-1,-1);( 0,-1)];
      [:: ( 1, 1);( 1, 1);( 1, 1);( 1, 0);(-1, 0);(-1, 1);(-1, 1);(-1, 1)];
      [:: (-1, 0);(-1,-1);(-1,-1);(-1,-1);( 1,-1);( 1,-1);( 1,-1);( 1, 0)];
      [:: (-1, 0);( 0, 1);( 0, 1);( 0, 1);( 0, 1);( 0, 1);( 0, 1);( 1, 0)];
      [:: (-1, 0);( 0,-1);( 0,-1);( 0,-1);( 0,-1);( 0,-1);( 0,-1);( 1, 0)]]%R.

Definition pair_table := hales_jewett. (* or gyorffy_et_al_1 *)

Definition pair_table_ref (pos : position) : int * int :=
  let: (x, y) := pos in
  ((nth [::] pair_table `|(y %% 8)%Z|)`_ `|(x %% 8)%Z|)%R.

Definition pairf (pos : position) : position := (pos + pair_table_ref pos)%R.

Lemma leq_abs_modS (x : int) (m : nat) : `|(x %% m.+1)%Z| <= m.
Proof. by rewrite -ltnS -ltz_nat gez0_abs ?modz_ge0 // ltz_pmod. Qed.

Lemma pair_table_opp (pos : position) :
  (pair_table_ref (pos + pair_table_ref pos) = - (pair_table_ref pos))%R.
Proof.
  case: pos => x y /=.
  by (case y_e: `|(y %% 8)%Z| => [|[|[|[|[|[|[|[|]]]]]]]];
      last by move: (leq_abs_modS y 7); rewrite y_e);
     (case x_e: `|(x %% 8)%Z| => [|[|[|[|[|[|[|[|]]]]]]]];
      last by move: (leq_abs_modS x 7); rewrite x_e);
     (rewrite /= -[((y + _) %% 8)%Z]modzDml -[((x + _) %% 8)%Z]modzDml;
      move/(congr1 Posz): y_e; rewrite gez0_abs ?modz_ge0 // => ->;
      move/(congr1 Posz): x_e; rewrite gez0_abs ?modz_ge0 // => ->).
Qed.

Lemma pair_table_nonzero (pos : position) : pair_table_ref pos != 0%R.
Proof.
  case: pos => x y /=.
  by (case y_e: `|(y %% 8)%Z| => [|[|[|[|[|[|[|[|]]]]]]]];
      last by move: (leq_abs_modS y 7); rewrite y_e);
     (case x_e: `|(x %% 8)%Z| => [|[|[|[|[|[|[|[|]]]]]]]];
      last by move: (leq_abs_modS x 7); rewrite x_e).
Qed.

Lemma pair_table_good_horizontal (y : int) :
  exists x : int, (pair_table_ref (x, y) = (1, 0))%R.
Proof.
  rewrite /pair_table_ref.
  (case y_e: `|(y %% 8)%Z| => [|[|[|[|[|[|[|[|]]]]]]]];
   last by move: (leq_abs_modS y 7); rewrite y_e);
  do [by exists 0|by exists 1|by exists 2|by exists 3
     |by exists 4|by exists 5|by exists 6|by exists 7].
Qed.

Lemma pair_table_good_vertical (x : int) :
  exists y : int, (pair_table_ref (x, y) = (0, 1))%R.
Proof.
  rewrite /pair_table_ref.
  (case x_e: `|(x %% 8)%Z| => [|[|[|[|[|[|[|[|]]]]]]]];
   last by move: (leq_abs_modS x 7); rewrite x_e);
  do [by exists 0|by exists 1|by exists 2|by exists 3
     |by exists 4|by exists 5|by exists 6|by exists 7].
Qed.

Lemma pair_table_good_diagonal (x : int) :
  exists y : int, (pair_table_ref (x + y, y) = (1, 1))%R.
Proof.
  suff [y tab_e]: exists y : int,
      (pair_table_ref (`|(x %% 8)%Z|%:Z + y, y) = (1, 1))%R.
    exists y; rewrite /pair_table_ref -modzDml; move: tab_e.
    by rewrite gez0_abs ?modz_ge0.
  (case x_e: `|(x %% 8)%Z| => [|[|[|[|[|[|[|[|]]]]]]]];
   last by move: (leq_abs_modS x 7); rewrite x_e);
  do [by exists 0|by exists 1|by exists 2|by exists 3
     |by exists 4|by exists 5|by exists 6|by exists 7].
Qed.

Lemma pair_table_good_anti_diagonal (y : int) :
  exists x : int, (pair_table_ref (x, y - x) = (1,-1))%R.
Proof.
  suff [x tab_e]: exists x : int,
      (pair_table_ref (x, `|(y %% 8)%Z|%:Z - x) = (1,-1))%R.
    exists x; rewrite /pair_table_ref -modzDml; move: tab_e.
    by rewrite gez0_abs ?modz_ge0.
  (case y_e: `|(y %% 8)%Z| => [|[|[|[|[|[|[|[|]]]]]]]];
   last by move: (leq_abs_modS y 7); rewrite y_e);
  do [by exists 0|by exists 1|by exists 2|by exists 3
     |by exists 4|by exists 5|by exists 6|by exists 7].
Qed.

Lemma pairfK : involutive pairf.
Proof. by move=> ?; rewrite /pairf pair_table_opp addrK. Qed.

Lemma pairf_irrefl (pos : position) : pairf pos != pos.
Proof. by rewrite /pairf -subr_eq0 addrC addKr pair_table_nonzero. Qed.

Lemma pair_good_horizontal (pos : position) :
  exists z : int, (pairf (pos + (1, 0) *+ `|(z %% 8)%Z|)
                   = pos + (1, 0) *+ `|(z %% 8)%Z|.+1)%R.
Proof.
  case: pos => x y; rewrite /pairf.
  have [z tab_e] := pair_table_good_horizontal y.
  exists (- x + z)%R; rewrite natz mulrSr -addrA; congr (_ + (_ + _))%R.
  rewrite pairMnE mul0rn /= addr0 !natz gez0_abs ?modz_ge0 //.
  by rewrite modzDmr addNKr.
Qed.

Lemma pair_good_vertical (pos : position) :
  exists z : int, (pairf (pos + (0, 1) *+ `|(z %% 8)%Z|)
                   = pos + (0, 1) *+ `|(z %% 8)%Z|.+1)%R.
Proof.
  case: pos => x y; rewrite /pairf.
  have [z tab_e] := pair_table_good_vertical x.
  exists (- y + z)%R; rewrite natz mulrSr -addrA; congr (_ + (_ + _))%R.
  rewrite pairMnE mul0rn /= addr0 !natz gez0_abs ?modz_ge0 //.
  by rewrite modzDmr addNKr.
Qed.

Lemma pair_good_diagonal (pos : position) :
  exists z : int, (pairf (pos + (1, 1) *+ `|(z %% 8)%Z|)
                   = pos + (1, 1) *+ `|(z %% 8)%Z|.+1)%R.
Proof.
  case: pos => x y; rewrite /pairf.
  have [z tab_e] := pair_table_good_diagonal (x - y)%R.
  exists (- y + z)%R; rewrite natz mulrSr -addrA; congr (_ + (_ + _))%R.
  rewrite pairMnE /= !natz gez0_abs ?modz_ge0 //.
  by rewrite !modzDmr addNKr addrA.
Qed.

Lemma pair_good_anti_diagonal (pos : position) :
  exists z : int, (pairf (pos + (1,-1) *+ `|(z %% 8)%Z|)
                   = pos + (1,-1) *+ `|(z %% 8)%Z|.+1)%R.
Proof.
  case: pos => x y; rewrite /pairf.
  have [z tab_e] := pair_table_good_anti_diagonal (y + x)%R.
  exists (- x + z)%R; rewrite natz mulrSr -addrA; congr (_ + (_ + _))%R.
  rewrite pairMnE mulNrn /= !natz gez0_abs ?modz_ge0 //.
  by rewrite -modzDmr modzNm opprD opprK !modzDmr addrA addNKr.
Qed.

Hypothesis n_ge8 : n >= 8.

Lemma pair_good (s : moves position) :
  winmoves s
  -> exists (p1 p2 : position),
      [&& p1 \in s, p2 \in s & pairrel pairf p1 p2].
Proof.
  rewrite /pairrel /=.
  by (case/hasP=> /= pos in_s; rewrite orbF => /or4P[] /forallP /= in_row);
     [have [z pairf_z] := pair_good_horizontal pos;
      exists (pos + (1, 0) *+ `|(z %% 8)%Z|)%R;
      exists (pairf (pos + (1, 0) *+ `|(z %% 8)%Z|)%R)
     |have [z pairf_z] := pair_good_vertical pos;
      exists (pos + (0, 1) *+ `|(z %% 8)%Z|)%R;
      exists (pairf (pos + (0, 1) *+ `|(z %% 8)%Z|)%R)
     |have [z pairf_z] := pair_good_diagonal pos;
      exists (pos + (1, 1) *+ `|(z %% 8)%Z|)%R;
      exists (pairf (pos + (1, 1) *+ `|(z %% 8)%Z|)%R)
     |have [z pairf_z] := pair_good_anti_diagonal pos;
      exists (pos + (1,-1) *+ `|(z %% 8)%Z|)%R;
      exists (pairf (pos + (1,-1) *+ `|(z %% 8)%Z|)%R)];
     (rewrite eqxx eq_sym pairf_irrefl !andbT pairf_z);
     (have z_lt_n: `|(z %% 8)%Z| < n
        by rewrite (leq_ltn_trans _ n_ge8) ?leq_abs_modS);
     move: (in_row (Ordinal z_lt_n)); rewrite /= => ->;
     (case: `|(z %% 8)%Z| z_lt_n => [|z']; first by rewrite mulr0n addr0 in_s);
     move/ltnW=> z'_lt_n; move: (in_row (Ordinal z'_lt_n)); rewrite /= => ->.
Qed.

Theorem N_in_a_row_player0_no_winning_strategy :
  ~ exists st : strategy position,
      winning_strategy winmoves fullb false st [::].
Proof.
  exact: (pair_good_player0_no_winning_strategy winmoves_supset_closed fullP
            fresh_valid pairfK pair_good).
Qed.

End N_in_a_row.
