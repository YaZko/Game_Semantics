Require Import Utils.

From ExtLib Require Import
     Structures.Monads
     Data.Monads.OptionMonad.

Import MonadNotation.
Open Scope monad_scope.

(**
   We consider games with exactly two players 
   When relevant, we will take the convention that P1 is the first player to play.
 *)
Inductive player := P1 | P2.
Definition opp p := match p with | P1 => P2 | P2 => P1 end.

(* A game comes with a notion of state upon which we play, an initial state and
   a move relation indexed by players.
   Compared to usual approaches, this is overly general: the set of moves themselves
   is not described, nore are the order and incompatibility relations.
   The intent is to explore how traditional games can be seen as instance of this
   general framework.
 *)

Class Game :=
  {
    state:> Type;
    initial_state: state;
    move: player -> state -> state -> Prop
  }.

Section Game_Basics.

  Context `{Game}.

  (* A position is a state and the knowledge of whose turn it is to play (referred to as _active_ in the following *)
  Definition position := (player * state)%type.

  (* A position is losing for the active player if he has no available play *)
  Definition losing_position (pos: position): Prop :=
    let '(p,σ) := pos in
    ~ exists σ', move p σ σ'.

  (**
     A position is winnable by the active player if he has an available move
     that leads to a new state from which any move the opponent would make
     leads to a still winnable state.
     Spelled differently, the active player will never be stuck, eventually reaching
     a state where the opponent is stuck.
     Note that making this definition co-inductive instead of inductive would allow
     for infinite plays, stating that a diverging game is won.
   *)
  (* I am not sure this is viable: it feels like we really want to be fine with ending
     on our turn in a satisfiable position. This gets quite apparent when defining
     winning strategy for the product (see below [Prod_Game]): with the current definition,
     we cannot really play a component until it terminates, and then switch to the other.
     Unless we define losing the product as losing both sides, but it's awkward.
   *)
  Inductive winnable_position : position -> Prop :=
  | Can_Step: forall p σ,
      (exists σ', move p σ σ' /\ (forall σ'', move (opp p) σ' σ'' -> winnable_position (p,σ''))) ->
      winnable_position (p,σ).

  (**
     A strategy is a decision procedure that tells a player which move to make
     in a given state of the game.
   *)
  Definition strategy (p: player) := state -> option state. 

  (**
     For this strategy to make any sense, it has to exclusively
     suggests legal move.
   *)
  Definition valid_strategy {p: player} (s: strategy p): Prop :=
    forall σ σ', s σ = Some σ' -> move p σ σ'.

  (**
     A strategy is winning starting from a position if it can be used
     as an oracle to feed the existential from the [winnable_position] definition.
   *)
  Inductive winning_strategy_from_pos {p: player} (s: strategy p): position -> Prop :=
  | Can_Step_Win: forall σ σ'
      (EQs: s σ = Some σ')
      (Hmove: move p σ σ') (* Redundant with [valid_strategy] *)
      (HRec: forall σ'', move (opp p) σ' σ'' -> winning_strategy_from_pos s (p,σ'')),
      winning_strategy_from_pos s (p,σ).

  (* A strategy is winning if it is winning from the initial position. *)
  Definition winning_strategy {p: player} (s: strategy p): Prop := winning_strategy_from_pos s (p,initial_state).

End Game_Basics.

Section Game_Constructions.

  Section Empty_Game.

    (**
     The empty game corresponds to one that [P1] cannot win.
     The move relation is empty.
     *)
    Inductive Empty_move: player -> unit -> unit -> Prop :=.

    Definition Empty_Game: Game :=
      {|
        state := unit;
        initial_state := tt;
        move := Empty_move
      |}.
    Hint Constructors Empty_move.

    (* Of course, [Empty_Game] does not admit a winning strategy. *)
    Lemma Empty_Game_cannot_win:
      forall (s: @strategy Empty_Game P1),
        ~ winning_strategy s.
    Proof.
      intros s abs; inv abs.
      inv Hmove.
    Qed.

  End Empty_Game.

  Section Unit_Game.

    (**
     The unit game corresponds to one that [P1] trivially wins.
     There is a single move.
     *)
    Inductive Unit_move: player -> unit + unit -> unit + unit -> Prop :=
    | UnitM: Unit_move P1 (inl tt) (inr tt).

    Definition Unit_Game: Game :=
      {|
        state := unit + unit;
        initial_state := inl tt;
        move := Unit_move
      |}.
    Hint Constructors Unit_move.

    (* [Unit_Game] admits a trivial winning strategy: *)
    Definition Unit_strategy: @strategy Unit_Game P1 :=
      fun σ => match σ with | inl _ => Some (inr tt) | _ => None end.

    Lemma Unit_strategy_is_winning: winning_strategy Unit_strategy.
    Proof.
      econstructor; [reflexivity | constructor | intros ? abs; inversion abs].
    Qed.

  End Unit_Game.

  Section Sum_Game.

    Context {G1 G2: Game}.

    (**
     Given two games, we can construct the game that consist of running either computation,
     but not both.
     The domain of states is the sum of both domains, plus a marker for the new initial state.
     The set of moves is essentially the sum of both relations, except that some care must be
     taken for the first move: it is the one that decides which computation will be run.
     *)
    Inductive Sum_move:
      player -> (unit + (@state G1 + @state G2)) -> (unit + (@state G1 + @state G2)) -> Prop :=
    | Sum_Pick_Left: forall σ p,
        move p initial_state σ ->
        Sum_move p (inl tt) (inr (inl σ))
    | Sum_Pick_Right: forall σ p,
        move p initial_state σ ->
        Sum_move p (inl tt) (inr (inr σ))
    | Sum_Move_Left: forall σ σ' p,
        move p σ σ' ->
        Sum_move p (inr (inl σ)) (inr (inl σ'))
    | Sum_Move_Right: forall σ σ' p,
        move p σ σ' ->
        Sum_move p (inr (inr σ)) (inr (inr σ'))
    .
    Hint Constructors Sum_move.

    Definition Sum_Game: Game :=
      {|
        state := unit + (@state G1 + @state G2);
        initial_state := inl tt;
        move := Sum_move 
      |}.

    Definition Sum_strategy_L (p: player) (s: @strategy G1 p): @strategy Sum_Game p :=
      fun σ => match σ with
            | inl _ =>
              'σ <- s initial_state;;
              ret (inr (inl σ))
            | inr (inl σ) => 
              'σ' <- s σ;;
              ret (inr (inl σ'))
            | inr (inr _) => None
            end.

    Lemma Sum_strategy_L_is_winning_aux:
      forall p (s: @strategy G1 p) σ pos,
        winning_strategy_from_pos s pos ->
        pos = (p,σ) ->
        winning_strategy_from_pos (Sum_strategy_L p s) (p, inr (inl σ)).
    Proof.
      intros p s σ pos H.
      revert σ; induction H.
      intros ? EQ; inv EQ.
      econstructor; cbn.
      - rewrite EQs; reflexivity.
      - auto. 
      - intros σ'' MOVE.
        inv MOVE.
        eapply H; eauto.
    Qed.

    Lemma Sum_strategy_L_is_winning:
      forall p (s: @strategy G1 p),
        winning_strategy s ->
        winning_strategy (Sum_strategy_L p s). 
    Proof.
      unfold winning_strategy, initial_state at 2; cbn; intros p s WIN.
      inv WIN.
      econstructor; cbn.
      - rewrite EQs; reflexivity.
      - auto.
      - intros ? MOVE; inv MOVE.
        eapply Sum_strategy_L_is_winning_aux; [| reflexivity].
        auto.
    Qed.

    Definition Sum_strategy_R (p: player) (s: @strategy G2 p): @strategy Sum_Game p :=
      fun σ => match σ with
            | inl _ =>
              'σ <- s initial_state;;
              ret (inr (inr σ))
            | inr (inr σ) => 
              'σ' <- s σ;;
              ret (inr (inr σ'))
            | inr (inl _) => None
            end.

    Lemma Sum_strategy_R_is_winning_aux:
      forall p (s: @strategy G2 p) σ pos,
        winning_strategy_from_pos s pos ->
        pos = (p,σ) ->
        winning_strategy_from_pos (Sum_strategy_R p s) (p, inr (inr σ)).
    Proof.
      intros p s σ pos H.
      revert σ; induction H.
      intros ? EQ; inv EQ.
      econstructor; cbn.
      - rewrite EQs; reflexivity.
      - auto. 
      - intros σ'' MOVE.
        inv MOVE.
        eapply H; eauto.
    Qed.

    Lemma Sum_strategy_R_is_winning:
      forall p (s: @strategy G2 p),
        winning_strategy s ->
        winning_strategy (Sum_strategy_R p s). 
    Proof.
      unfold winning_strategy, initial_state at 2; cbn; intros p s WIN.
      inv WIN.
      econstructor; cbn.
      - rewrite EQs; reflexivity.
      - auto.
      - intros ? MOVE; inv MOVE.
        eapply Sum_strategy_R_is_winning_aux; [| reflexivity].
        auto.
    Qed.

  End Sum_Game.

  Section Prod_Game.
    
    Context {G1 G2: Game}.

    (**
     Given two games, we can construct the game that consist of running both computations
     in parallel.
     The domain of states is the product of both domains.
     Moves can be taken on either side non-deterministically.
     *)
    Inductive Prod_move:
      player -> (@state G1 * @state G2) -> (@state G1 * @state G2) -> Prop :=
    | Prod_Move_Left: forall σl σl' σr p,
        move p σl σl' ->
        Prod_move p (σl,σr) (σl',σr)
    | Prod_Move_Right: forall σl σr σr' p,
        move p σr σr' ->
        Prod_move p (σl,σr) (σl,σr')
    .

    Definition Prod_Game: Game :=
      {|
        state := (@state G1 * @state G2);
        initial_state := (initial_state, initial_state);
        move := Prod_move 
      |}.

    Definition Prod_strategy (p: player) (s1: @strategy G1 p) (s2: @strategy G2 p): @strategy Prod_Game p :=
      fun σ => let '(σ1,σ2) := σ in
            match s1 σ1 with
            | None => 'σ2' <- s2 σ2;;
                     ret (σ1,σ2')    
            | Some σ1' => ret (σ1',σ2)
            end.

    (* A bit annoying to prove *)
    Lemma Prod_strategy_is_winning_aux:
      forall p (s1: @strategy G1 p) (s2: @strategy G2 p) σ1 σ2 pos1 pos2,
        winning_strategy_from_pos s1 pos1 ->
        pos1 = (p,σ1) ->
        winning_strategy_from_pos s2 pos2 ->
        pos2 = (p,σ2) ->
        winning_strategy_from_pos (Prod_strategy p s1 s2) (p,(σ1,σ2)).
    Proof.
      intros p s1 s2 σ1 σ2 pos1 pos2 WIN1 EQ1 WIN2 EQ2.
      revert σ1 EQ1; induction WIN1.
      intros σ1 EQ1; inv EQ1.
      (* remember (p,σ2) as pos2. revert σ2 Heqpos2. induction WIN2. *)

      econstructor; cbn.
      - rewrite EQs; reflexivity.
      - apply Prod_Move_Left; auto.
      - intros ? MOVE; inv MOVE.
        + eapply H; eauto.
        + (* Here this case should be impossible since it should not be opponent's turn to play in game 2 *)
          (* How to express it? *)
    Abort.

  End Prod_Game.

  Section Dual_Game.

    Context {G: Game}.

    Inductive Dual_move: player -> state -> state -> Prop :=
    | Dual_Move: forall p σ1 σ2,
        move p σ1 σ2 -> Dual_move (opp p) σ1 σ2.
    Hint Constructors Dual_move.

    Definition Dual_Game: Game :=
      {|
        state := state;
        initial_state := initial_state;
        move := Dual_move
      |}.
    
    Definition Dual_strategy {p: player} (s: strategy p): @strategy Dual_Game (opp p) := s.

    Lemma opp_involutive:
      forall p, opp (opp p) = p.
      intros []; auto.
    Qed.

    Lemma Dual_strategy_is_winning_aux:
      forall p (s: strategy p) σ pos,
        winning_strategy_from_pos s pos ->
        pos = (p,σ) ->
        winning_strategy_from_pos (Dual_strategy s) (opp p,σ).
    Proof.
      intros p s σ pos WIN; revert σ; induction WIN; intros ? EQ; inv EQ.
      eapply (@Can_Step_Win Dual_Game (opp p)).
      - unfold Dual_strategy; eauto.
      - cbn; constructor; auto.
      - rewrite opp_involutive; cbn; intros ? MOVE; inv MOVE.
        eapply H; eauto.
        rewrite opp_involutive; auto.
    Qed.

    Lemma Dual_strategy_is_winning:
      forall p (s: strategy p), 
        winning_strategy s ->
        winning_strategy (Dual_strategy s).
    Proof.
      unfold winning_strategy; intros; eapply Dual_strategy_is_winning_aux; eauto.
    Qed.

  End Dual_Game.

  Section Arrow_Game.

    (**
       The [Arrow_Game] models a function type.
       It should be a dialogue between the return Game that
       requests an input, the input Game that runs to provide one
       such, and finally the return Game that answers the resulting value.
       A recurrent way to define it is to see it as a cartesian product but
       whose left-hand-side is dualized: in A -> B, we are challenged to provide B,
       but we can assume A for free.
     *)

    Definition Arrow_Game (G1 G2: Game): Game := @Prod_Game (@Dual_Game G1) G2.

    (* Definition copycat G1: @strategy (Arrow_Game G1 G1) P1 := *)

  End Arrow_Game.

End Game_Constructions.

Infix "⊕" := Sum_Game (at level 30).
Infix "⊗" := Prod_Game (at level 20).
Infix "↪" := Arrow_Game (at level 50).



