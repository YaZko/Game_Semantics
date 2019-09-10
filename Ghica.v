From Games Require Import
     Utils.

From Coq Require Import
     List
     Relations.
Import ListNotations.

(**
   We now implement "The far side of the cube" as described by Dan R. Ghica.
   It is stated as being the simplest traditional game semantics in the sense
   that very few restrictions are put on the structure. In this sense, it is
   not a very interesting domain since it is too large for definability to hold
   when taken as a model of a programming language.
   However it is a good starting point upon which enforce additional constraints
   to model various programming constructs.
   This approach is referred to as "Abramsky's Cube".
 *)

Section Arena.

  (**
     [Arena]s are the basic structure upon which games are played.
     It contains:
     - a type [M] of moves that can be taken;
     - a subset of moves [Q] that are interpreted as queries;
     - a subset of moves [O] that are assigned to the opponent;
     - a subset of moves [I] that are initial;
     - a relation of moves stating how taking a move enables new moves to become legal.
   *)

  Class Arena :=
    {
      M:> Type;
      Q: M -> Prop;
      O: M -> Prop;
      I: M -> Prop;
      enable: M -> M -> Prop
    }.

  (* The complement of [Q] are answers [A] *)
  Definition A `{Arena} := fun m => ~ Q m.
  (* The complement of [O] are player moves [P] *)
  Definition P `{Arena} := fun m => ~ O m.

  Infix "⊢" := enable (at level 50).

  (**
     Constraints are then enforced on arenas:
     - Initial moves are exclusively queries by opponent;
     - Only queries can enable new moves;
     - Plays are alternating: a move of a polarity can only enable moves of the other polarity;
     - Initial move cannot be enabled.
   *)
  Record Arena_WF `{Arena} :=
    {
      init_WF: forall m, I m -> Q m /\ O m;
      e1: forall m n, m ⊢ n -> Q m;
      e2: forall m n, m ⊢ n -> (O m <-> P n);
      e3: forall m n, m ⊢ n -> ~ I n
    }.

End Arena.

Infix "⊢" := enable (at level 50).
Notation "⟨ M , Q , O , I , R ⟩" := (Build_Arena M Q O I R). 

Inductive void: Type :=.

Section Arena_Constructs.

  (**
     We can then construct combinators over arenas.
   *)

    (* The product is a straightforward join of both arenas.
       Intuitively, both games are played in parallel without any interaction.
     *)
    Definition Prod_Arena (A1 A2: Arena): Arena :=
      ⟨
        @M A1 + @M A2,
        Q +' Q,
        O +' O,
        I +' I,
        enable +'' enable
      ⟩.

    (* The unit arena contains no move. *)
    Definition Unit_Arena: Arena :=
      ⟨
        void,
        FF,
        FF,
        FF,
        FF'
      ⟩.

    (* The arrow arena contains the union of moves.
       However, the polarity of the game to the left of the arrow is reversed.
       The game starts to the right of the arrow.
       Finally, inital moves to the right of the arrow enables the ones to the left.
     *)
    Definition Arrow_Arena (A1 A2: Arena): Arena :=
      {|
        M := @M A1 + @M A2;
        Q := Q +' Q;
        O := P +' O;
        I := inr_ (@I A2);
        enable := (@enable A1 +'' @enable A2) ∪ (inr_ I ->' inl_ I)
      |}.

End Arena_Constructs.

Notation "'Unit'" := Unit_Arena.
Infix "⊗" := Prod_Arena (at level 29, left associativity).
Infix "↪" := Arrow_Arena (at level 11, right associativity).

(* TODO: Define the isomorphism of Arenas up to which we work.
   Prove that 1 is indeed a unit for the product and arrow. 
 *)

Section Plays.

  Context {A: Arena}.

  Definition pointer: Type := M * nat.

  Definition pointer_sequence := list pointer.

  (* A play is a pointer_sequence such that the first pointer is an initial
     move, and every subsequent pointer is such that its move is indeed enabled
     by the pointed justifying move *)
  Record play (p: pointer_sequence): Prop :=
    {
      play_justifies: forall p' (m: M) (a: nat),
        snoc p' (m,a) ⊑ p -> p' <> [] ->
        exists q b, Q q /\ p'[[a]] = Some (q,b) /\ q ⊢ m;

      play_init: forall (q: M) (a: nat), [(q,a)] ⊑ p -> I q
    }.

  Definition strategy := pointer_sequence -> Prop.

  (* A strategy is a set of plays that is closed both by prefixed and by legal O-moves *)
  (* Note: traditional presentations only contain the even-lengthed ones contained here *)
  Record strategy_wf (s: strategy): Prop :=
    {
      are_plays: forall p, s p -> play p;
      prefix_closed: forall p p', s p -> p' ⊑ p -> s p';
      Oclosed: forall p m, s p -> play (snoc p m) -> O (fst m) -> s (snoc p m)
    }.

  (* Alternatively, strategies can be defined by a next move function *)
  Definition next_move := pointer_sequence -> (pointer -> Prop).

  Definition next_move_wf (s: next_move): Prop :=
    forall p m a, play p -> s p (m,a) -> play (snoc p (m,a)).

  Inductive strategy_from_next_move (next: next_move): strategy :=
  | Empty_play: strategy_from_next_move next []
  | P_move: forall p m a,
      strategy_from_next_move next p ->
      next p (m,a) ->
      strategy_from_next_move next (snoc p (m,a))
  | O_move: forall p m a,
      O m ->
      strategy_from_next_move next p ->
      play (snoc p (m,a)) ->
      strategy_from_next_move next (snoc p (m,a)).
  Hint Constructors strategy_from_next_move.

  Lemma nil_is_play: play [].
  Proof.
    split; intros.
    - inv H; exfalso; eauto.
    - inv H; exfalso; eauto.
  Qed.
  Hint Resolve nil_is_play.

  Lemma strategy_from_next_move_wf:
    forall next, next_move_wf next ->
            strategy_wf (strategy_from_next_move next).
  Proof.
    intros next nextWF; split.
    - induction p as [| [m a] p IH] using rev_ind; auto.
      intros ?.
      inv H.
      + exfalso; eauto.
      + apply nextWF; auto.
        apply snoc_inj in H0; destruct H0; subst; auto.
      + apply snoc_inj in H0; destruct H0; subst; auto.
    - intros p p' strat; revert p'; induction strat; intros p' prefix.
      + inv prefix; auto.
      + apply prefix_snoc in prefix; destruct prefix as [-> | ?]; auto.
      + apply prefix_snoc in prefix; destruct prefix as [-> | ?]; auto.
    - intros p m strat; revert m; induction strat; intros [] PLAY HO; auto.
  Qed.

  (* Least strategy spanned by a set of plays.
     TODO: think about this for a more interesting definition.
   *)
  Record least_strat (generators: pointer_sequence -> Prop) (s: strategy): Prop :=
    {
      generators_plays: forall p, generators p -> play p;
      s_strategy: strategy_wf s;
      s_least_strategy: forall s', strategy_wf s' -> generators ⊆ s' -> s ⊆ s'
    }.

  Fixpoint deletion (p: pointer_sequence): pointer_sequence :=
    match view p with
    | Nil => []
    | Snoc x p => []
    end.

End Plays.
