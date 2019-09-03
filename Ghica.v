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

Section Relations.

  (**
     Utilities to manipulates predicates and relations.
     Should eventually be moved somewhere else.
   *)
  Section Pred.
    
    Definition TT {A: Type}: A -> Prop := fun _ => True.
    Definition FF {A: Type}: A -> Prop := fun _ => False.

    Inductive Sum_Pred {A B: Type} (P1: A -> Prop) (P2: B -> Prop): (A + B) -> Prop :=
    | Sum_Pred_L: forall a, P1 a -> Sum_Pred P1 P2 (inl a) 
    | Sum_Pred_R: forall b, P2 b -> Sum_Pred P1 P2 (inr b).

    Inductive Inl_Pred {A B: Type} (P1: A -> Prop): (A + B) -> Prop :=
    | Inl_PredC: forall a, P1 a -> Inl_Pred P1 (inl a).

    Inductive Inr_Pred {A B: Type} (P2: B -> Prop): (A + B) -> Prop :=
    | Inr_PredC: forall b, P2 b -> Inr_Pred P2 (inr b).
  End Pred.

  Section Rel.

    Definition TT' {A: Type}: relation A := fun _ _ => True.
    Definition FF' {A: Type}: relation A := fun _ _ => False.

    Inductive Prod_Pred_to_Rel {A B: Type} (P1: A -> Prop) (P2: B -> Prop): A -> B -> Prop :=
    | Prod_PredC: forall a b, P1 a -> P2 b -> Prod_Pred_to_Rel P1 P2 a b.

    Inductive Sum_Rel {A B: Type} (R1: relation A) (R2: relation B): relation (A + B) :=
    | Sum_Rel_L: forall a a', R1 a a' -> Sum_Rel R1 R2 (inl a) (inl a')
    | Sum_Rel_R: forall b b', R2 b b' -> Sum_Rel R1 R2 (inr b) (inr b').

    Inductive Join_Rel {A: Type} (R1 R2: relation A): relation A :=
    | Join_Rel_L: forall a a', R1 a a' -> Join_Rel R1 R2 a a'
    | Join_Rel_R: forall b b', R2 b b' -> Join_Rel R1 R2 b b'.

  End Rel.

End Relations.

Infix "+'" := Sum_Pred (at level 40).
Notation "'inl_' P" := (Inl_Pred P) (at level 5).
Notation "'inr_' P" := (Inr_Pred P) (at level 5).
Infix "->'" := (Prod_Pred_to_Rel) (at level 40).
Infix "+''" := Sum_Rel (at level 40).
Infix "∪" := Join_Rel (at level 60).

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

Notation "'1'" := Unit_Arena.
Infix "⊗" := Prod_Arena (at level 29, left associativity).
Infix "↪" := Arrow_Arena (at level 11, left associativity).

(* TODO: Define the isomorphism of Arenas up to which we work.
   Prove that 1 is indeed a unit for the product and arrow. 
 *)

Section Arena_Examples.

  (* An arena representing the type of natural numbers *)
  Inductive Nat_enable: unit + nat -> unit + nat -> Prop :=
  | Nat_E: forall n, Nat_enable (inl tt) (inr n).

  Definition Nat_Arena: Arena :=
    ⟨ unit + nat,
      inl_ TT,
      inl_ TT,
      inl_ TT,
      Nat_enable
    ⟩.

End Arena_Examples.

Section Plays.

  Context {A: Arena}.

  Definition pointer: Type := M * nat.

  (* (* List of names of pointers. *)
  (*    We probably want at least a decidable equality upon it. *)
  (*  *) *)
  (* Variable N: Type. *)

  (* (* A pointer is a move carrying the name of the pointer that justifies it, as *)
  (* well as a fresh name for itself *) *)
  (* Definition pointer: Type := M * N * N. *)

  Definition pointer_sequence := list pointer.

  Inductive prefix {A: Type}: relation (list A) :=
  | Nil_Prefix: forall l, prefix [] l
  | Cons_Prefix: forall l x l', prefix l l' -> prefix (x :: l) (x :: l').
  Infix "⊑" := prefix (at level 40).

  Infix "∈" := In (at level 40).

  Inductive included {A: Type}: relation (list A) :=
  | Nil_Included: forall l, included [] l
  | Cons_Included: forall l x y l', included l l' -> included (x :: l) (y :: l')
  | Prefix_Included: forall l l', prefix l l' -> included l l'.
  Infix "⊆" := included (at level 40).

  (* TODO: think about how to implement this pointer stuff, might want to use views *)
  Inductive snoc_view {A: Type}: list A -> Type :=
  | Nil: snoc_view nil
  | Snoc: forall xs x, snoc_view (xs ++ [x]).

  Fixpoint view {X: Type} (xs: list X): snoc_view xs :=
    match xs with
    | [] => Nil
    | x :: xs =>
      match view xs with
      | Nil => Snoc [] x
      | Snoc ys y => Snoc (x::ys) y
      end
    end.

  Definition snoc {A: Type} (l: list A) a: list A := l ++ [a].

  (* Definition pointer_sequence_Wf (p: pointer_sequence): Prop := *)
  (*   forall q m a b m' a' b', snoc q (m,a,b) ⊑ p -> [(m',a',b')] ⊆ q -> b <> a' /\ b <> b'. *)

  Notation "x [[ n ]]" := (nth_error x n) (at level 12).

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
      play (snoc p (m,a)) ->
      strategy_from_next_move next (snoc p (m,a)).

  Lemma strategy_from_next_move_wf:
    forall next, next_move_wf next ->
            strategy_wf (strategy_from_next_move next).
  Admitted.

End Plays.