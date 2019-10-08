From Coq Require Import
     Program.Basics.

From Games Require Import
     Category
     Utils.
Import CatNotations.
Local Open Scope cat_scope.

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
    M :> Type;
    Q: M -> Prop;
    O: M -> Prop;
    I: M -> Prop;
    enable: M -> M -> Prop
  }.
Arguments M: clear implicits.
(* Definition is_true: bool -> Prop := fun b => b = true. *)
(* Coercion is_true: bool >-> Sortclass. *)

Notation A := (fun m => ~ Q m).
Notation P := (fun m => ~ O m).

Infix "⊢" := enable (at level 50).
Notation "⟨ M , Q , O , I , R ⟩" := (Build_Arena M Q O I R).

(**
     Constraints are then enforced on arenas:
     - Initial moves are exclusively queries by opponent;
     - Only queries can enable new moves;
     - Plays are alternating: a move of a polarity can only enable moves of the other polarity;
     - Initial move cannot be enabled.
 *)
Class Arena_WF `{Arena} :=
  {
    init_WF: forall m, I m -> Q m /\ O m;
    Q_entails: forall m n, m ⊢ n -> Q m;
    alternating: forall m n, m ⊢ n -> (O m <-> P n);
    non_init: forall m n, m ⊢ n -> ~ I n
  }.

Record ArenaC: Type :=
  {
    arena :> Arena;
    arena_wf: @Arena_WF arena
  }.

(* The unit arena contains no move. *)
Definition Unit_Arena: Arena :=
  ⟨void, FF, FF, FF, FF'⟩.

Program Definition Unit_ArenaC: ArenaC := {| arena := Unit_Arena |}.
Next Obligation.
split; (intros m n H || intros m H); inv H.
Qed.

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
