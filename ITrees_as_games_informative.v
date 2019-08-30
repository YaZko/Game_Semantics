From Games Require Import
     Utils
     Games.

From Coq Require Import
     List.

Import ListNotations.

Section ITrees.

  (**
     Let's work with inductive trees for now.
     
   *)

  Inductive itree (E: Type -> Type) (X: Type): Type :=
  | Ret (x: X)
  | Vis: forall {Y: Type}, E Y -> (Y -> itree E X) -> itree E X.

End ITrees.
Arguments Ret [_ _] _.
Arguments Vis [_ _ _] _ _.


Section Games_From_Interface.

  Inductive Event_E {E: Type -> Type}: Type :=
  | Req {Y} (e: E Y)
  | Ans {Y} (e: E Y) (y: Y).

  Notation "'stateE' E" := (list (@Event_E E)) (at level 10).

  Inductive move_from_E (E: Type -> Type): player -> stateE E -> stateE E -> Prop :=
  | MoveReq: forall Y (e: E Y) σ, move_from_E E P1 σ (Req e :: σ)
  | MoveAns: forall Y (e: E Y) σ y, move_from_E E P2 (Req e :: σ) (Ans e y :: Req e :: σ)
  .

  Definition Game_from_E (E: Type -> Type): Game :=
    {|
      state := stateE E;
      initial_state := [];
      move := move_from_E E
    |}.

  (* In order to interpret an itree as a strategy, we want to descend the itree
     following the trace described by the state, and use the head Vis event once
     it's done.
     However the return type of the event makes things messy.
   *)
  Fail
  Fixpoint get_next {E X} (t: itree E X) (σ: stateE E): option (@Event_E E) :=
    match σ with
    | [] =>
      match t with
      | Ret _ => None
      | Vis e _ => Some (Req e)
      end
    | Req _ :: Ans _ y :: σ =>
      match t with
      | Ret _ => None
      | Vis _ k => get_next (k y) σ
      end
    | _ => None
    end.

  Definition strategy_from_itree (E: Type -> Type) (X: Type) (t: itree E X): @strategy (Game_from_E E) P1.
  Abort.

End Games_From_Interface.