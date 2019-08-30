From Games Require Import
     Utils
     Games.

From Coq Require Import
     List.

Import ListNotations.

Section ITrees.

  (**
     Let's work with inductive trees for now.
     We also do not consider a return type of events for now,
     see _ITrees_as_games_informative_
   *)

  Inductive itree (E: Type) (X: Type): Type :=
  | Ret (x: X)
  | Vis: E -> itree E X -> itree E X.

End ITrees.
Arguments Ret [_ _] _.
Arguments Vis [_ _] _ _.

Section Games_From_Interface.

  Inductive Event_E {E: Type}: Type :=
  | Req (e: E)
  | Ans (e: E).

  Notation "'stateE' E" := (list (@Event_E E)) (at level 10).

  Inductive move_from_E (E: Type): player -> stateE E -> stateE E -> Prop :=
  | MoveReq: forall (e: E) σ, move_from_E E P1 σ (Req e :: σ)
  | MoveAns: forall (e: E) σ, move_from_E E P2 (Req e :: σ) (Ans e :: Req e :: σ)
  .

  Definition Game_from_E (E: Type): Game :=
    {|
      state := stateE E;
      initial_state := [];
      move := move_from_E E
    |}.

  Fixpoint get_next {E X} (t: itree E X) (σ: stateE E): option (@Event_E E) :=
    match σ with
    | [] =>
      match t with
      | Ret _ => None
      | Vis e _ => Some (Req e)
      end
    | Req _ :: Ans _ :: σ =>
      match t with
      | Ret _ => None
      | Vis _ k => get_next k σ
      end
    | _ => None
    end.

  Definition strategy_from_itree (E: Type) (X: Type) (t: itree E X): @strategy (Game_from_E E) P1 :=
    fun σ => match get_next t σ with
          | Some e => Some (e :: σ)
          | None => None
          end.

End Games_From_Interface.