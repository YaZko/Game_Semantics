From Games Require Import
     Utils
     Games.

From Coq Require Import
     List.

Import ListNotations.

Section Cell_Game.

  (**
     A game corresponding to the interaction with a single cell of memory
     containing a [nat].
   *)

  (* Four events: the "client" requesting a read or a write, and the "server"
  answering them *)
  Inductive Cell_Event :=
  | RdC
  | WrC (_: nat)
  | WrS 
  | RdS (_: nat).

  Notation state_cell := (list Cell_Event).

  Fixpoint get_write (σ: state_cell): option nat :=
    match σ with
    | [] => None
    | WrC n :: _ => Some n
    | _ :: σ => get_write σ
    end.

  Inductive move_cell: player -> state_cell -> state_cell -> Prop :=
  | Move_RdC: forall σ, move_cell P1 σ (RdC :: σ)
  | Move_WrC: forall σ n, move_cell P1 σ (WrC n :: σ)
  | Move_RdS: forall σ n, get_write σ = Some n -> move_cell P2 (RdC :: σ) (RdS n :: RdC :: σ)
  | Move_WrS: forall σ n, move_cell P2 (WrC n :: σ) (WrS :: WrC n :: σ).

  Definition Cell_Game: Game :=
    {|
      state := list Cell_Event;
      initial_state := [];
      move := move_cell
    |}.

End Cell_Game.

