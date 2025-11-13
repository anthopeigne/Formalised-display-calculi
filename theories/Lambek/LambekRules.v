Require Import String.
Open Scope string_scope.
Require Import Ensembles.
Require Import List.
Import ListNotations.

Require Import Tactics.
Require Import Utils.
Require Import Lang.
Require Import Sequents.
Require Import LambekLang.
Import LambekNotations.

Module LambekRules.

  (* Logical rules *)

  (* Extensional connectives *)
  Definition Topl  : rule := ([I ⊢ $"X"],
                               £⊤ ⊢ $"X").

  Definition Topr  : rule := ([],
                              I ⊢ £⊤).

  Definition Botl  : rule := ([],
                              £⊥ ⊢ I). 
  
  Definition Botr  : rule := ([$"X" ⊢ I],
                               $"X" ⊢ £⊥).

  Definition Conll : rule := ([£?"A" ⊢ $"X"],
                               £(?"A" ∧ ?"B") ⊢ $"X").

  Definition Conlr : rule := ([£?"B" ⊢ $"X"],
                               £(?"A" ∧ ?"B") ⊢ $"X").

  Definition Conr  : rule := ([$"X" ⊢ £?"A"   ;   $"X" ⊢ £?"B"],
                               $"X" ⊢ £(?"A" ∧ ?"B")).

  Definition Disl  : rule := ([£?"A" ⊢ $"X"   ;   £?"B" ⊢ $"X"],
                               £(?"A" ∨ ?"B") ⊢ $"X").

  Definition Disrl : rule := ([$"X" ⊢ £?"A"],
                               $"X" ⊢ £(?"A" ∨ ?"B")).

  Definition Disrr  : rule := ([$"X" ⊢ £?"B"],
                               $"X" ⊢ £(?"A" ∨ ?"B")).

  (* Intensional connectives *)
  Definition Onel  : rule := ([Φ ⊢ $"X"],
                               £| ⊢ $"X").

  Definition Oner  : rule := ([],
                              Φ ⊢ £|).

  Definition Zerl  : rule := ([],
                              £○ ⊢ Φ). 
  
  Definition Zerr  : rule := ([$"X" ⊢ Φ],
                               $"X" ⊢ £○).

  Definition Fusl  : rule := ([£?"A" ;; £?"B" ⊢ $"X"],
                               £(?"A" ⊗ ?"B") ⊢ $"X").

  Definition Fusr  : rule := ([$"X" ⊢ £?"A"   ;   $"Y" ⊢ £?"B"],
                               $"X" ;; $"Y" ⊢ £(?"A" ⊗ ?"B")).
(*
  Definition Disl  : rule := ([£?"A" ⊢ $"X"   ;   £?"B" ⊢ $"Y"],
                               £(?"A" ∨ ?"B") ⊢ $"X",, $"Y").

  Definition Disr  : rule := ([$"X" ⊢ £?"A",, £?"B"],
                               $"X" ⊢ £(?"A" ∨ ?"B")).
*)

  Definition Undl  : rule := ([$"X" ⊢ £?"A"   ;   £?"B" ⊢ $"Y"],
                               £(?"A" \ ?"B") ⊢ $"X" ⟩ $"Y").

  Definition Undr  : rule := ([$"X" ⊢ £?"A" ⟩ £?"B"],
                               $"X" ⊢ £(?"A" \ ?"B")).

  Definition Ovel  : rule := ([£?"A" ⊢ $"X"   ;   $"Y" ⊢ £?"B"],
                               £(?"A" ∕ ?"B") ⊢ $"X" ⟨ $"Y").

  Definition Over  : rule := ([$"X" ⊢ £?"A" ⟨ £?"B"],
                               $"X" ⊢ £(?"A" ∕ ?"B")).


  (* Structural rules *)

  Definition Iwl   : rule := ([I ⊢ $"Y"],
                               $"X" ⊢ $"Y").

  Definition Iwr   : rule := ([$"X" ⊢ I],
                               $"X" ⊢ $"Y").

  Definition Φaddll : rule := ([$"X" ⊢ $"Y"],
                                Φ ;; $"X" ⊢ $"Y").

  Definition Φaddlr : rule := ([$"X" ⊢ $"Y"],
                                $"X" ;; Φ ⊢ $"Y").

  Definition Φaddrl : rule := ([$"X" ⊢ $"Y"],
                                $"X" ⊢ Φ ;; $"Y").

  Definition Φaddrr : rule := ([$"X" ⊢ $"Y"],
                                $"X" ⊢ $"Y" ;; Φ).

  Definition Φdelll : rule := ([Φ ;; $"X" ⊢ $"Y"],
                                $"X" ⊢ $"Y").

  Definition Φdellr : rule := ([$"X" ;; Φ ⊢ $"Y"],
                                $"X" ⊢ $"Y").

  Definition Φdelrl : rule := ([$"X" ⊢ Φ ;; $"Y"],
                                $"X" ⊢ $"Y").

  Definition Φdelrr : rule := ([$"X" ⊢ $"Y" ;; Φ],
                                $"X" ⊢ $"Y").


  (* Display rules *)

  Definition Rlesmr : rule := ([$"X" ⊢ $"Y" ⟨ $"Z"],
                                $"X" ;; $"Z" ⊢ $"Y").

  Definition Rsmgel : rule := ([$"X" ;; $"Y" ⊢ $"Z"],
                                $"Y" ⊢ $"X" ⟩ $"Z").

  Definition Rgesmr : rule := ([$"X" ⊢ $"Y" ⟩ $"Z"],
                                $"Y" ;; $"X" ⊢ $"Z").

  Definition Rsmlel : rule := ([$"X" ;; $"Y" ⊢ $"Z"],
                                $"X" ⊢ $"Z" ⟨ $"Y").

  Definition Rlesml : rule := ([$"X" ⟨ $"Y" ⊢ $"Z"],
                                $"X" ⊢ $"Z" ;; $"Y").

  Definition Rsmger : rule := ([$"X" ⊢ $"Y" ;; $"Z"],
                                $"Y" ⟩ $"X" ⊢ $"Z").

  Definition Rgesml : rule := ([$"X" ⟩ $"Y" ⊢ $"Z"],
                                $"Y" ⊢ $"X" ;; $"Z").

  Definition Rsmler : rule := ([$"X" ⊢ $"Y" ;; $"Z"],
                              $"X" ⟨ $"Z" ⊢ $"Y").

End LambekRules.
