Require Import String.
Open Scope string_scope.

Require Import EqDec.
Require Import Tactics.
Require Import Utils.
Require Import Lang.
Require Import Sequents.
Require Import Substitutions.
Require Import Derivation.
Require Import Derivability.
Require Import Deletion.
Require Import Reduction.
Require Import Displequiv.
Require Import Decidability.

Require Import Rules.
Require Import PL.
Import CPLNotations.
Require Import DecCPL.

Require Extraction.
Require Import Coq.extraction.ExtrOcamlNativeString.

Definition lem : @sequent _ _ _ _ _ _ _ CPL := I ⊢ £(?"A" ∨ ¬ ?"A").

(*
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive prod => "(*)"  [ "(,)" ].

Extraction "cpl_decidable.ml" CPL_DC'_Deriv_dec lem.
*)
