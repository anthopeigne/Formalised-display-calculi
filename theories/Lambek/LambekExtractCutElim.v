Require Import String.
Open Scope string_scope.

Require Import Lang.
Require Import Sequents.
Require Import Derivation.
Require Import Derivability.
Require Import Cuts.
Require Import CutElim.
Require Import Rules.
Require Import LambekLang.
Require Import LambekRules.
Import LambekRules.
Require Import LambekDC.
Import LambekNotations.

Require Import List.
Import ListNotations.

Require Extraction.
Require Import Coq.extraction.ExtrOcamlNativeString.



Definition ex_rule : rule := ([], £((%"p" ∕ %"q") ⊗ %"q") ⊢ £((%"q" ∕ %"p") \ %"q")).

#[export] Instance derr_ex_rule : DerivRule Lambek_DC ex_rule.
Proof.
  Import LambekDeriv.
  set (p := %"p"). set (q := %"q").
  confirm_derr (Der (£((p ∕ q) ⊗ q) ⊢ £((q ∕ p) \ q)) CUT
                 [Der (£((p ∕ q) ⊗ q) ⊢ £p) Fusl
                 [Der (£(p ∕ q) ;; £q ⊢ £p) Rlesmr
                 [Der (£(p ∕ q) ⊢ £p ⟨ £q) Ovel
                   [Der (£p ⊢ £p) atrefl [];
                    Der (£q ⊢ £q) atrefl []]]];
                  Der (£p ⊢ £((q ∕ p) \ q)) Undr
                   [Der (£p ⊢ £(q ∕ p) ⟩ £q) Rsmgel
                   [Der (£(q ∕ p) ;; £p ⊢ £q) Rlesmr
                   [Der (£(q ∕ p) ⊢ £q ⟨ £p) Ovel
                     [Der (£q ⊢ £q) atrefl [];
                      Der (£p ⊢ £p) atrefl []]]]]]).
Defined.

Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive prod => "(*)"  [ "(,)" ].

Extraction "Lambek_cutelim.ml" Lambek_cutElim derr_ex_rule.
