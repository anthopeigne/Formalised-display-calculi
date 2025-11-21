Require Import String.
Require Import Ensembles.
Require Import List.
Import ListNotations.
Require Import ListSetNotations.

Require Import EqDec.
Require Import Tactics.
Require Import Utils.
Require Import Lang.
Require Import Sequents.
Require Import Substitutions.
Require Import Derivation.
Require Import Cuts.
Require Import Derivability.
Require Import Rules.
Require Import LambekLang.
Require Import LambekDC.
Require Import LambekRules.
Import LambekRules.

Open Scope string_scope.
Open Scope list_scope.
Close Scope nat_scope.



(* Proof that our display calculus for Lambek calculus is Hilbert-complete *)

(* Here, we implement the "syntatic calculus" of Lambek as described in
Lambek, J. (1993). From categorial grammar to bilinear logic. Substructural logics, 2, 207-237 *)

Section BasicCalc.

  Context `{LL : LOGLANG}.

  Inductive HCsequent := HCSequent : formula -> formula -> HCsequent.
  Definition HCrule := list HCsequent * HCsequent.
  Definition HCpremsRule (r : HCrule) : list HCsequent := fst r.
  Definition HCconclRule (r : HCrule) : HCsequent := snd r.

End BasicCalc.

Notation "A ⇒ B" := (HCSequent A B) (at level 60).

Definition HILBCALC `{LL : LOGLANG} := list (@HCrule formula).

Import LambekNotations.

Definition REFL : HCrule := ([], ?"A" ⇒ ?"A").
Definition TRANS : HCrule := ([?"A" ⇒ ?"B"; ?"B" ⇒ ?"C"], ?"A" ⇒ ?"C").
Definition FIDR : HCrule := ([], ?"A" ⊗ | ⇒ ?"A").
Definition FIDL : HCrule := ([], ?"A" ⇒ | ⊗ ?"A").
Definition FIDLR : HCrule := ([], | ⊗ ?"A" ⇒ ?"A" ⊗ |).
Definition FUOV : HCrule := ([?"A" ⊗ ?"B" ⇒ ?"C"], ?"A" ⇒ ?"C" ∕ ?"B").
Definition OVUN : HCrule := ([?"A" ⇒ ?"C" ∕ ?"B"], ?"B" ⇒ ?"A" \ ?"C").
Definition UNFU : HCrule := ([?"B" ⇒ ?"A" \ ?"C"], ?"A" ⊗ ?"B" ⇒ ?"C").
Definition TOP : HCrule := ([], ?"A" ⇒ ⊤).
Definition CONL1 : HCrule := ([], ?"A" ∧ ?"B" ⇒ ?"A").
Definition CONL2 : HCrule := ([], ?"A" ∧ ?"B" ⇒ ?"B").
Definition CONR : HCrule := ([?"C" ⇒ ?"A"; ?"C" ⇒ ?"B"], ?"C" ⇒ ?"A" ∧ ?"B").
Definition EXPL : HCrule := ([], ⊥ ⇒ ?"A").
Definition DISR1 : HCrule := ([], ?"A" ⇒ ?"A" ∨ ?"B").
Definition DISR2 : HCrule := ([], ?"B" ⇒ ?"A" ∨ ?"B").
Definition DISL : HCrule := ([?"A" ⇒ ?"C"; ?"B" ⇒ ?"C"], ?"A" ∨ ?"B" ⇒ ?"C").

Definition Lambek_HC : @HILBCALC _ _ _ Lambek_log :=
  [REFL; TRANS; FIDR; FIDL; FIDLR; FUOV; OVUN; UNFU;
   TOP; CONL1; CONL2; CONR; EXPL; DISR1; DISR2; DISL].


Section HC_TO_DC.

  Definition HCtoDC_sequent (s : HCsequent) : sequent :=
    match s with A ⇒ B => FS A ⊢ FS B end.

  Definition HCtoDC_rule (r : HCrule) : rule := 
    (map HCtoDC_sequent (HCpremsRule r), HCtoDC_sequent (HCconclRule r)).

  Definition HCtoDC (HC : HILBCALC) : DISPCALC := map HCtoDC_rule HC.

End HC_TO_DC.

Definition LambekHilbComp (DC : DISPCALC) := SubDer (HCtoDC Lambek_HC) DC.

Definition Lambek_DC_r : DISPCALC := Lambek_DC ++ [refl].

Ltac set_ABC := set (A := ?"A"); set (B := ?"B"); set (C := ?"C").
Ltac prep_HCrule :=
  match goal with |- DerivRule _ (HCtoDC_rule ?r) => unfold r end;
  set_ABC; unfold HCtoDC_rule; simpl.

#[export] Instance Lambek_DC_r_REFL : DerivRule Lambek_DC_r (HCtoDC_rule REFL).
Proof.
  prep_HCrule.
  apply derr_rules. unfold Lambek_DC_r.
  apply in_or_app. right. left. reflexivity.
Defined.

#[export] Instance Lambek_DC_r_TRANS : DerivRule Lambek_DC_r (HCtoDC_rule TRANS).
Proof.
  prep_HCrule.
  confirm_derr (Der (£A ⊢ £C) CUT
                 [Unf (£A ⊢ £B);
                  Unf (£B ⊢ £C)]).
Defined.

#[export] Instance Lambek_DC_r_FIDR : DerivRule Lambek_DC_r (HCtoDC_rule FIDR).
Proof.
  prep_HCrule.
  confirm_derr (Der (£A ⊗ | ⊢ £A) Fusl
               [Der (£A ;; £| ⊢ £A) Rgesmr
               [Der (£| ⊢ £A ⟩ £A) Onel
               [Der (Φ ⊢ £A ⟩ £A) Rsmgel
               [Der (£A ;; Φ ⊢ £A) Φaddlr
               [Der (£A ⊢ £A) refl []]]]]]).
Defined.

#[export] Instance Lambek_DC_r_FIDL : DerivRule Lambek_DC_r (HCtoDC_rule FIDL).
Proof.
  prep_HCrule.
  confirm_derr (Der (£A ⊢ £(| ⊗ A)) Φdelll
               [Der (Φ ;; £A ⊢ £(| ⊗ A)) Fusr
               [Der (Φ ⊢ £|) Oner [];
                Der (£A ⊢ £A) refl []]]).
Defined.

#[export] Instance Lambek_DC_r_FIDLR : DerivRule Lambek_DC_r (HCtoDC_rule FIDLR).
Proof.
  prep_HCrule.
  confirm_derr (Der (£(| ⊗ A) ⊢ £(A ⊗ |)) Fusl
               [Der (£| ;; £A ⊢ £(A ⊗ |)) Rlesmr
               [Der (£| ⊢ £(A ⊗ |) ⟨ £A) Onel
               [Der (Φ ⊢ £(A ⊗ |) ⟨ £A) Rsmlel
               [Der (Φ ;; £A ⊢ £(A ⊗ |)) Φaddll
               [Der (£A ⊢ £(A ⊗ |)) Φdellr
               [Der (£A ;; Φ ⊢ £(A ⊗ |)) Fusr
                 [Der (£A ⊢ £A) refl [];
                  Der (Φ ⊢ £|) Oner []]]]]]]]).
Defined.

#[export] Instance Lambek_DC_r_FUOV : DerivRule Lambek_DC_r (HCtoDC_rule FUOV).
Proof.
  prep_HCrule.
  confirm_derr (Der (£A ⊢ £(C ∕ B)) Over
               [Der (£A ⊢ £C ⟨ £B) Rsmlel
               [Der (£A ;; £B ⊢ £C) CUT
                 [Der (£A ;; £B ⊢ £(A ⊗ B)) Fusr
                   [Der (£A ⊢ £A) refl [];
                    Der (£B ⊢ £B) refl []];
                  Unf (£(A ⊗ B) ⊢ £C)]]]).
Defined.

#[export] Instance Lambek_DC_r_OVUN : DerivRule Lambek_DC_r (HCtoDC_rule OVUN).
Proof.
  prep_HCrule.
  confirm_derr (Der (£B ⊢ £(A \ C)) Undr
               [Der (£B ⊢ £A ⟩ £C) Rsmgel
               [Der (£A ;; £B ⊢ £C) Rlesmr
               [Der (£A ⊢ £C ⟨ £B) CUT
                 [Unf (£A ⊢ £(C ∕ B));
                  Der (£(C ∕ B) ⊢ £C ⟨ £B) Ovel
                   [Der (£C ⊢ £C) refl [];
                    Der (£B ⊢ £B) refl []]]]]]).
Defined.

#[export] Instance Lambek_DC_r_UNFU : DerivRule Lambek_DC_r (HCtoDC_rule UNFU).
Proof.
  prep_HCrule.
  confirm_derr (Der (£(A ⊗ B) ⊢ £C) Fusl
               [Der (£A ;; £B ⊢ £C) Rgesmr
               [Der (£B ⊢ £A ⟩ £C) CUT
                 [Unf (£B ⊢ £(A \ C));
                  Der (£(A \ C) ⊢ £A ⟩ £C) Undl
                   [Der (£A ⊢ £A) refl [];
                    Der (£C ⊢ £C) refl []]]]]).
Defined.

#[export] Instance Lambek_DC_r_TOP : DerivRule Lambek_DC_r (HCtoDC_rule TOP).
Proof.
  prep_HCrule.
  confirm_derr (Der (£A ⊢ £⊤) Iwl
               [Der (I ⊢ £⊤) Topr []]).
Defined.

#[export] Instance Lambek_DC_r_CONL1 : DerivRule Lambek_DC_r (HCtoDC_rule CONL1).
Proof.
  prep_HCrule.
  confirm_derr (Der (£(A ∧ B) ⊢ £A) Conll
               [Der (£A ⊢ £A) refl []]).
Defined.

#[export] Instance Lambek_DC_r_CONL2 : DerivRule Lambek_DC_r (HCtoDC_rule CONL2).
Proof.
  prep_HCrule.
  confirm_derr (Der (£(A ∧ B) ⊢ £B) Conlr
               [Der (£B ⊢ £B) refl []]).
Defined.

#[export] Instance Lambek_DC_r_CONR : DerivRule Lambek_DC_r (HCtoDC_rule CONR).
Proof.
  prep_HCrule.
  confirm_derr (Der (£C ⊢ £(A ∧ B)) Conr
                 [Unf (£C ⊢ £A);
                  Unf (£C ⊢ £B)]).
Defined.

#[export] Instance Lambek_DC_r_EXPL : DerivRule Lambek_DC_r (HCtoDC_rule EXPL).
Proof.
  prep_HCrule.
  confirm_derr (Der (£⊥ ⊢ £A) Iwr
               [Der (£⊥ ⊢ I) Botl []]).
Defined.

#[export] Instance Lambek_DC_r_DISR1 : DerivRule Lambek_DC_r (HCtoDC_rule DISR1).
Proof.
  prep_HCrule.
  confirm_derr (Der (£A ⊢ £(A ∨ B)) Disrl
               [Der (£A ⊢ £A) refl []]).
Defined.

#[export] Instance Lambek_DC_r_DISR2 : DerivRule Lambek_DC_r (HCtoDC_rule DISR2).
Proof.
  prep_HCrule.
  confirm_derr (Der (£B ⊢ £(A ∨ B)) Disrr
               [Der (£B ⊢ £B) refl []]).
Defined.

#[export] Instance Lambek_DC_r_DISL : DerivRule Lambek_DC_r (HCtoDC_rule DISL).
Proof.
  prep_HCrule.
  confirm_derr (Der (£(A ∨ B) ⊢ £C) Disl
                 [Unf (£A ⊢ £C);
                  Unf (£B ⊢ £C)]).
Defined.

(* Lambek_DC_r is Hilbert-complete *)
Theorem Hilbert_complete_Lambek_DC_r : SubDer (HCtoDC Lambek_HC) Lambek_DC_r.
Proof.
  apply DerivDC_SubDer. intros r Hr.
  unfold HCtoDC, Lambek_HC, map in Hr.
  dest_in_list_eqdec rule_eq_dec Hr; rewrite Heq; try apply (alr_DerivRule _ _).
Defined.
