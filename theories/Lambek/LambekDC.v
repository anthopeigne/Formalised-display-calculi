Require Import String.
Open Scope string_scope.
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
Require Import CutElim.
Require Import Derivability.
Require Import BelnapAid.
Require Import LambekLang.
Import LambekNotations.
Require Import Rules.
Require Import LambekRules.

Import LambekRules.

Definition Lambek_DC : DISPCALC :=
  [atrefl; CUT;
   Topl; Topr; Botl; Botr; Conll; Conlr; Conr; Disl; Disrl; Disrr;
   Onel; Oner; Zerl; Zerr; Fusl; Fusr; Undl; Undr; Ovel; Over;
   Iwl; Iwr; Φaddll; Φaddlr; Φaddrl; Φaddrr; Φdelll; Φdellr; Φdelrl; Φdelrr;
   Rlesml; Rsmlel; Rlesmr; Rsmler; Rgesml; Rsmgel; Rgesmr; Rsmger].

(* Lists of logical introduction rules of the calculus *)
Definition Lambek_RIR :=
  [atrefl; Topr; Botr; Conr; Disrl; Disrr; Oner; Zerr; Fusr; Undr; Over].
Definition Lambek_LIR :=
  [atrefl; Topl; Botl; Conll; Conlr; Disl; Onel; Zerl; Fusl; Undl; Ovel].
(* Their defining properties. *)
Lemma Lambek_RIR_ppty : forall r, r ∈ Lambek_DC -> (r ∈ Lambek_RIR <-> strIsFml (succ (conclRule r))).
Proof.
  intros r Hr. split.
  - intro HRIR. dest_in_list HRIR;
      rewrite <- HRIR; simpl; constructor.
  - intro H. dest_in_list Hr; rewrite <- Hr; auto_in;
      unfold strIsFml in H; rewrite <- Hr in H;
      rewrite (isVar_iff_isVar_cpt FS) in H;
      unfold isVar_cpt in H; simpl Var_dec in H;
      simpl in H; contradiction.
Qed.

Lemma Lambek_LIR_ppty : forall r, r ∈ Lambek_DC -> (r ∈ Lambek_LIR <-> strIsFml (antec (conclRule r))).
Proof.
  intros r Hr. split.
  - intro HLIR. dest_in_list HLIR;
      rewrite <- HLIR; simpl; constructor.
  - intro H. dest_in_list Hr; rewrite <- Hr; auto_in;
      unfold strIsFml in H; rewrite <- Hr in H;
      rewrite (isVar_iff_isVar_cpt FS) in H;
      unfold isVar_cpt in H; simpl Var_dec in H;
      simpl in H; contradiction.
Qed.

(* This is necessary for the application of the tactic prep_C8. *)
#[export] Instance Lambek_INTRO_RULES : INTRO_RULES Lambek_DC := {|
  RIR := Lambek_RIR;
  LIR := Lambek_LIR;
  RIR_ppty := Lambek_RIR_ppty;
  LIR_ppty := Lambek_LIR_ppty
|}.



Module LambekDeriv.

  Ltac set_XYZW :=
    set (X := $"X" : structr); set (Y := $"Y" : structr);
    set (Z := $"Z" : structr); set (W := $"W" : structr).

  #[export] Instance dernc_frefl :
    forall A : Lambek.formula, fmlNoFV A -> DerivRuleNC Lambek_DC (frefl A).
  Proof.
    intros A H. induction A; try (contradict H; apply isVar_not_noVar; constructor).
    all: try (apply fmlNoFV_ipse in H; try (intros; discriminate)).
    all: try (specialize (IHA (Forall_inv H))).
    all: try (specialize (IHA1 (Forall_inv H));
              specialize (IHA2 (Forall_inv (Forall_inv_tail H)))).
    all: unfold frefl.
    - set (d := Der (£% p ⊢ £% p) atrefl []). confirm_derrnc d.
    - set (d := Der (£⊤ ⊢ £⊤) Topl
               [Der (I ⊢ £⊤) Topr []]).
      confirm_derrnc d.
    - set (d := Der (£⊥ ⊢ £⊥) Botr
               [Der (£⊥ ⊢ I) Botl []]).
      confirm_derrnc d.
    - apply_DRNC_inDC Disl.
      + apply_DRNC_inDC Disrl; assumption.
      + apply_DRNC_inDC Disrr; assumption.
    - apply_DRNC_inDC Conr.
      + apply_DRNC_inDC Conll; assumption.
      + apply_DRNC_inDC Conlr; assumption.
    - set (d := Der (£| ⊢ £|) Onel
               [Der (Φ ⊢ £|) Oner []]).
      confirm_derrnc d.
    - set (d := Der (£○ ⊢ £○) Zerr
               [Der (£○ ⊢ Φ) Zerl []]).
      confirm_derrnc d.
    - apply_DRNC_inDC Fusl.
      apply_DRNC_inDC Fusr;
      assumption.
    - apply_DRNC_inDC Undr.
      apply_DRNC_inDC Undl;
      assumption.
    - apply_DRNC_inDC Over.
      apply_DRNC_inDC Ovel;
      assumption.

(*set (d := Der (£(A1 ⊗ A2) ⊢ £(A1 ⊗ A2)) Fusl
               [Der (£A1 ;; £A2 ⊢ £(A1 ⊗ A2)) Fusr
                 [Der ( *)
  Defined.

End LambekDeriv.

Module LambekBelnap.

  Import LambekDeriv.

  Theorem has_CUT : In CUT Lambek_DC.
  Proof. auto_in. Qed.

  Theorem C3_holds : C3 Lambek_DC.
  Proof. auto_C3. Qed.

  Theorem C4_holds : C4 Lambek_DC.
  Proof. auto_C4. Qed.

  Theorem C5_holds : C5 Lambek_DC.
  Proof. auto_C5. Qed.

  Theorem C8_Con_l {X Y A B} : C8_case Lambek_DC X Y
                                 [X ⊢ £A; X ⊢ £B; £A ⊢ Y]
                                 (isipsubfml (A ∧ B)).
  Proof.
    prep_C8_case.
    apply_cof_CUT A;
    assumption.
  Defined.

  Theorem C8_Con_r {X Y A B} : C8_case Lambek_DC X Y
                                 [X ⊢ £A; X ⊢ £B; £B ⊢ Y]
                                 (isipsubfml (A ∧ B)).
  Proof.
    prep_C8_case.
    apply_cof_CUT B; assumption.
  Defined.

  Theorem C8_Dis_l {X Y A B} : C8_case Lambek_DC X Y
                                       [X ⊢ £A; £A ⊢ Y; £B ⊢ Y]
                                       (isipsubfml (A ∨ B)).
  Proof.
    prep_C8_case.
    apply_cof_CUT A; assumption.
  Defined.

  Theorem C8_Dis_r {X Y A B} : C8_case Lambek_DC X Y
                                       [X ⊢ £B; £A ⊢ Y; £B ⊢ Y]
                                       (isipsubfml (A ∨ B)).
  Proof.
    prep_C8_case.
    apply_cof_CUT B; assumption.
  Defined.

  Theorem C8_Fus {X1 X2 Y A B} :
    C8_case Lambek_DC (X1 ;; X2) Y [X1 ⊢ £A; X2 ⊢ £B; £A ;; £B ⊢ Y] (isipsubfml (A ⊗ B)).
  Proof.
    prep_C8_case.
    apply_cof_inDC Rgesmr.
    apply_cof_CUT B; [assumption|].
    apply_cof_inDC Rsmgel.
    apply_cof_inDC Rlesmr.
    apply_cof_CUT A; [assumption|].
    apply_cof_inDC Rsmlel.
    assumption.
  Defined.

  Theorem C8_Und {X Y1 Y2 A B} :
    C8_case Lambek_DC X (Y1 ⟩ Y2) [X ⊢ £A ⟩ £B; Y1 ⊢ £A; £B ⊢ Y2] (isipsubfml (A \ B)).
  Proof.
    prep_C8_case.
    apply_cof_inDC Rsmgel.
    apply_cof_inDC Rlesmr.
    apply_cof_CUT A; [assumption|].
    apply_cof_inDC Rsmlel.
    apply_cof_CUT B; [|assumption].
    apply_cof_inDC Rgesmr.
    assumption.
  Defined.

  Theorem C8_Ove {X Y1 Y2 A B} :
    C8_case Lambek_DC X (Y1 ⟨ Y2) [X ⊢ £A ⟨ £B; £A ⊢ Y1; Y2 ⊢ £B] (isipsubfml (A ∕ B)).
  Proof.
    prep_C8_case.
    apply_cof_inDC Rsmlel.
    apply_cof_inDC Rgesmr.
    apply_cof_CUT B; [assumption|].
    apply_cof_inDC Rsmgel.
    apply_cof_CUT A; [|assumption].
    apply_cof_inDC Rlesmr.
    assumption.
  Defined.

  Theorem C8_holds : C8 Lambek_DC.
  Proof.
    prep_C8 Lambek_DC.
    - remember (fst (fst afsR) "p") as p. rewrite HeqipsA in *.
      exists (Der (£%p ⊢ £%p) atrefl []). split.
      try (repeat (split; try auto_in; try auto_wfr)).
      rewrite HeqX, HeqY. split; try reflexivity.
      simpl. split; [left; discriminate|constructor].
    - exists dR. rewrite HeqX, HeqY. split; [|split]; try assumption.
      apply (allDT_impl _ _ (nocut_impl_cut (isipsubfml A))).
      assumption.
    - exists dL. rewrite HeqX, HeqY. split; [|split]; try assumption.
      apply (allDT_impl _ _ (nocut_impl_cut (isipsubfml A))).
      assumption.
    - rewrite HeqX, HeqY, HeqAR. rewrite H2, H3 in *.
      apply (C8_Con_l [dL; dL0; dR]); try auto_Forall.
      simpl. rewrite H, H0, H1. reflexivity.
    - rewrite HeqX, HeqY, HeqAR. rewrite H2, H3 in *.
      apply (C8_Con_r [dL; dL0; dR]); try auto_Forall.
      simpl. rewrite H, H0, H1. reflexivity.
    - rewrite HeqX, HeqY, HeqAR. rewrite H2, H3 in *.
      apply (C8_Dis_l [dL; dR; dR0]); try auto_Forall.
      simpl. rewrite H, H0, H1. reflexivity.
    - rewrite HeqX, HeqY, HeqAR. rewrite H2, H3 in *.
      apply (C8_Dis_r [dL; dR; dR0]); try auto_Forall.
      simpl. rewrite H, H0, H1. reflexivity.
    - exists dR. rewrite HeqX, HeqY. split; [|split]; try assumption.
      apply (allDT_impl _ _ (nocut_impl_cut (isipsubfml A))).
      assumption.
    - exists dL. rewrite HeqX, HeqY. split; [|split]; try assumption.
      apply (allDT_impl _ _ (nocut_impl_cut (isipsubfml A))).
      assumption.
    - rewrite HeqX, HeqY, HeqAR. rewrite H2, H3 in *.
      apply (C8_Fus [dL; dL0; dR]); try auto_Forall.
      simpl. rewrite H, H0, H1. reflexivity.
    - rewrite HeqX, HeqY, HeqAR. rewrite H2, H3 in *.
      apply (C8_Und [dL; dR; dR0]); try auto_Forall.
      simpl. rewrite H, H0, H1. reflexivity.
    - rewrite HeqX, HeqY, HeqAR. rewrite H2, H3 in *.
      apply (C8_Ove [dL; dR; dR0]); try auto_Forall.
      simpl. rewrite H, H0, H1. reflexivity.
  Defined.

End LambekBelnap.

#[export] Instance Lambek_DCBel : BELNAP Lambek_DC := {|
  has_CUT := LambekBelnap.has_CUT;
  C3_holds := LambekBelnap.C3_holds;
  C4_holds := LambekBelnap.C4_holds;
  C5_holds := LambekBelnap.C5_holds;
  C8_holds := LambekBelnap.C8_holds; |}.

Definition Lambek_cutElim := cutElim Lambek_DC Lambek_DCBel.
