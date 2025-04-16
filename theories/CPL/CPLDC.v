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
Require Import PL.
Import CPLNotations.
Require Import Rules.
Require Import CPLRules.

Import CPLRules.
Open Scope list_scope.

Definition CPL_DC : DISPCALC :=
  [atrefl; Iwr; Iaddl; Idell; Iwl; Comml; Contl; Assol; CUT;
   Topl; Topr; Botl; Botr; Negl; Negr; Conl; Conr; Disl; Disr; Impl; Impr;
   Mlrn; Mrrslln; Mrls; Snn; Sns; DSEr; Mrrn; Mlrsrln; Mlls].



Definition DE : DISPCALC :=
  [Mlrn; Mrrslln; Mrls; Snn; Sns; DSEr; Mrrn; Mlrsrln; Mlls; Comml; Assol].

Definition MDE : DISPCALC :=
  [Mlln; Mlls; Mlrn; Mlrs; Mrln; Mrls; Mrrn; Mrrs; Snn; Sns; Ssn; Sss; DSEl; DSEr;
   DSIl; DSIr; Comml; Commr; Assol; Assolinv].

Definition ICW : DISPCALC :=
  [Iaddl; Idell; Iaddr; Idelr; Wkl; Wkr; Contl; ContWkls; ContWkln].

Definition MDEICW : DISPCALC := MDE ++ ICW.

Definition CPL_DC' : @DISPCALC _ _ _ _ _ _ _ CPL_LANG :=
  MDEICW ++ [atrefl; Topr; Botl; Negl; Negr; Conl; Consr; Dissl; Disr; Impsl; Impr].



Module CPLDeriv.

  Ltac set_XYZW :=
    set (X := $"X" : structr); set (Y := $"Y" : structr);
    set (Z := $"Z" : structr); set (W := $"W" : structr).
  
  Ltac set_ABC :=
    set (A := ?"A" : PL.formula); set (B := ?"B" : PL.formula);
    set (C := ?"C" : PL.formula).

  #[export] Instance dernc_Sss : DerivRuleNC CPL_DC Sss.
  Proof.
    unfold Sss.
    apply_DRNC_inDC DSEr.
    apply_DRNC_inDC Sns.
    apply DerivRuleNC_refl.
  Defined.

  #[export] Instance dernc_DSEl : DerivRuleNC CPL_DC DSEl.
  Proof.
    set_XYZW.
    apply (Extend_DerivRuleNC _ Sss).
    set (d := Der (X ⊢ Y) Sss
             [Der (∗Y ⊢ ∗X) DSEr
             [Der (∗Y ⊢ ∗∗∗X) Snn
             [Unf ((∗∗X) ⊢ Y)]]]).
    confirm_derrnc d.
  Defined.

  #[export] Instance dernc_Ssn : DerivRuleNC CPL_DC Ssn.
  Proof.
    set (d := Der (∗ $"Y" ⊢ $"X") DSEr
             [Der (∗ $"Y" ⊢ ∗ ∗ $"X") Snn
             [Unf (∗ $"X" ⊢ $"Y")]]).
    confirm_derrnc d.
  Defined.

  #[export] Instance dernc_Sns : DerivRuleNC CPL_DC Sns.
  Proof.
    set_XYZW.
    apply (Extend_DerivRuleNC _ DSEl).
    set (d := Der (Y ⊢ ∗ X) DSEl
             [Der ((∗∗Y) ⊢ ∗X) Snn
             [Unf (X ⊢ ∗Y)]]).
    confirm_derrnc d.
  Defined.

  #[export] Instance dernc_Mrrs : DerivRuleNC CPL_DC Mrrs.
  Proof.
    set_XYZW.
    set (d := Der (X,, Z ⊢ Y) Mrls [Der (Z ⊢ ∗X,, Y) Mrrslln [Unf (X ⊢ Y,, ∗Z)] ]).
    confirm_derrnc d.
  Defined.

  #[export] Instance dernc_Commr : DerivRuleNC CPL_DC Commr.
  Proof.
    set_XYZW.
    set (d := Der (X ⊢ Z,, Y) Mlls
             [Der (∗Z,, X ⊢ Y) Comml
             [Der (X,, ∗Z ⊢ Y) Mrrn
             [Unf (X ⊢ Y,, Z)]]]).
    confirm_derrnc d.
  Defined.

  #[export] Instance dernc_Mlln : DerivRuleNC CPL_DC Mlln.
  Proof.
    set_XYZW.
    apply (Extend_DerivRuleNC _ Commr).
    set (d := Der (Y ⊢ ∗X,, Z) Commr
             [Der (Y ⊢ Z,, ∗X) Mlrn
             [Der (Y,, X ⊢ Z) Comml
             [Unf (X,, Y ⊢ Z)]]]).
    confirm_derrnc d.
  Defined.

  #[export] Instance dernc_Assolinv : DerivRuleNC CPL_DC Assolinv.
  Proof.
    unfold Assolinv. set_XYZW.
    apply_DRNC_inDC Comml.
    apply_DRNC_inst Mrrs.
    apply_DRNC_inDC Comml.
    apply_DRNC_inDC Mlrn.
    apply_DRNC_inDC Assol.
    apply_DRNC_inDC Comml.
    apply_DRNC_inst Mrrs.
    apply_DRNC_inDC Comml.
    apply_DRNC_inDC Mlrn.
    apply DerivRuleNC_refl.
  Defined.

  #[export] Instance dernc_Mlrs : DerivRuleNC CPL_DC Mlrs.
  Proof.
    unfold Mlrs. set_XYZW.
    apply (Extend_DerivRuleNC _ Commr).
    confirm_derrnc (Der (X ⊢ Z,, Y) Commr
                   [Der (X ⊢ Y,, Z) Mlls
                   [Der (∗Y,, X ⊢ Z) Comml
                   [Unf (X,, ∗Y ⊢ Z)]]]).
  Defined.

  #[export] Instance dernc_Mrln : DerivRuleNC CPL_DC Mrln.
  Proof.
    unfold Mrln. set_XYZW.
    apply (Extend_DerivRuleNC _ Commr).
    confirm_derrnc (Der (∗Y,, X ⊢ Z) Comml
                   [Der (X,, ∗Y ⊢ Z) Mrrn
                   [Der (X ⊢ Z,, Y) Commr
                   [Unf (X ⊢ Y,, Z)]]]).
  Defined.

  #[export] Instance dernc_DSIl : DerivRuleNC CPL_DC DSIl.
  Proof.
    unfold DSIl. set_XYZW.
    confirm_derrnc (Der (∗(∗X) ⊢ Y) DSEr
                   [Der (∗(∗X) ⊢ ∗∗Y) Snn
                   [Der (∗Y ⊢ ∗X) Snn
                   [Unf (X ⊢ Y)]]]).
  Defined.

  #[export] Instance dernc_DSIr : DerivRuleNC CPL_DC DSIr.
  Proof.
    unfold DSIr. set_XYZW.
    apply (Extend_DerivRuleNC _ DSEl).
    confirm_derrnc (Der (X ⊢ ∗∗Y) DSEl
                   [Der (∗(∗X) ⊢ ∗∗Y) Snn
                   [Der (∗Y ⊢ ∗X) Snn
                   [Unf (X ⊢ Y)]]]).
  Defined.

  Lemma derr_struct_rules : DerivDCNC CPL_DC [Mrrs; Mlln; Mlrs; Mrln; Commr].
  Proof.
    intros r Hr. dec_destruct_List_In rule_eq_dec r;
      rewrite Heq; apply (alr_DerivRuleNC _ _).
  Defined.

  #[export] Instance dernc_Iaddr : DerivRuleNC CPL_DC Iaddr.
  Proof.
    unfold Iaddr. set_XYZW.
    apply (Extend_DerivDCNC _ _ derr_struct_rules).
    confirm_derrnc (Der (X ⊢ I,, Y) Commr
                   [Der (X ⊢ Y,, I) Mlrs
                   [Der (X,, ∗I ⊢ Y) Mrls
                   [Der (∗I ⊢ ∗X,, Y) Iwl
                   [Der (I ⊢ ∗X,, Y) Mlln
                   [Der (X,, I ⊢ Y) Iaddl
                   [Unf (X ⊢ Y)]]]]]]).
  Defined.

  #[export] Instance dernc_Idelr : DerivRuleNC CPL_DC Idelr.
  Proof.
    unfold Idelr. set_XYZW.
    apply (Extend_DerivDCNC _ _ derr_struct_rules).
    confirm_derrnc (Der (X ⊢ Y) Idell
                   [Der (X,, I ⊢ Y) Mrrs
                   [Der (X ⊢ Y,, ∗I) Mlls
                   [Der (∗Y,, X ⊢ ∗I) Iwr
                   [Der (∗Y,, X ⊢ I) Mrln
                   [Der (X ⊢ Y,, I) Commr
                   [Unf (X ⊢ I,, Y)]]]]]]).
  Defined.

  #[export] Instance dernc_Wkl : DerivRuleNC CPL_DC Wkl.
  Proof.
    set_XYZW.
    apply (Extend_DerivRuleNC _ Mlln).
    confirm_derrnc (Der (Z,, X ⊢ Y) Comml
                   [Der (X,, Z ⊢ Y) Mrls
                   [Der (Z ⊢ ∗X,, Y) Iwl
                   [Der (I ⊢ ∗X,, Y) Mlln
                   [Der (X,, I ⊢ Y) Iaddl
                   [Unf (X ⊢ Y)]]]]]).
  Defined.

  #[export] Instance dernc_Wkr : DerivRuleNC CPL_DC Wkr.
  Proof.
    unfold Wkr. set_XYZW.
    apply (Extend_DerivDCNC _ _ derr_struct_rules).
    confirm_derrnc (Der (X ⊢ Y,, Z) Mlrs
                   [Der (X,, ∗Z ⊢ Y) Mrls
                   [Der (∗Z ⊢ ∗X,, Y) Iwl
                   [Der (I ⊢ ∗X,, Y) Mlln
                   [Der (X,, I ⊢ Y) Iaddl
                   [Unf (X ⊢ Y)]]]]]).
  Defined.

  #[export] Instance dernc_ContWkls : DerivRuleNC CPL_DC ContWkls.
  Proof.
    unfold ContWkls. set_XYZW.
    apply (Extend_DerivDCNC _ [Wkr; Sss; Mrln]).
    intros r Hr; dec_destruct_List_In rule_eq_dec r;
      rewrite Heq; apply (alr_DerivRuleNC _ _).
    confirm_derrnc (Der (Y ⊢ X) Sss
                   [Der (∗X ⊢ ∗Y) Contl
                   [Der (∗X,, ∗X ⊢ ∗Y) Mrln
                   [Der (∗X ⊢ X,, ∗Y) Wkr
                   [Unf (∗X ⊢ X)]]]]).
  Defined.

  #[export] Instance dernc_ContWkln : DerivRuleNC CPL_DC ContWkln.
  Proof.
    unfold ContWkln. set_XYZW.
    apply (Extend_DerivRuleNC _ Wkr).
    confirm_derrnc (Der (Y ⊢ ∗X) Sns
                   [Der (X ⊢ ∗Y) Contl
                   [Der (X,, X ⊢ ∗Y) Mrls
                   [Der (X ⊢ ∗X,, ∗Y) Wkr
                   [Unf (X ⊢ ∗X)]]]]).
  Defined.

  #[export] Instance dernc_Contr : DerivRuleNC CPL_DC Contr.
  Proof.
    unfold Contr. set_XYZW.
    apply (Extend_DerivDCNC _ [Sss; Mlln]).
    intros r Hr; dec_destruct_List_In rule_eq_dec r;
      rewrite Heq; apply (alr_DerivRuleNC _ _).
    confirm_derrnc (Der (X ⊢ Y) Sss
                   [Der (∗Y ⊢ ∗X) Contl
                   [Der (∗Y,, ∗Y ⊢ ∗X) Mrrn
                   [Der (∗Y ⊢ ∗X,, Y) Mlln
                   [Der (X,, ∗Y ⊢ Y) Mrrn
                   [Unf (X ⊢ Y,, Y)]]]]]).
  Defined.

  #[export] Instance dernc_Consr : DerivRuleNC CPL_DC Consr.
  Proof.
    unfold Consr. set_XYZW. set_ABC.
    confirm_derrnc (Der (X ⊢ £ A ∧ B) Contl
                   [Der (X,, X ⊢ £ A ∧ B) Conr
                   [Unf (X ⊢ £A);
                    Unf (X ⊢ £B)]]).
  Defined.

  #[export] Instance dernc_Dissl : DerivRuleNC CPL_DC Dissl.
  Proof.
    unfold Dissl. set_XYZW. set_ABC.
    apply (Extend_DerivRuleNC _ Contr).
    confirm_derrnc (Der (£ A ∨ B ⊢ X) Contr
                   [Der (£ A ∨ B ⊢ X,, X) Disl
                   [Unf (£A ⊢ X);
                    Unf (£B ⊢ X)]]).
  Defined.

  #[export] Instance dernc_Impsl : DerivRuleNC CPL_DC Impsl.
  Proof.
    unfold Impsl. set_XYZW. set_ABC.
    apply (Extend_DerivDCNC _ [Contr; Mlrs; Ssn]).
    intros r Hr; dec_destruct_List_In rule_eq_dec r;
      rewrite Heq; apply (alr_DerivRuleNC _ _).
    confirm_derrnc (Der (£ A → B ⊢ X) Contr
                   [Der (£ A → B ⊢ X,, X) Mlrs
                   [Der (£ A → B,, ∗X ⊢ X) DSEr
                   [Der (£ A → B,, ∗X ⊢ ∗∗X) Mrrn
                   [Der (£ A → B ⊢ ∗(∗X),, X) Impl
                   [Der (∗X ⊢ £A) Ssn
                     [Unf (∗£A ⊢ X)];
                    Unf (£B ⊢ X)]]]]]).
  Defined.


(* CPL_DC' *)

  #[export] Instance derr_Iwr : DerivRule CPL_DC' Iwr.
  Proof.
    unfold Iwr. set_XYZW.
    confirm_derr (Der (X ⊢ Y) Idelr
                 [Der (X ⊢ I,, Y) Wkr
                 [Unf (X ⊢ I)]]).
  Defined.

  #[export] Instance derr_Iwl : DerivRule CPL_DC' Iwl.
  Proof.
    unfold Iwl. set_XYZW.
    confirm_derr (Der (X ⊢ Y) Idell
                 [Der (X,, I ⊢ Y) Wkl
                 [Unf (I ⊢ Y)]]).
  Defined.

  #[export] Instance derr_Topl : DerivRule CPL_DC' Topl.
  Proof.
    unfold Topl. set_XYZW.
    apply (Extend_DerivRule _ Iwl).
    confirm_derr (Der (£⊤ ⊢ X) Iwl [Unf (I ⊢ X)]).
  Defined.

  #[export] Instance derr_Botr : DerivRule CPL_DC' Botr.
  Proof.
    unfold Botr. set_XYZW.
    apply (Extend_DerivRule _ Iwr).
    confirm_derr (Der (X ⊢ £⊥) Iwr [Unf (X ⊢ I)]).
  Defined.

  #[export] Instance derr_Conr : DerivRule CPL_DC' Conr.
  Proof.
    unfold Conr. set_XYZW. set_ABC.
    confirm_derr (Der (X,, Y ⊢ £ A ∧ B) Consr
                 [Der (X,, Y ⊢ £A) Comml
                   [Der (Y,, X ⊢ £A) Wkl
                   [Unf (X ⊢ £A)]];
                  Der (X,, Y ⊢ £B) Wkl
                   [Unf (Y ⊢ £B)]]).
  Defined.

  #[export] Instance derr_Disl : DerivRule CPL_DC' Disl.
  Proof.
    unfold Disl. set_XYZW. set_ABC.
    confirm_derr (Der (£ A ∨ B ⊢ X,, Y) Dissl
                 [Der (£A ⊢ X,, Y) Wkr
                   [Unf (£A ⊢ X)];
                  Der (£B ⊢ X,, Y) Commr
                   [Der (£B ⊢ Y,, X) Wkr
                   [Unf (£B ⊢ Y)]]]).
  Defined.

  #[export] Instance derr_Impl : DerivRule CPL_DC' Impl.
  Proof.
    unfold Impl. set_XYZW. set_ABC.
    confirm_derr (Der (£ A → B ⊢ ∗X,, Y) Impsl
                 [Der (∗£A ⊢ ∗X,, Y) Wkr
                   [Der (∗£A ⊢ ∗X) Snn
                   [Unf (X ⊢ £A)]];
                  Der (£B ⊢ ∗X,, Y) Commr
                   [Der (£B ⊢ Y,, ∗X) Wkr
                   [Unf (£B ⊢ Y)]]]).
  Defined.

  #[export] Instance derr_Mrrslln : DerivRule CPL_DC' Mrrslln.
  Proof.
    unfold Mrrslln. set_XYZW.
    confirm_derr (Der (Z ⊢ ∗X,, Y) Mlln
                 [Der (X,, Z ⊢ Y) Mrrs
                 [Unf (X ⊢ Y,, ∗Z)]]).
  Defined.

  #[export] Instance derr_Mlrsrln : DerivRule CPL_DC' Mlrsrln.
  Proof.
    unfold Mlrsrln. set_XYZW.
    confirm_derr (Der (∗Z,, X ⊢ Y) Mrln
                 [Der (X ⊢ Z,, Y) Mlrs
                 [Unf (X,, ∗Y ⊢ Z)]]).
  Defined.

  Theorem DerivDC_CPLDC'_CPLDC : DerivDC CPL_DC' (remove_rule CUT CPL_DC).
  Proof.
    unfold CPL_DC. intros r Hr. simpl remove_rule in Hr.
    dec_destruct_List_In rule_eq_dec r;
    rewrite Heq;
    try apply (alr_DerivRule _ _);
    try (apply derr_rules; auto_in; fail).
  Defined.

  Theorem DerivDC_CPLDC_CPLDC' : DerivDC (remove_rule CUT CPL_DC) CPL_DC'.
  Proof.
    unfold CPL_DC'. simpl app. intros r Hr.
    apply dernc_derremcut.
    dec_destruct_List_In rule_eq_dec r;
    rewrite Heq;
    try apply (alr_DerivRuleNC _ _);
    apply derrnc_rules; simpl; tauto.
  Defined.

  Theorem EqDer_CPLDC_CPLDC' : EqDer (remove_rule CUT CPL_DC) CPL_DC'.
  Proof.
    apply DerivDC_EqDer.
    - apply DerivDC_CPLDC_CPLDC'.
    - apply DerivDC_CPLDC'_CPLDC.
  Defined.


  #[export] Instance dernc_frefl : forall A : PL.formula, fmlNoFV A -> DerivRuleNC CPL_DC (frefl A).
  Proof.
    intros A H. induction A; try (contradict H; apply isVar_not_noVar; constructor).
    all: try (apply fmlNoFV_ipse in H; try (intros; discriminate)).
    all: try (specialize (IHA (Forall_inv H))).
    all: try (specialize (IHA1 (Forall_inv H));
              specialize (IHA2 (Forall_inv (Forall_inv_tail H)))).
    all: unfold frefl.
    - set (d := Der (£% p ⊢ £% p) atrefl []). confirm_derrnc d.
    - set (d := Der (£ PL.Top ⊢ £ PL.Top) Topl
               [Der (I ⊢ £ PL.Top) Topr []]).
      confirm_derrnc d.
    - set (d := Der (£ PL.Bot ⊢ £ PL.Bot) Botr
               [Der (£ PL.Bot ⊢ I) Botl []]).
      confirm_derrnc d.
    - apply_DRNC_inDC Negr.
      apply_DRNC_inDC Negl.
      apply_DRNC_inDC Snn.
      assumption.
    - apply_DRNC_inDC Impr.
      apply_DRNC_inDC Comml.
      apply_DRNC_inDC Mrls.
      apply_DRNC_inDC Impl; assumption.
    - apply_DRNC_inDC Disr.
      apply_DRNC_inDC Disl; assumption.
    - apply_DRNC_inDC Conl.
      apply_DRNC_inDC Conr; assumption.
  Defined.

  Import PL.
  #[export] Instance CPL_DC_derr_frefl : forall A : formula, fmlNoFV A -> DerivRule CPL_DC (frefl A).
  Proof. apply dernc_frefl. Defined.

End CPLDeriv.

Module CPLBelnap.

  Import CPLDeriv.

  Theorem has_CUT : In CUT CPL_DC.
  Proof. simpl. tauto. Qed.

  Theorem C3_holds : C3 CPL_DC.
  Proof. auto_C3. Qed.

  Theorem C4_holds : C4 CPL_DC.
  Proof. auto_C4. Qed.

  Theorem C5_holds : C5 CPL_DC.
  Proof. auto_C5. Qed.

  Theorem C8_Neg {X Y A} : C8_case CPL_DC X Y [X ⊢ ∗ £A; ∗ £A ⊢ Y] (isipsubfml (¬ A)).
  Proof.
    prep_C8_case.
    apply_cof_inst Sss.
    apply_cof_CUT A.
    - apply_cof_inst Ssn. assumption.
    - apply_cof_inst Sns. assumption.
  Defined.


  Theorem C8_Con {X Y Z A B} : C8_case CPL_DC (X,, Y) Z
                                 [X ⊢ £A; Y ⊢ £B; £A,, £B ⊢ Z]
                                 (isipsubfml (A ∧ B)).
  Proof.
    prep_C8_case.
    apply_cof_inst Mrrs.
    apply_cof_CUT A; [assumption|].
    apply_cof_inDC Mlrn.
    apply_cof_inDC Mrls.
    apply_cof_CUT B; [assumption|].
    apply_cof_inst Mlln.
    assumption.
  Defined.

  Theorem C8_Dis {X Y Z A B} : C8_case CPL_DC X (Y,, Z)
                                       [X ⊢ £A,, £B; £A ⊢ Y; £B ⊢ Z]
                                       (isipsubfml (A ∨ B)).
  Proof.
    prep_C8_case.
    apply_cof_inDC Mlls.
    apply_cof_CUT B; [|assumption].
    apply_cof_inDC Mlrsrln.
    apply_cof_CUT A; [|assumption].
    apply_cof_inDC Mrrn.
    assumption.
  Defined.

  Theorem C8_Imp {X Y Z A B} :
    C8_case CPL_DC X (∗Y,, Z) [Y ⊢ £A; X,, £A ⊢ £B; £B ⊢ Z] (isipsubfml (A → B)).
  Proof.
    prep_C8_case.
    apply_cof_inst Mlln.
    apply_cof_CUT B; [|assumption].
    apply_cof_inst Mrrs.
    apply_cof_CUT A; [assumption|].
    apply_cof_inDC Mlrn.
    apply_cof_inDC Comml.
    assumption.
  Defined.

  
  Theorem C8_holds : C8 CPL_DC.
  Proof.
    auto_C8.
    - remember (fst (fst afsR) "p") as p. rewrite HeqipsA in *.
      exists (Der (£ PL.Atf p ⊢ £ PL.Atf p) atrefl []). split.
      try (repeat (split; try auto_in; try auto_wfr)).
      rewrite HeqX, HeqY. split; try reflexivity.
      simpl. split; [left; discriminate|constructor].
    - exists dR. rewrite HeqX, HeqY. split; [|split]; try assumption.
      apply (allDT_impl _ _ (nocut_impl_cut (@isipsubfml _ _ f_PL A))).
      assumption.
    - exists dL. rewrite HeqX, HeqY. split; [|split]; try assumption.
      apply (allDT_impl _ _ (nocut_impl_cut (@isipsubfml _ _ f_PL A))).
      assumption.
    - rewrite HeqX, HeqY, HeqAR. rewrite H1 in *.
      apply (C8_Neg [dL; dR]); try auto_Forall.
      simpl. rewrite H, H0. reflexivity.
    - rewrite HeqX, HeqY, HeqAR. rewrite H2, H3 in *.
      apply (C8_Con [dL; dL0; dR]); try auto_Forall.
      simpl. rewrite H, H0, H1. reflexivity.
    - rewrite HeqX, HeqY, HeqAR. rewrite H2, H3 in *.
      apply (C8_Dis [dL; dR; dR0]); try auto_Forall.
      simpl. rewrite H, H0, H1. reflexivity.
    - rewrite HeqX, HeqY, HeqAR. rewrite H2, H3 in *.
      apply (C8_Imp [dR; dL; dR0]); try auto_Forall.
      simpl. rewrite H, H0, H1. reflexivity.
  Defined.

End CPLBelnap.

#[export] Instance CPL_DC_Bel : BELNAP CPL_DC := {|
  has_CUT := CPLBelnap.has_CUT;
  C3_holds := CPLBelnap.C3_holds;
  C4_holds := CPLBelnap.C4_holds;
  C5_holds := CPLBelnap.C5_holds;
  C8_holds := CPLBelnap.C8_holds; |}.
  

Definition CPL_cutElim := cutElim CPL_DC CPL_DC_Bel.
