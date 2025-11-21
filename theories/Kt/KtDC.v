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
Require Import KtLang.
Import KtNotations.
Require Import Rules.
Require Import KtRules.

Import KtRules.

Definition Kt_DC : DISPCALC :=
  [atrefl; CUT;
   Topl; Topr; Botl; Botr; Negl; Negr; Conl; Conr; Disl; Disr; Impl; Impr;
   Boxnl; Boxnr; Dianl; Dianr; Boxpl; Boxpr; Diapl; Diapr;
   Iaddl; Idell; Iaddr; Idelr; Isl; Iul; Isr; Iur; Wkl; Wkr;
   Assol; Assolinv; Assor; Assorinv; Comml; Commr; Contl; Contr; Icl; Icr;
   Mlrn; Mrrs; Mlln; Mrls; Mrrn; Mlrs; Mrln; Mlls;
   Ssn; Sns; DSEl; DSIl; DSEr; DSIr; Scl; Scr].


Definition Kt_RIR : list rule :=
  [atrefl; Topr; Botr; Negr; Conr; Disr; Impr; Boxnr; Dianr; Boxpr; Diapr].
Definition Kt_LIR : list rule :=
  [atrefl; Topl; Botl; Negl; Conl; Disl; Impl; Boxnl; Dianl; Boxpl; Diapl].

Lemma Kt_RIR_ppty : forall r, r ∈ Kt_DC -> (r ∈ Kt_RIR <-> strIsFml (succ (conclRule r))).
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

Lemma Kt_LIR_ppty : forall r, r ∈ Kt_DC -> (r ∈ Kt_LIR <-> strIsFml (antec (conclRule r))).
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
#[export] Instance Kt_INTRO_RULES : INTRO_RULES Kt_DC := {|
  RIR := Kt_RIR;
  LIR := Kt_LIR;
  RIR_ppty := Kt_RIR_ppty;
  LIR_ppty := Kt_LIR_ppty
|}.


Module KtDeriv.

  Ltac set_XYZW :=
    set (X := $"X" : structr); set (Y := $"Y" : structr);
    set (Z := $"Z" : structr); set (W := $"W" : structr).

  #[export] Instance dernc_Snn : DerivRuleNC Kt_DC Snn.
  Proof.
    set_XYZW.
    confirm_derrnc (Der (∗Y ⊢ ∗X) Idell
                   [Der (I,, ∗Y ⊢ ∗X) Mrrn
                   [Der (I ⊢ ∗X,, Y) Mlln
                   [Der (X,, I ⊢ Y) Comml
                   [Der (I,, X ⊢ Y) Iaddl
                   [Unf (X ⊢ Y)]]]]]).
  Defined.

  #[export] Instance dernc_Sss : DerivRuleNC Kt_DC Sss.
  Proof.
    set_XYZW.
    confirm_derrnc (Der (Y ⊢ X) DSEl
                   [Der ((∗∗Y) ⊢ X) Ssn
                   [Unf (∗X ⊢ ∗Y)]]).
  Defined.

  #[export] Instance dernc_frefl : forall A : Kt.formula, fmlNoFV A -> DerivRuleNC Kt_DC (frefl A).
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
    - apply_DRNC_inDC Negr.
      apply_DRNC_inDC Negl.
      apply_DRNC_inDC Ssn.
      apply_DRNC_inDC DSIl.
      assumption.
    - apply_DRNC_inDC Impr.
      apply_DRNC_inDC Comml.
      apply_DRNC_inDC Mrls.
      apply_DRNC_inDC Impl; assumption.
    - apply_DRNC_inDC Disr.
      apply_DRNC_inDC Disl; assumption.
    - apply_DRNC_inDC Conl.
      apply_DRNC_inDC Conr; assumption.
    - apply_DRNC_inDC Boxnr.
      apply_DRNC_inDC Scr.
      apply_DRNC_inDC Boxnl.
      assumption.
    - apply_DRNC_inDC Dianl.
      apply_DRNC_inDC Dianr.
      assumption.
    - apply_DRNC_inDC Boxpr.
      apply_DRNC_inDC Boxpl.
      assumption.
    - apply_DRNC_inDC Diapl.
      apply_DRNC_inDC Scl.
      apply_DRNC_inDC Diapr.
      assumption.
  Defined.

End KtDeriv.

Module KtBelnap.

  Import KtDeriv.

  Theorem has_CUT : In CUT Kt_DC.
  Proof. auto_in. Qed.

  Theorem C3_holds : C3 Kt_DC.
  Proof. auto_C3. Qed.

  Theorem C4_holds : C4 Kt_DC.
  Proof. auto_C4. Qed.

  Theorem C5_holds : C5 Kt_DC.
  Proof. auto_C5. Qed.

  Theorem C8_Neg {X Y A} : C8_case Kt_DC X Y [X ⊢ ∗ £A; ∗ £A ⊢ Y] (isipsubfml (¬ A)).
  Proof.
    prep_C8_case.
    apply_cof_inst Sss.
    apply_cof_CUT A.
    - apply_cof_inDC Ssn. assumption.
    - apply_cof_inDC Sns. assumption.
  Defined.


  Theorem C8_Con {X Y Z A B} : C8_case Kt_DC (X,, Y) Z
                                 [X ⊢ £A; Y ⊢ £B; £A,, £B ⊢ Z]
                                 (isipsubfml (A ∧ B)).
  Proof.
    prep_C8_case.
    apply_cof_inDC Mrrs.
    apply_cof_CUT A; [assumption|].
    apply_cof_inDC Mlrn.
    apply_cof_inDC Mrls.
    apply_cof_CUT B; [assumption|].
    apply_cof_inDC Mlln.
    assumption.
  Defined.

  Theorem C8_Dis {X Y Z A B} : C8_case Kt_DC X (Y,, Z)
                                       [X ⊢ £A,, £B; £A ⊢ Y; £B ⊢ Z]
                                       (isipsubfml (A ∨ B)).
  Proof.
    prep_C8_case.
    apply_cof_inDC Mlls.
    apply_cof_CUT B; [|assumption].
    apply_cof_inDC Mrln.
    apply_cof_inDC Mlrs.
    apply_cof_CUT A; [|assumption].
    apply_cof_inDC Mrrn.
    assumption.
  Defined.

  Theorem C8_Imp {X Y Z A B} :
    C8_case Kt_DC X (∗Y,, Z) [Y ⊢ £A; X,, £A ⊢ £B; £B ⊢ Z] (isipsubfml (A → B)).
  Proof.
    prep_C8_case.
    apply_cof_inDC Mlln.
    apply_cof_CUT B; [|assumption].
    apply_cof_inDC Mrrs.
    apply_cof_CUT A; [assumption|].
    apply_cof_inDC Mlrn.
    apply_cof_inDC Comml.
    assumption.
  Defined.

  Theorem C8_Boxn {X Y A} :
    C8_case Kt_DC X (●Y) [●X ⊢ £A; £A ⊢ Y] (isipsubfml (◻A)).
  Proof.
    prep_C8_case.
    apply_cof_inDC Scl.
    apply_cof_CUT A; assumption.
  Defined.

  Theorem C8_Dian {X Y A} :
    C8_case Kt_DC (∗●∗X) Y [X ⊢ £A; (∗●∗ £A) ⊢ Y] (isipsubfml (◊A)).
  Proof.
    prep_C8_case.
    apply_cof_inDC Ssn.
    apply_cof_inDC Scl.
    apply_cof_inDC Sns.
    apply_cof_CUT A; [assumption|].
    apply_cof_inDC Sns.
    apply_cof_inDC Scr.
    apply_cof_inDC Ssn.
    assumption.
  Defined.

  Theorem C8_Boxp {X Y A} :
    C8_case Kt_DC X (∗●∗Y) [X ⊢ ∗●∗ £A; £A ⊢ Y] (isipsubfml (◼A)).
  Proof.
    prep_C8_case.
    apply_cof_inDC Sns.
    apply_cof_inDC Scr.
    apply_cof_inDC Ssn.
    apply_cof_CUT A; [|assumption].
    apply_cof_inDC Ssn.
    apply_cof_inDC Scl.
    apply_cof_inDC Sns.
    assumption.
  Defined.

  Theorem C8_Diap {X Y A} :
    C8_case Kt_DC (●X) Y [X ⊢ £A; £A ⊢ ●Y] (isipsubfml (⧫A)).
  Proof.
    prep_C8_case.
    apply_cof_inDC Scr.
    apply_cof_CUT A; assumption.
  Defined.

  
  Theorem C8_holds : C8 Kt_DC.
  Proof.
    prep_C8 Kt_DC.
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
    - rewrite HeqX, HeqY, HeqAR. rewrite H1 in *.
      apply (C8_Boxn [dL; dR]); try auto_Forall.
      simpl. rewrite H, H0. reflexivity.
    - rewrite HeqX, HeqY, HeqAR. rewrite H1 in *.
      apply (C8_Dian [dL; dR]); try auto_Forall.
      simpl. rewrite H, H0. reflexivity.
    - rewrite HeqX, HeqY, HeqAR. rewrite H1 in *.
      apply (C8_Boxp [dL; dR]); try auto_Forall.
      simpl. rewrite H, H0. reflexivity.
    - rewrite HeqX, HeqY, HeqAR. rewrite H1 in *.
      apply (C8_Diap [dL; dR]); try auto_Forall.
      simpl. rewrite H, H0. reflexivity.
  Defined.

End KtBelnap.

#[export] Instance Kt_DCBel : BELNAP Kt_DC := {|
  has_CUT := KtBelnap.has_CUT;
  C3_holds := KtBelnap.C3_holds;
  C4_holds := KtBelnap.C4_holds;
  C5_holds := KtBelnap.C5_holds;
  C8_holds := KtBelnap.C8_holds; |}.

Definition Kt_cutElim := cutElim Kt_DC Kt_DCBel.
