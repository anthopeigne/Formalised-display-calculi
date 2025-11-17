Require Import String.
Open Scope string_scope.
Require Import Relations.
Require Import List ListSet.
Import ListNotations.
Require Import ListSetNotations.
Require Import ListSet.
Require Import Arith.
Require Import ssrbool.
Require Import Wellfounded.
Require Import Datatypes.
Require Import Lia.
Require Import FunctionalExtensionality.

Require Import EqDec.
Require Import Tactics.
Require Import Utils.
Require Import FunAgree.
Require Import Lang.
Require Import Sequents.
Require Import Substitutions.

(* Open Scope nat_scope. *)


(* Application of our framework to Kt (Tense logic). *)


Module Lambek.
  Inductive formula : Set :=
    | Atf (p : string)
    | FVf (A : string)
    | Top
    | Bot
    | Dis (phi psi : formula)
    | Con (phi psi : formula)
    | One
(*    | Zer*)
    | Fus (phi psi : formula)
    | Und (phi psi : formula)
    | Ove (phi psi : formula).

  Inductive structr : Set :=
    | SVf (X : string)
    | FSf (A : formula)
    | I
    | Φ
    | Smc (X Y : structr)
    | Gre (X Y : structr)
    | Les (X Y : structr).
End Lambek.

Module LambekNotations.
  
  Export Lambek.
  
  Notation "% p" := (Lambek.Atf p) (at level 10).
  Notation "? A" := (Lambek.FVf A) (at level 10).
  Notation "⊤" := (Lambek.Top) (at level 20).
  Notation "⊥" := (Lambek.Bot) (at level 20).
  Notation "|" := (Lambek.One) (at level 20).
(*  Notation "○" := (Lambek.Zer) (at level 20).*)
  Notation "phi ∨ psi" := (Lambek.Dis phi psi) (at level 30).
  Notation "phi ∧ psi" := (Lambek.Con phi psi) (at level 30).
  Notation "phi ⊗ psi" := (Lambek.Fus phi psi) (at level 30).
  Notation "phi \ psi" := (Lambek.Und phi psi) (at level 30).
  Notation "phi ∕ psi" := (Lambek.Ove phi psi) (at level 30).
  
  Notation "$ X" := (Lambek.SVf X) (at level 35).
  Notation "£ A" := (Lambek.FSf A) (at level 35).
  Notation "X ;; Y" := (Lambek.Smc X Y) (at level 50).
  Notation "X ⟩ Y" := (Lambek.Gre X Y) (at level 50).
  Notation "X ⟨ Y" := (Lambek.Les X Y) (at level 50).
End LambekNotations.

Module Lambek_LOG.

  Import Lambek.

  Theorem fml_eq_dec : eq_dec formula.
  Proof. unfold eq_dec. decide equality; apply string_dec. Defined.

  Definition ipse (A : formula) : list formula :=
    match A with
    | Dis A1 A2   => [A1; A2]
    | Con A1 A2   => [A1; A2]
    | Fus A1 A2   => [A1; A2]
    | Und A1 A2   => [A1; A2]
    | Ove A1 A2   => [A1; A2]
    | _           => []
    end.
    
  Theorem ipse_rect (P : formula -> Type) :
    (forall A, (forall B, B ∈ (ipse A) -> P B) -> P A) -> forall A, P A.
  Proof.
    intro H. induction A; apply H;
      try (simpl; tauto);
      try (intros B HB; simpl ipse in HB;
           dest_in_list_eqdec_rec fml_eq_dec B;
           rewrite Heq; assumption).
  Defined.

  (* Requires functional extensionality *)
  Theorem ipse_rect_cmp :
    forall P P_IS A, ipse_rect P P_IS A = P_IS A (fun B HB => ipse_rect _ P_IS B).
  Proof.
    intros P f. induction A;
    simpl; apply f_equal; extensionality B; extensionality HB;
    try contradiction.
    all:
    repeat match goal with
      |- context[match ?C with _ => _ end] =>
          let Heq := fresh "Heq" in
          let Hneq := fresh "Hneq" in
          destruct C as [Heq|Hneq]
    end;
    try (rewrite Heq; unfold eq_rect_r; simpl; reflexivity);
    exfalso;
    repeat destruct HB as [HB|HB]; contradict HB; apply not_eq_sym; assumption.
  Qed.

  Definition fml_df : formula := Atf "".

  Definition conn (A : formula) : list formula -> formula :=
    match A with
    | Dis A1 A2   => fun l => match l with B1 :: B2 :: _ => Dis B1 B2 | _ => fml_df end
    | Con A1 A2   => fun l => match l with B1 :: B2 :: _ => Con B1 B2 | _ => fml_df end
    | Fus A1 A2   => fun l => match l with B1 :: B2 :: _ => Fus B1 B2 | _ => fml_df end
    | Und A1 A2   => fun l => match l with B1 :: B2 :: _ => Und B1 B2 | _ => fml_df end
    | Ove A1 A2   => fun l => match l with B1 :: B2 :: _ => Ove B1 B2 | _ => fml_df end
    | A0          => fun _ => A0
    end.

  Lemma conn_ipse : forall A : formula, A = conn A (ipse A).
  Proof. destruct A; reflexivity. Qed.

  Lemma conn_inj : forall (A B : formula) (l l' : list formula),
      length l = length (ipse A) ->
      length l' = length (ipse B) -> conn A l = conn B l' -> conn A = conn B /\ l = l'.
  Proof.
    destruct A; destruct B; intros l l' Hl Hl' Heq; simpl in *;
      try (apply length_zero_iff_nil in Hl, Hl'; now rewrite Hl, Hl');
    repeat (let B := fresh "B" in destruct l as [|B l]; try discriminate);
    repeat (let C := fresh "C" in destruct l' as [|C l']; try discriminate);
    injection Heq; intros; all_rewrite; split; reflexivity.
  Qed.

  Definition Atm := Atf.
  Definition FV := FVf.

  Lemma Atm_dec : forall A : formula, {p : string | A = Atm p} + {forall p : string, A <> Atm p}.
  Proof.
    destruct A; try (right; intro; discriminate).
    left. exists p. reflexivity.
  Defined.

  Lemma FV_dec : forall A : formula, {V : string | A = FV V} + {forall V : string, A <> FV V}.
  Proof.
    destruct A; try (right; intro; discriminate).
    left. exists A. reflexivity.
  Defined.

  Lemma Atm_FV_disc : forall p V : string, Atm p <> FV V.
  Proof. intros p V. discriminate. Qed.

  Lemma Atm_inj : forall p q : string, Atm p = Atm q -> p = q.
  Proof. intros p q H. injection H. tauto. Qed.

  Lemma FV_inj : forall V W : string, FV V = FV W -> V = W.
  Proof. intros V W H. injection H. tauto. Qed.

  Lemma Atm_ipse : forall p : string, ipse (Atm p) = [].
  Proof. reflexivity. Qed.

  Lemma FV_ipse : forall V : string, ipse (FV V) = [].
  Proof. reflexivity. Qed.

End Lambek_LOG.

#[export] Instance EqDec_formula : EqDec Lambek.formula := {| eqdec := Lambek_LOG.fml_eq_dec |}.

#[export] Instance f_Lambek_log : @FLANG Lambek.formula _ := {|
  ipse   := Lambek_LOG.ipse;
  ipse_rect := Lambek_LOG.ipse_rect;
  ipse_rect_cmp := Lambek_LOG.ipse_rect_cmp;
  conn := Lambek_LOG.conn;
  conn_ipse := Lambek_LOG.conn_ipse;
  conn_inj := Lambek_LOG.conn_inj |}.

#[export] Instance Lambek_Atm : @IXEXP _ _ f_Lambek_log string Lambek_LOG.Atm := {|
  Var_dec := Lambek_LOG.Atm_dec;
  Var_inj := Lambek_LOG.Atm_inj;
  Var_ipse := Lambek_LOG.Atm_ipse; |}.

#[export] Instance Lambek_FV : @IXEXP _ _ f_Lambek_log string Lambek_LOG.FV := {|
  Var_dec := Lambek_LOG.FV_dec;
  Var_inj := Lambek_LOG.FV_inj;
  Var_ipse := Lambek_LOG.FV_ipse; |}.

#[export] Instance Lambek_log : @LOGLANG _ _ f_Lambek_log := {|
  Atm := Lambek.Atf;
  FV := Lambek.FVf;
  ATMVAR := Lambek_Atm;
  FVVAR := Lambek_FV;
  Atm_FV_disc := Lambek_LOG.Atm_FV_disc; |}.

Module Lambek_STR.
  
  Import Lambek.

  Theorem str_eq_dec : eq_dec structr.
  Proof. unfold eq_dec. decide equality; apply eqdec. Defined.

  Definition ipse (X : structr) : list structr :=
    match X with
    | Smc X1 X2   => [X1; X2]
    | Gre X1 X2   => [X1; X2]
    | Les X1 X2   => [X1; X2]
    | _           => []
    end.
    
  Theorem ipse_rect (P : structr -> Type) :
    (forall A, (forall B, B ∈ (ipse A) -> P B) -> P A) -> forall A, P A.
  Proof.
    intro H. induction A; apply H;
      try (simpl; tauto);
      try (intros B HB; simpl ipse in HB;
           dest_in_list_eqdec_rec str_eq_dec B;
           rewrite Heq; assumption).
  Defined.

  (* Requires functional extensionality *)
  Theorem ipse_rect_cmp :
    forall P P_IS A, ipse_rect P P_IS A = P_IS A (fun B HB => ipse_rect _ P_IS B).
  Proof.
    intros P f. induction A;
    simpl; apply f_equal; extensionality B; extensionality HB;
    try contradiction.
    all:
    repeat match goal with
      |- context[match ?C with _ => _ end] =>
          let Heq := fresh "Heq" in
          let Hneq := fresh "Hneq" in
          destruct C as [Heq|Hneq]
    end;
    try (rewrite Heq; unfold eq_rect_r; simpl; reflexivity);
    exfalso;
    repeat destruct HB as [HB|HB]; contradict HB; apply not_eq_sym; assumption.
  Qed.

  Definition str_df : structr := SVf "".

  Definition conn (X : structr) : list structr -> structr :=
    match X with
    | Smc X1 X2 => fun l => match l with Y1 :: Y2 :: _ => Smc Y1 Y2 | _ => str_df end
    | Gre X1 X2 => fun l => match l with Y1 :: Y2 :: _ => Gre Y1 Y2 | _ => str_df end
    | Les X1 X2 => fun l => match l with Y1 :: Y2 :: _ => Les Y1 Y2 | _ => str_df end
    | X0          => fun _ => X0
    end.

  Lemma conn_ipse : forall X : structr, X = conn X (ipse X).
  Proof. destruct X; reflexivity. Qed.

  Lemma conn_inj : forall (X Y : structr) (l l' : list structr),
      length l = length (ipse X) ->
      length l' = length (ipse Y) -> conn X l = conn Y l' -> conn X = conn Y /\ l = l'.
  Proof.
    destruct X; destruct Y; intros l l' Hl Hl' Heq; simpl in *;
      try (apply length_zero_iff_nil in Hl, Hl'; now rewrite Hl, Hl');
    repeat (let Y := fresh "Y" in destruct l as [|Y l]; try discriminate);
    repeat (let C := fresh "C" in destruct l' as [|C l']; try discriminate);
    injection Heq; intros; all_rewrite; split; reflexivity.
  Qed.

  Definition SV := SVf.
  Definition FS := FSf.

  Lemma SV_dec : forall X : structr, {v : string | X = SV v} + {forall v : string, X <> SV v}.
  Proof.
    destruct X; try (right; intro; discriminate).
    left. exists X. reflexivity.
  Defined.

  Lemma FS_dec : forall X : structr, {A : formula | X = FS A} + {forall A : formula, X <> FS A}.
  Proof.
    destruct X; try (right; intro; discriminate).
    left. exists A. reflexivity.
  Defined.

  Lemma SV_FS_disc : forall v A, SV v <> FS A.
  Proof. intros. discriminate. Qed.

  Lemma SV_inj : forall v w : string, SV v = SV w -> v = w.
  Proof. intros v w H. injection H. tauto. Qed.

  Lemma FS_inj : forall A B : formula, FS A = FS B -> A = B.
  Proof. intros A B H. injection H. tauto. Qed.

  Lemma SV_ipse : forall v : string, ipse (SV v) = [].
  Proof. reflexivity. Qed.

  Lemma FS_ipse : forall A : formula, ipse (FS A) = [].
  Proof. reflexivity. Qed.
  
  Definition sgnips (X : structr) : list bool :=
    match X with
    | Smc X1 X2 => [true; true]
    | Gre X1 X2 => [false; true]
    | Les X1 X2 => [true; false]
    | _           => []
    end.

  Lemma sgnips_length : forall X : structr, length (sgnips X) = length (ipse X).
  Proof. intro X. destruct X; reflexivity. Qed.

  Lemma sgnips_conn : forall (X : structr) (l : list structr),
      length l = length (ipse X) -> sgnips (conn X l) = sgnips X.
  Proof.
    intros X l H. destruct X; try reflexivity.
    all: destruct_list_easy l X.
  Qed.
  
End Lambek_STR.

#[export] Instance EqDec_structr : EqDec Lambek.structr := {| eqdec := Lambek_STR.str_eq_dec |}.

#[export] Instance f_Lambek : @FLANG Lambek.structr _ := {|
  ipse   := Lambek_STR.ipse;
  ipse_rect := Lambek_STR.ipse_rect;
  ipse_rect_cmp := Lambek_STR.ipse_rect_cmp;
  conn := Lambek_STR.conn;
  conn_ipse := Lambek_STR.conn_ipse;
  conn_inj := Lambek_STR.conn_inj |}.

#[export] Instance Lambek_SV : @IXEXP _ _ f_Lambek string Lambek_STR.SV := {|
  Var_dec := Lambek_STR.SV_dec;
  Var_inj := Lambek_STR.SV_inj;
  Var_ipse := Lambek_STR.SV_ipse; |}.

#[export] Instance Lambek_FS : @IXEXP _ _ f_Lambek Lambek.formula Lambek_STR.FS := {|
  Var_dec := Lambek_STR.FS_dec;
  Var_inj := Lambek_STR.FS_inj;
  Var_ipse := Lambek_STR.FS_ipse; |}.

#[export] Instance Lambek_str : @STRLANG _ Lambek.structr _ _ Lambek_log _ f_Lambek := {|
  SV := Lambek.SVf;
  FS := Lambek.FSf;
  SVVAR := Lambek_SV;
  FSVAR := Lambek_FS;
  SV_FS_disc := Lambek_STR.SV_FS_disc;
  sgnips := Lambek_STR.sgnips;
  sgnips_length := Lambek_STR.sgnips_length;
  sgnips_conn := Lambek_STR.sgnips_conn |}.
