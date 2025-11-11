Require Import String.
Require Import Constructive_sets.
Require Import Relations.
Require Import List ListDec Decidable.
Import ListNotations.
Require Import ListSetNotations.
Require Import Datatypes.
Require Import Arith.
Require Import Bool.

Require Import EqDec.
Require Import Tactics.
Require Import Utils.
Require Import Lang.
Require Import Sequents.
Require Import Substitutions.
Require Import Derivation.
Require Import Cuts.




Ltac auto_C1 :=
  let r := fresh "r" in let Hr := fresh "H" r in
  intros r Hr; dest_in_list Hr;
  match goal with H : _ = r |- _ =>
    rewrite <- H; unfold C1_one;
  repeat (constructor; try (simpl; split; auto_incl)) end.


Ltac auto_C3 :=
  match goal with
  | |- C3 ?DC => try unfold DC
  end;
  let r := fresh "r" in
  let Hr := fresh "H" r in
  intros r Hr; dest_in_list Hr;
   match goal with
   | H:_ = r |- _ =>
       rewrite <- H; unfold seqSVs; simpl;
       try (repeat (constructor; try (intro; dest_in_list_any; discriminate || tauto));
            apply in_nil)
   end.

(*
Ltac auto_C3 :=
  let r := fresh "r" in let Hr := fresh "H" r in
  intros r Hr; simpl in Hr; destruct_List_In_name Hr;
  match goal with
    | [ H : _ = r |- _ ] =>
        rewrite <- H; unfold seqSVs; simpl; try (
        repeat (constructor; try (intro; destruct_List_In; (discriminate || tauto)));
        apply in_nil)
  end.
*)



Ltac auto_C4 :=
  match goal with
  | |- C4 ?DC => try unfold DC
  end;
  let r := fresh "r" in let Hr := fresh "H" r in
  intros r Hr; dest_in_list Hr;
   match goal with
   | H:_ = r |- _ =>
       let prems := fresh "prems" in
       let b := fresh "b" in let s := fresh "s" in
       rewrite <- H; try (intros prems b s; destruct b; simpl; try tauto; intros;
       repeat dest_or_any; try contradiction;
       match goal with
       | H0:_ = prems |- _ =>
           match goal with
           | H1:_ = s |- _ =>
               rewrite <- H0, <- H1; unfold seqSVsSgn; simpl; intro;
               dest_or_any; discriminate || tauto
           end
       end)
   end.

(*
Ltac auto_C4 :=    
  let r := fresh "r" in let Hr := fresh "H" r in
  intros r Hr; simpl in Hr; destruct_List_In_name Hr;
  match goal with
  | [ H : _ = r |- _ ] =>
    let prems := fresh "prems" in let b := fresh "b" in let s := fresh "s" in
    rewrite <- H; try (intros prems b s; destruct b; simpl;
    try tauto; intros; repeat destruct_or; try contradiction;
    match goal with
    | [ H0 : _ = prems |- _ ] =>
      match goal with
      | [ H1 : _ = s |- _ ] =>
        rewrite <- H0, <- H1; unfold seqSVsSgn; simpl; intro; destruct_or; (discriminate || tauto)
      end
    end)
  end.
*)

Arguments eq_rect_r /.


Ltac auto_C5 :=
  match goal with
  | |- C5 ?DC => try unfold DC
  end;
  let r := fresh "r" in
  let Hr := fresh "H" r in
  intros r Hr; try (dest_in_list Hr;
    match goal with
    | H:_ = r |- _ => rewrite <- H
    end);
  simpl; unfold strIsFml, strCtnsFml;
  rewrite !(isVar_iff_isVar_cpt FS), !(CtnsVar_iff_CtnsVar_cpt FS);
  repeat
  (rewrite CtnsVar_cpt_eq; unfold isVar_cpt; simpl Var_dec; simpl ipse; cbv iota;
   unfold fold_right); tauto.

(*
Ltac auto_C5 :=
  let r := fresh "r" in
  let Hr := fresh "H" r in
  intros r Hr; simpl in Hr;
   try
    (destruct_List_In_name Hr;
      match goal with
      | H:_ = r |- _ => rewrite <- H
      end);
  simpl; unfold strIsFml, strCtnsFml;
  rewrite ! (isVar_iff_isVar_cpt FS), ! (CtnsVar_iff_CtnsVar_cpt FS);
  repeat (rewrite CtnsVar_cpt_eq; unfold isVar_cpt; simpl Var_dec;
          simpl ipse; cbv iota; unfold fold_right); try tauto.
*)

Section C8.

  Context `{SL : STRLANG}.
  Context (DC : DISPCALC).

  Definition C8_case (X Y : structr) (ls : list sequent) (fmls : formula -> Prop) :=
    forall (ld : list dertree),
      Forall (proper DC) ld ->
      map conclDT ld = ls ->
      Forall (allDT nocut) ld ->
      {dt : dertree | proper DC dt /\ conclDT dt = X ⊢ Y /\ allDT (cutOnFmls fmls) dt}.

  Definition C8_case_alt (X Y : structr) (ls : list sequent) (fmls : formula -> Prop) :=
    deriv_cofseqs DC fmls ls -> deriv_cofseq DC fmls (X ⊢ Y).

  Lemma C8_case_alt_imp_C8_case :
    forall X Y ls fmls, C8_case_alt X Y ls fmls -> C8_case X Y ls fmls.
  Proof.
    intros X Y ls fmls Halt ld Hprold Hconcld Hncld.
    apply deriv_cofseq_iff, Halt, deriv_cofseqs_iff.
    exists ld. repeat split; try assumption.
    eapply Forall_impl. eapply allDT_impl. apply nocut_impl_cut.
    assumption.
  Defined.


  Lemma LP_exhibit {A s r l} :
    r = CUT -> cutIsLP A (Der s r l) -> 
    {ant : structr &
             {r' : rule &
                     {l' : list dertree &
                             {pr : dertree | l = [Der (ant ⊢ FS A) r' l'; pr] /\ strIsFml (succ (conclRule r'))}}}}.
  Proof.
    intros Hr HLP. destruct (LP_dec l A) as [HyL|HnL]; [assumption|].
    exfalso. destruct HLP as [H|]; [contradiction|].
    destruct H as (ant & r' & l' & br & H).
    specialize (HnL ant r' l' br). tauto.
  Defined.

  Lemma RP_exhibit {A s r l} :
    r = CUT -> cutIsRP A (Der s r l) -> 
    {suc : structr &
             {pl : dertree &
                     {r' : rule &
                             {l' : list dertree | l = [pl; Der (FS A ⊢ suc) r' l'] /\ strIsFml (antec (conclRule r'))}}}}.
  Proof.
    intros Hr HRP. destruct (RP_dec l A) as [HyR|HnR]; [assumption|].
    exfalso. destruct HRP as [H|]; [contradiction|].
    destruct H as (suc & bl & r' & l' & H).
    specialize (HnR suc bl r' l'). tauto.
  Defined.


  Lemma reduce_C8 :
    (forall A l X Y rL lL rR lR afs,
        proper DC (Der (X ⊢ Y) CUT l) ->
        l = [Der (X ⊢ FS A) rL lL; Der (FS A ⊢ Y) rR lR] ->
        ([X ⊢ FS A; FS A ⊢ Y], X ⊢ Y) = ruleSubst afs CUT ->
        strIsFml (succ (conclRule rL)) ->
        strIsFml (antec (conclRule rR)) ->
        (forall d, d ∈ lL -> allDT nocut d) ->
        (forall d, d ∈ lR -> allDT nocut d) ->
        {dt : dertree | proper DC dt /\ conclDT dt = X ⊢ Y /\
                          allDT (cutOnFmls (isipsubfml A)) dt})  
    -> C8 DC.
  Proof.
    intros Hred A dt Hpro Hcut Hnocut; destruct Hcut as [HLP HRP].
    destruct dt as [|s r l]; [contradict Hpro; apply not_proper_Unf|].
    destruct (rule_eq_dec r CUT) as [Heqr|Hneqr];
      [|exists (Der s r l); split; [assumption | split; [reflexivity|]];
        apply (allDT_impl _ _ (nocut_impl_cut _)); apply allDT_Next; tauto].
    apply (LP_exhibit Heqr) in HLP.
    apply (RP_exhibit Heqr) in HRP.
    destruct HLP as (X & rL & lL & br & HLeql & HfmlrL).
    destruct HRP as (Y & bl & rR & lR & HReql & HfmlrR).
    rewrite HReql in HLeql. injection HLeql. intros Heqbr Heqbl.
    rewrite Heqbl in HReql. clear HLeql Heqbr Heqbl.
    rename HReql into Heql.
    pose proof (properUp Hpro) as Hproup. rewrite Heql in Hproup.
    specialize_Forall_H Hproup.
    rename Hproup0 into HproL. rename Hproup1 into HproR.
    rewrite Heql in Hnocut.
    pose proof (proper_root _ _ Hpro) as Hwfr. destruct Hwfr as [_ Hwfr].
    simpl in Hwfr. rewrite Heqr, Heql in Hwfr.
    apply ruleInst_ruleSubst in Hwfr.
    destruct Hwfr as [afs Hafs].
    injection Hafs. intros Heqs HeqY _ _ HeqX.
    rewrite <- HeqX, <- HeqY in Heqs. clear HeqY HeqX.
    rewrite Heqs. simpl.
    unfold allNextDTs, allDTs in Hnocut.
    rewrite <- Forall_fold_right, Forall_forall in Hnocut.
    spec_list Hnocut.
    pose proof (allDT_up_forall Hnocut0) as HnocutL; clear Hnocut0.
    pose proof (allDT_up_forall Hnocut1) as HnocutR; clear Hnocut1.
    rewrite Heqs, Heqr in Hpro. rewrite Heqs in Hafs.
    apply (Hred A l X Y rL lL rR lR afs); assumption.
  Defined.

  Class INTRO_RULES := {
    RIR : list rule;
    LIR : list rule;
    RIR_ppty : forall r, r ∈ DC -> (r ∈ RIR <-> strIsFml (succ (conclRule r)));
    LIR_ppty : forall r, r ∈ DC -> (r ∈ LIR <-> strIsFml (antec (conclRule r)))
  }.

End C8.


Ltac prep_C8_case :=
  apply C8_case_alt_imp_C8_case;
  let Hders := fresh "Hders" in intro Hders;
  apply ForallT_deriv_cofseqs_iff in Hders;
  specialize_ForallT_H Hders.


(* Assumes the user defined an Instance of INTRO_RULES DC. *)
Ltac prep_C8 DC :=
  let A := fresh "A" in let l := fresh "l" in
  let X := fresh "X" in let Y := fresh "Y" in
  let rL := fresh "rL" in let lL := fresh "lL" in
  let HrL := fresh "HrL" in let HnocutL := fresh "HnocutL" in
  let rR := fresh "rR" in let lR := fresh "lR" in
  let HrR := fresh "HrR" in let HnocutR := fresh "HnocutR" in
  let afs := fresh "afs" in let Hafs := fresh "Hafs" in
  let Heql := fresh "Heql" in
  let Hpro := fresh "Hpro" in let Hprol := fresh "Hprol" in
  let Hprol0 := fresh "Hprol" in let Hprol1 := fresh "Hprol" in
  let HproL := fresh "HproL" in let HproR := fresh "HproR" in
  let HexrL := fresh "HexrL" in let HwfrL := fresh "HwfrL" in
  let HexrR := fresh "HexrR" in let HwfrR := fresh "HwfrR" in
  let HprodL := fresh "HprodL" in let HprodR := fresh "HprodR" in
  apply reduce_C8;
  intros A l X Y rL lL rR lR afs Hpro Heql Hafs HrL HrR HnocutL HnocutR;
  pose proof (proper_up_Forall _ Hpro) as Hprol;
  rewrite Heql in Hprol;
  specialize_Forall_H Hprol;
  rename Hprol0 into HproL; rename Hprol1 into HproR;
  pose proof (properUp HproL) as HprodL;
  pose proof (properUp HproR) as HprodR;
  apply proper_root in HproL, HproR;
  destruct HproL as [HexrL HwfrL];
  destruct HproR as [HexrR HwfrR];
  apply (RIR_ppty DC rL HexrL) in HrL;
  apply (LIR_ppty DC rR HexrR) in HrR;
  simpl RIR in HrL; simpl LIR in HrR;
  match type of HrL with rL ∈ ?RI => unfold RI in HrL end;
  match type of HrR with rR ∈ ?LI => unfold LI in HrR end;
(* Compute all combinations of introduction rules *)
  let HeqrL := fresh "HeqrL" in let HeqrR := fresh "HeqrR" in
  dest_in_list_eqdec (@eqdec rule _) HrL; rename Heq into HeqrL;
  dest_in_list_eqdec (@eqdec rule _) HrR; rename Heq into HeqrR;
(* Get substitutions for rL and rR *)
  let afsL := fresh "afsL" in let HafsL := fresh "HafsL" in
  let afsR := fresh "afsR" in let HafsR := fresh "HafsR" in
  apply ruleInst_ruleSubst in HwfrL; destruct HwfrL as [afsL HafsL];
  rewrite HeqrL in HafsL;
  try (match type of HeqrL with rL = ?rho => unfold rho in HafsL end);
  apply ruleInst_ruleSubst in HwfrR; destruct HwfrR as [afsR HafsR];
  rewrite HeqrR in HafsR;
  try (match type of HeqrR with rR = ?rho => unfold rho in HafsR end);
(* Get equalities between X, Y, A, lL, lR, and the substitions of rL and rR *)
(* This part takes the longest, in particular the "injection" tactic *)
  let HeqAL := fresh "HeqAL" in let HeqX := fresh "HeqX" in
  let HeqlL := fresh "HeqlL" in let dL := fresh "dL" in
  injection HafsL; intros HeqAL HeqX HeqlL;
  destruct_list_easy lL dL; try (injection HeqlL; intros);
  simpl in HprodL; specialize_Forall_H HprodL;
  let HeqAR := fresh "HeqAR" in let HeqY := fresh "HeqY" in
  let HeqlR := fresh "HeqlR" in let dR := fresh "dR" in
  injection HafsR; intros HeqY HeqAR HeqlR;
  destruct_list_easy lR dR; try (injection HeqlR; intros);
  simpl in HprodR; specialize_Forall_H HprodR;
(* Remove combinations of introduction rules where the formulae can't match *)
  let HeqipsA := fresh "HeqipsA" in
  pose proof HeqAR as HeqipsA; rewrite HeqAL in HeqipsA;
  try discriminate; try injection HeqipsA; intros;
  spec_list HnocutL; spec_list HnocutR.

(* (* Old version of prep_C8 *)
Ltac auto_C8 :=
  let A := fresh "A" in let dt := fresh "dt" in
  let Hpro := fresh "Hpro" in let Hproup := fresh "Hproup" in
  let Hproup0 := fresh "Hproup" in let Hproup1 := fresh "Hproup" in
  let HproL := fresh "HproL" in let HproR := fresh "HproR" in
  let Hcut := fresh "Hcut" in let Hnocut := fresh "Hnocut" in
  let HyL := fresh "HyL" in let HnL := fresh "HnL" in
  let HyR := fresh "HyR" in let HnR := fresh "HnR" in
  let HLP := fresh "HLP" in let HRP := fresh "HRP" in
  let Heqr := fresh "Heqr" in let Hneqr := fresh "Hneqr" in
  intros A dt Hpro Hcut Hnocut; destruct Hcut as [HLP HRP];
  destruct dt as [|s r l]; [contradict Hpro; apply not_proper_Unf|];
  destruct (rule_eq_dec r CUT) as [Heqr|Hneqr];
    [|exists (Der s r l); split; [assumption | split; [reflexivity|]];
      apply (allDT_impl _ _ (nocut_impl_cut _)); apply allDT_Next; tauto];
  destruct (LP_dec l A) as [HyL|HnL];
    try (exfalso; let H := fresh "H" in destruct HLP as [H|]; try contradiction;
      destruct H as (ant & r' & l' & br & H); specialize (HnL ant r' l' br); tauto);
  destruct (RP_dec l A) as [HyR|HnR];
    try (exfalso; let H := fresh "H" in destruct HRP as [H|]; try contradiction;
      destruct H as (suc & bl & r' & l' & H); specialize (HnR suc bl r' l'); tauto);
  destruct HyL as (X & rL & lL & br & HLeql & HfmlrL);
    destruct HyR as (Y & bl & rR & lR & HReql & HfmlrR);
  rewrite HReql in HLeql; injection HLeql; intros Heqbr Heqbl;
  rewrite Heqbl in HReql; clear HLeql Heqbr Heqbl;
  let Heql := fresh "Heql" in rename HReql into Heql;
  pose proof (properUp Hpro) as Hproup; rewrite Heql in Hproup;
  specialize_Forall_H Hproup;
  rename Hproup0 into HproL; rename Hproup1 into HproR;
  rewrite Heql in Hnocut;
  let Hexr := fresh "Hexr" in
  let Hwfr := fresh "Hwfr" in
  let Hprems := fresh "Hprems" in
  let Hexrup := fresh "Hexrup" in
  let Hwfrup := fresh "Hwfrup" in
  destruct Hpro as (Hexr, (Hwfr, Hprems)); rewrite allDT_Next in Hwfr, Hexr;
  destruct Hwfr as [Hwfr Hwfrup]; destruct Hexr as [Hexr Hexrup];
  rewrite Heql in Hexrup;
  simpl in Hwfr; rewrite Heqr, Heql in Hwfr;
  apply ruleInst_ruleSubst in Hwfr; destruct Hwfr as [pfs Hpfs];
  injection Hpfs; intros Heqs HeqY _ _ HeqX;
  rewrite <- HeqX, <- HeqY in Heqs; clear HeqY HeqX;
  rewrite Heqs; simpl;
  destruct Hexrup as [ [HrLin _] [ [HrRin _] _] ];
  unfold exr in HrLin, HrRin;
  unfold allNextDTs, allDTs in Hnocut;
  rewrite <- Forall_fold_right, Forall_forall in Hnocut; specialize_list;
  let HnocutL := fresh "HnocutL" in let HnocutR := fresh "HnocutR" in
  match goal with | H : allDT nocut (Der _ rL _) |- _ =>
  pose proof (allDT_up_forall H) as HnocutL; clear H end;
  match goal with | H : allDT nocut (Der _ rR _) |- _ =>
  pose proof (allDT_up_forall H) as HnocutR; clear H end;
  (* Consider all possible combinations of rules
     while removing those without formula variables at right places *)
  dec_destruct_List_In (@eqdec rule _) rL;
  let HeqrL := fresh "HeqrL" in
  match goal with
  | H : rL = _ |- _ =>
      rename H into HeqrL; rewrite HeqrL in *; simpl in HfmlrL;
      try (unfold strIsFml in HfmlrL;
           rewrite (isVar_iff_isVar_cpt FS) in HfmlrL;
           unfold isVar_cpt in HfmlrL; simpl Var_dec in HfmlrL;
           cbv iota in HfmlrL; contradiction)
  end;
  dec_destruct_List_In (@eqdec rule _) rR;
  let HeqrR := fresh "HeqrR" in
  match goal with
  | H : rR = _ |- _ =>
      rename H into HeqrR; rewrite HeqrR in *; simpl in HfmlrR;
      try (unfold strIsFml in HfmlrR;
           rewrite (isVar_iff_isVar_cpt FS) in HfmlrR;
           unfold isVar_cpt in HfmlrR; simpl Var_dec in HfmlrR;
           cbv iota in HfmlrR; contradiction)
  end;
  (* Remove incompatible rules *)
  pose proof (proper_root _ _ HproL) as HwfrL; destruct HwfrL as [_ HwfrL];
  apply ruleInst_ruleSubst in HwfrL; destruct HwfrL as [afsL HafsL];
  try (match type of HeqrL with rL = ?rho => unfold rho in HafsL end);
  let HeqAL := fresh "HeqAL" in let HeqX := fresh "HeqX" in
  let HeqlL := fresh "HeqlL" in let dL := fresh "dL" in
  injection HafsL; intros HeqAL HeqX HeqlL;
  destruct_list_easy lL dL; try (injection HeqlL; intros);
  pose proof (properUp HproL) as HprodL; simpl in HprodL; specialize_Forall_H HprodL;
  pose proof (proper_root _ _ HproR) as HwfrR; destruct HwfrR as [_ HwfrR];
  apply ruleInst_ruleSubst in HwfrR; destruct HwfrR as [afsR HafsR];
  try (match type of HeqrR with rR = ?rho => unfold rho in HafsR end);
  let HeqAR := fresh "HeqAR" in let HeqY := fresh "HeqY" in
  let HeqlR := fresh "HeqlR" in let dR := fresh "dR" in
  injection HafsR; intros HeqY HeqAR HeqlR;
  destruct_list_easy lR dR; try (injection HeqlR; intros);
  pose proof (properUp HproR) as HprodR; simpl in HprodR; specialize_Forall_H HprodR;
  (* Last details *)
  let HeqipsA := fresh "HeqipsA" in
  pose proof HeqAR as HeqipsA; rewrite HeqAL in HeqipsA;
  try discriminate; try injection HeqipsA; intros;
  move HnocutL at bottom; move HnocutR at bottom;
  specialize_list; try specialize_list.
*)
