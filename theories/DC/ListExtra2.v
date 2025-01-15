Require Import String.
Require Import List ListDec ListSet SetoidList Decidable.
Import ListNotations.
Require Import ListSetNotations.
Require Import Bool.
Require Import Permutation.
Require Import Arith.
Require Import Wellfounded.
Require Import Datatypes.
Require Import ssrbool.

Require Import Recdef.
Require Import Lia.
Require Import Ring.

Require Import Tactics.
Require Import EqDec.
Require Import ListExtra1.

Section NTPower.

  Context {A : Type}.
  Context `{AED : EqDec A}.

  Definition nt_power_mset (l : list A) : list (list A) :=
    listminus (power_mset l) [[]; l]. 

  Lemma power_mset_max_length (l' l : list A) :
    In l (power_mset l') -> length l = length l' -> l = l'.
  Proof.
    revert l. induction l'; intros l Hinl Hlen.
    - destruct Hinl; try contradiction. now apply eq_sym.
    - simpl in Hinl. rewrite in_app_iff in Hinl.
      destruct Hinl as [Hinl|Hinl]. 
      + apply in_map_iff in Hinl.
        destruct Hinl as [sl [Heqsl Hinsl]].
        specialize (IHl' sl Hinsl).
        rewrite <- IHl'; try now apply eq_sym.
        rewrite <- Heqsl in Hlen. simpl in Hlen. lia.
      + exfalso. cut (length l <= length l').
        simpl in Hlen. lia.
        apply mset_incl_length, power_mset_all.
        apply (In_InA _). assumption.
  Qed.

  Lemma nt_power_mset_all (l' l : list A) :
    (mset_incl l l' /\ length l <> 0 /\ length l <> length l') <-> InA mset_eq l (nt_power_mset l').
  Proof.
    split.
    - intros [Hinc [Hlen0 Hlenl']].
      apply power_mset_all in Hinc.
      rewrite InA_alt in Hinc |- *.
      destruct Hinc as [sl [Hmeqsl Hinsl]].
      exists sl. split; try assumption.
      apply in_listminus_iff. split; try assumption.
      intros [H|[H|]]; try contradiction;
        rewrite <- H in Hmeqsl; apply mset_eq_length in Hmeqsl; contradiction.
    - intro HInA. apply InA_alt in HInA.
      destruct HInA as [sl [Hmeqsl Hinsl]].
      apply in_listminus_iff in Hinsl.
      destruct Hinsl as [Hinsl Hninsl].
      split; try split.
      + apply power_mset_all. apply InA_alt.
        exists sl. tauto.
      + contradict Hninsl. left.
        apply mset_eq_length in Hmeqsl. rewrite Hninsl in Hmeqsl.
        apply eq_sym in Hmeqsl. apply eq_sym.
        apply length_zero_iff_nil in Hmeqsl. assumption.
      + contradict Hninsl. right. left.
        apply mset_eq_length in Hmeqsl. rewrite Hninsl in Hmeqsl.
        apply eq_sym. apply power_mset_max_length; try assumption.
        now apply eq_sym.
  Qed.

End NTPower.


Section FoldRight.
  
  Context {A B C D : Type}.
  Context `{AED : EqDec A}.

  Definition app2 (p1 p2 : list A * list B) : list A * list B :=
    ((fst p1) ++ (fst p2), (snd p1) ++ (snd p2)).

  Definition app3 (p1 p2 : list A * list B * list C) : list A * list B * list C :=
    (app2 (fst p1) (fst p2), (snd p1) ++ (snd p2)).

  Lemma list_2_elems_dec : forall (l : list A),
      {a & {b & l = [a; b]} } + {forall a b, l <> [a; b]}.
  Proof.
    intro l.
    destruct l as [|a l]; try (right; intros; intro; discriminate).
    destruct l as [|b l]; try (right; intros; intro; discriminate).
    destruct l;try (right; intros; intro; discriminate).
    left. exists a, b. reflexivity.
  Defined.

  Lemma map_id (l : list A) : map id l = l.
  Proof.
    induction l.
    - simpl. reflexivity.
    - simpl. unfold id at 1. rewrite IHl. reflexivity.
  Qed.

  Lemma app_eq_nil_iff (l l' : list A) : l ++ l' = [] <-> l = [] /\ l' = [].
  Proof.
    split; try apply app_eq_nil.
    intros [Hl Hl']. rewrite Hl, Hl'. reflexivity.
  Qed.

  Lemma dec_list_eq : forall (l l' : list A), decidable (l = l').
  Proof. intros l l'. unfold decidable. destruct (list_eq_dec eqdec l l'); tauto. Qed.

  Lemma Forall_rw_fold_right [f g : B -> C] [h : C -> A -> A] [a : A] [l : list B] :
    Forall (fun x => f x = g x) l ->
    fold_right (fun x => h (f x)) a l = fold_right (fun x => h (g x)) a l.
  Proof.
    intro Hall. induction Hall.
    - simpl. reflexivity.
    - simpl. rewrite H, IHHall. reflexivity.
  Qed.

  Lemma fold_right_id (l : list B) (a : A) :
    fold_right (fun _ b => b) a l = a.
  Proof.
    induction l.
    - simpl. reflexivity.
    - simpl. apply IHl.
  Qed.

  Lemma in_map_inv_sig {f : B -> A} {l : list B} {y : A} :
    List.In y (map f l) -> {x : B | f x = y /\ List.In x l}.
  Proof.
    intro H. induction l; try contradiction.
    destruct (eqdec (f a) y) as [Heq|Hneq].
    - exists a. simpl. tauto.
    - destruct (in_dec eqdec y (map f l)) as [Hin|Hnin];
        try (exfalso; destruct H; contradiction).
      destruct (IHl Hin) as [x Hx]. exists x. simpl. tauto.
  Defined.

  Lemma fold_right_cons {l : list A} :
    fold_right (fun x => cons x) [] l = l.
  Proof.
    induction l; try reflexivity. simpl. rewrite IHl. reflexivity.
  Qed.

  Lemma fold_right_map (f : B -> C -> C) (g : A -> B) (c : C) (l : list A) :
    fold_right (fun x => f (g x)) c l = fold_right (fun x => f x) c (map g l).
  Proof.
    induction l; try reflexivity. simpl. rewrite IHl. reflexivity.
  Qed.

  Lemma fold_right_app_incl {a : list A} {l : list (list A)} :
    List.In a l -> incl a (fold_right (fun x => app x) [] l).
  Proof.
    intro Hin. induction l as [|b l]; try contradiction.
    simpl. destruct Hin as [Heq|Hin].
    - rewrite Heq. apply incl_appl, incl_refl.
    - apply incl_appr. apply IHl. assumption.
  Qed.

  Lemma Forall_incl_fold_right_incl {l : list (list A)} {l' : list A} :
    Forall (fun a => incl a l') l -> incl (fold_right (fun a => app a) [] l) l'.
  Proof.
    intro H. induction l; try apply incl_nil_l.
    simpl. pose proof (Forall_inv H). pose proof (Forall_inv_tail H).
    apply incl_app; try assumption. apply IHl. assumption.
  Qed.

  Lemma In_fold_right_app {l : list A} {f : A -> list B} {b : B} :
    In b (fold_right (fun x => app (f x)) [] l) -> exists x, In x l /\ In b (f x).
  Proof.
    induction l; simpl; try tauto.
    intro H. rewrite in_app_iff in H. destruct H as [H|H].
    - exists a. split; try now left. assumption.
    - specialize (IHl H). destruct IHl as [x [Hinx Hinb]].
      exists x. split; try now right. assumption.
  Qed.

  Lemma In_fold_right_app_iff {l : list A} {f : A -> list B} {b : B} :
    In b (fold_right (fun x => app (f x)) [] l) <-> exists x, In x l /\ In b (f x).
  Proof.
    split; try apply In_fold_right_app.
    intros [x [Hinx Hinb]]. induction l; try contradiction.
    simpl. rewrite in_app_iff. destruct Hinx as [Hx|Hx].
    - left. rewrite Hx. assumption.
    - right. apply IHl. assumption.
  Qed.

  Lemma In_fold_right_app_iff' {l : list A} {f : A -> list B} (l' : list B) :
    l' = fold_right (fun x => app (f x)) [] l ->
      forall b, In b l' <-> exists x, In x l /\ In b (f x).
  Proof.
    intros Heql' b. rewrite Heql'. apply In_fold_right_app_iff.
  Qed.
  
  Lemma bc_incl_fold_right_app_bc (l : list A) (bc : list B) (f : A -> list B) :
    bc ⊆ (fold_right (fun x => app (f x)) bc l).
  Proof.
    induction l.
    - simpl. apply incl_refl.
    - simpl. apply incl_appr. assumption.
  Qed.

  Lemma In_fold_right_app_bc {l : list A} {f : A -> list B} {bc : list B} {b : B} :
    In b (fold_right (fun x => app (f x)) bc l) -> (exists x, In x l /\ In b (f x)) \/ b ∈ bc.
  Proof.
    induction l; simpl; try tauto.
    intro H. rewrite in_app_iff in H. destruct H as [H|H].
    - left. exists a. split; try now left. assumption.
    - specialize (IHl H). destruct IHl as [[x [Hinx Hinb]]|Hin].
      + left. exists x. split; try now right. assumption.
      + right. assumption.
  Qed.

  Lemma In_fold_right_app_bc_iff {l : list A} {f : A -> list B} {bc : list B} {b : B} :
    In b (fold_right (fun x => app (f x)) bc l) <-> (exists x, In x l /\ In b (f x)) \/ b ∈ bc.
  Proof.
    split; try apply In_fold_right_app_bc.
    intros [[x [Hinx Hinb]]|Hin].
    - induction l; try contradiction.
      simpl. rewrite in_app_iff. destruct Hinx as [Hx|Hx].
      + left. rewrite Hx. assumption.
      + right. apply IHl. assumption.
    - pose proof (bc_incl_fold_right_app_bc l bc f) as H.
      apply H. assumption.
  Qed.

  Lemma fold_right_cons_eq (f : B -> A -> A) (a0 : A) (b : B) (l : list B) :
    fold_right f a0 (b :: l) = f b (fold_right f a0 l).
  Proof. reflexivity. Qed.

End FoldRight.

Definition list_union {A B : Type} (l : list A) (f : A -> list B) : list B :=
  fold_right (fun x => app (f x)) [] l.

Lemma list_union_alt {A B : Type} (l : list A) (f : A -> list B) :
  list_union l f = fold_right (@app B) [] (map f l).
Proof. unfold list_union. apply fold_right_map. Qed.

Section ListUnion.

  Context {A B C D : Type}.

  Lemma union_map (l : list A) (f : A -> list B) :
    list_union l f = list_union (map f l) id.
  Proof.
    unfold list_union. unfold id. apply fold_right_map.
  Qed.

  Lemma In_union {l : list A} {f : A -> list B} {b : B} :
    In b (list_union l f) -> exists x, In x l /\ In b (f x).
  Proof. apply In_fold_right_app. Qed.
  
  Lemma In_union_iff {l : list A} {f : A -> list B} {b : B} :
    In b (list_union l f) <-> exists x, In x l /\ In b (f x).
  Proof. apply In_fold_right_app_iff. Qed.

End ListUnion.


Section ForallMore.
  
  Context {A B C D : Type}.
  Context `{AED : EqDec A}.

  Lemma sing_incl_in (x : A) (l : list A) : [x] ⊆ l -> x ∈ l.
  Proof.
    intro H. apply H. now left.
  Qed.

  Lemma Forall_mp {P Q : A -> Prop} {l : list A} :
    Forall P l -> Forall (fun x => P x -> Q x) l -> Forall Q l.
  Proof.
    intros HP HPQ. induction l; try constructor 1.
    inversion HP. inversion HPQ. constructor 2. 
    - apply H5. assumption.
    - apply IHl; assumption.
  Qed.

  Lemma Forall_and_iff {P Q : A -> Prop} {l : list A} :
    Forall (fun x : A => P x /\ Q x) l <-> Forall P l /\ Forall Q l.
  Proof.
    split. apply Forall_and_inv. intro H. apply Forall_and; tauto.
  Qed.

  Lemma Forall_iff : forall {P Q : A -> Prop}, (forall a, P a <-> Q a) ->
    forall l, Forall P l <-> Forall Q l.
  Proof.
    intros P Q HPQ l. split; apply Forall_impl; intro a; apply HPQ.
  Qed.

  Lemma Forall_cons_iff {P : A -> Prop} {l : list A} {a : A} :
    Forall P (a :: l) <-> P a /\ Forall P l.
  Proof.
    split; try (intro; apply Forall_cons; tauto).
    intro H. split; [apply (Forall_inv H) | apply (Forall_inv_tail H)].
  Qed.

  Lemma Forall_one {P : A -> Prop} {a : A} : P a -> Forall P [a].
  Proof. exact (fun H => Forall_cons _ H (Forall_nil _)). Qed.

  Inductive ForallT (P : A -> Type) : list A -> Type :=
  | ForallT_nil : ForallT P []
  | ForallT_cons : forall {x l}, P x -> ForallT P l -> ForallT P (x::l).

  Lemma ForallT_inv {P : A -> Type} {a : A} {l : list A} : ForallT P (a :: l) -> P a.
  Proof. intro H. inversion H. assumption. Defined.

  Lemma ForallT_inv_tail {P : A -> Type} {a : A} {l : list A} : ForallT P (a :: l) -> ForallT P l.
  Proof. intro H. inversion H. assumption. Defined.

  Lemma ForallT_forall {P : A -> Type} :
    forall l : list A, ForallT P l <+> (forall x, List.In x l -> P x).
  Proof.
    split.
    - intro H. induction l; try contradiction.
      intros x Hx. inversion H. clear H2 H1 l0 x0. rename X into HPa, X0 into HPl.
      destruct (eqdec a x) as [Heq|Hneq]; try now rewrite <- Heq.
      destruct (in_dec eqdec x l) as [Hin|Hnin]; try now apply IHl.
      exfalso. simpl in Hx. tauto.
    - intro H. induction l; try constructor.
      + apply H. now left.
      + apply IHl. intros x Hx. apply H. now right.
  Defined.

  Lemma ForallT_mp {P Q : A -> Type} {l : list A} :
    ForallT P l -> ForallT (fun x => P x -> Q x) l -> ForallT Q l.
  Proof.
    intros HP HPQ. induction l; try constructor 1.
    inversion HP. inversion HPQ. clear H3 H2 l1 x0 H1 H0 l0 x.
    rename X into HPa, X0 into HPl, X1 into HPaQa, X2 into HPQl.
    constructor 2.
    - apply HPaQa. assumption.
    - apply IHl; assumption.
  Defined.

  Lemma ForallT_mp_dep {P : B -> A -> Type} {l : list A} (b : B) :
    ForallT (fun x => forall y, P y x) l -> ForallT (P b) l.
  Proof.
    intros HP. induction l; try constructor.
    - apply (ForallT_inv HP).
    - apply IHl. apply (ForallT_inv_tail HP).
  Defined.

  Lemma ForallT_act {P Q : A -> Type} {l : list A} (f : forall x, P x -> Q x) :
    ForallT P l -> ForallT Q l.
  Proof.
    intro H. apply (ForallT_mp H). induction l; try constructor.
    exact (f a). inversion H. apply IHl. assumption.
  Qed.
  
  Lemma ForallT_act_iff {P Q : A -> Type} {l : list A} :
      (forall x : A, P x <+> Q x) -> ForallT P l <+> ForallT Q l.
  Proof.
    intro H. split; apply ForallT_act; intro x; apply H.
  Defined.

  Lemma ForallT_sig_elim {R : A -> B -> Prop} {l : list A} :
    ForallT (fun x => {y : B | R x y}) l -> {l' | Forall2 R l l'}.
  Proof.
    intro H. induction l; try (exists []; constructor).
    inversion H. clear H2 H1 l0 x. destruct X as [b Rab]. rename X0 into Hl.
    destruct (IHl Hl) as [l' Rll']. exists (b :: l').
    constructor; assumption.
  Defined.

  Lemma Forall_ForallT {P : A -> Prop} : forall l : list A, Forall P l <+> ForallT P l.
  Proof.
    split.
    - intro H. apply ForallT_forall, Forall_forall. assumption.
    - intro H. apply Forall_forall, ForallT_forall. assumption.
  Defined.

  Lemma Forall2_and_inv {R1 R2 : A -> B -> Prop} {l : list A} {l' : list B} :
    Forall2 (fun x y => R1 x y /\ R2 x y) l l' -> Forall2 R1 l l' /\ Forall2 R2 l l'.
  Proof.
    intro H. induction H; auto. split; constructor; tauto.
  Qed.

  Lemma Forall2_Forall_r {P : B -> Prop} {l : list A} {l' : list B} :
    Forall2 (fun x y => P y) l l' -> Forall P l'.
  Proof.
    intro H. induction H; auto.
  Qed.

  Lemma Forall2_map_iff {R : C -> D -> Prop} {f : A -> C} {g : B -> D} {l : list A} {l' : list B} :
    Forall2 (fun x y => R (f x) (g y)) l l' <-> Forall2 R (map f l) (map g l').
  Proof.
    split.
    - intro H. induction H; [constructor | constructor; assumption].
    - intro H. revert l' H. induction l.
      + intros l' H. destruct l'; [constructor | inversion H].
      + intros l' H. destruct l'; try inversion H.
        constructor; [idtac | apply IHl]; assumption.
  Qed.

  Lemma Forall2_eq_same {l : list A} : Forall2 eq l l.
  Proof.
    induction l.
    - constructor.
    - constructor; tauto.
  Qed.

  Lemma Forall2_eq_iff {l l' : list A} : Forall2 eq l l' <-> l = l'.
  Proof.
    split.
    - intro H. induction H; try reflexivity. rewrite H, IHForall2. reflexivity.
    - intro H. rewrite <- H. apply Forall2_eq_same.
  Qed.

  Lemma Forall2_sig_l {R : B -> A -> Prop} {l : list B} {l' : list A} :
    Forall2 R l l' -> forall x', List.In x' l' -> {x | List.In x l /\ R x x'}.
  Proof.
    intros Hall2. pose proof (Forall2_length Hall2) as Hlen. revert Hall2. pattern l, l'.
    revert l l' Hlen. apply list_biind; try (simpl; tauto).
    intros a l b l' IH Hall2 x' H. apply Forall2_cons_iff in Hall2.
    destruct Hall2 as [Hab Hall2]. destruct (eqdec b x') as [Heq|Hneq].
    - exists a. rewrite <- Heq. simpl. tauto.
    - destruct (in_dec eqdec x' l') as [Hin|Hnin]; try (exfalso; destruct H; tauto).
      destruct (IH Hall2 x' Hin) as [x Hx]. exists x. simpl. tauto.
  Defined.

  Lemma Forall2_iff : forall {R S : A -> B -> Prop}, (forall a b, R a b <-> S a b) ->
    forall l l', Forall2 R l l' <-> Forall2 S l l'.
  Proof.
    intros R S HRS l l'. split; apply Forall2_impl; intro a; apply HRS.
  Qed.


  Inductive ExistsT (P : A -> Type) : list A -> Type :=
  | ExistsT_cons_hd : forall (x : A) (l : list A), P x -> ExistsT P (x :: l)
  | Exists_cons_tl : forall (x : A) (l : list A), ExistsT P l -> ExistsT P (x :: l).

  Lemma ExistsT_exists {P : A -> Type} (l : list A) :
    ExistsT P l <+> {a & In a l & P a}.
  Proof.
    split.
    - intro Hex. induction Hex.
      + exists x; [now left | assumption].
      + destruct IHHex as [a Hina HPa].
        exists a; [now right | assumption].
    - intros [a Hina HPa]. induction l as [|x l]; try contradiction.
      destruct (eqdec x a) as [Heq|Hneq].
      + rewrite Heq. constructor 1. assumption.
      + constructor 2. apply IHl. destruct (in_dec eqdec a l); try assumption.
        destruct Hina; contradiction.
  Defined.

End ForallMore.


Lemma in_if_in_dec_eq {A B : Type} {Aeq_dec : forall x y : A, {x = y} + {x <> y}} (a : A) (l : list A) :
  a ∈ l -> forall (b b' : B), (if in_dec Aeq_dec a l then b else b') = b.
Proof.
  intro H. destruct (in_dec Aeq_dec a l). reflexivity. contradiction.
Qed.

Lemma fold_right_in_dec_incl {A B C : Type} {EDA : EqDec A} (l l' : list A) (op : B -> C -> C) (c0 : C) (f g : A -> B) :
  l ⊆ l' ->
  fold_right (fun x => op (if in_dec eqdec x l' then f x else g x)) c0 l
  = fold_right (fun x => op (if in_dec eqdec x l then f x else g x)) c0 l.
Proof.
  revert l'. induction l; try reflexivity.
  intros l' H. rewrite ! fold_right_cons_eq.
  rewrite ! in_if_in_dec_eq.
  rewrite IHl. rewrite <- (IHl (a :: l)). reflexivity.
  - apply incl_tl, incl_refl.
  - eapply incl_tran; try apply H. apply incl_tl, incl_refl.
  - now left.
  - apply H. now left.
Qed.

Lemma fold_right_in_dec {A B C : Type} {EDA : EqDec A} (op : B -> C -> C) (f g : A -> B) (c0 : C) (l : list A) :
  fold_right (fun x => op (if (in_dec eqdec x l) then f x else g x)) c0 l
  = fold_right (fun x => op (f x)) c0 l.
Proof.
  induction l; try reflexivity.
  rewrite fold_right_cons_eq. rewrite fold_right_in_dec_incl.
  rewrite IHl. rewrite in_if_in_dec_eq. reflexivity.
  - now left.
  - apply incl_tl, incl_refl.
Qed.

Lemma union_in_dec  {A B : Type} {EDA : EqDec A} (f g : A -> list B) (l : list A) :
  list_union l (fun x => if in_dec eqdec x l then f x else g x) = list_union l f.
Proof. apply fold_right_in_dec. Qed.

Lemma fold_right_in_dec_map {A B : Type} {EDA : EqDec A} (f : A -> B) (l : list A) :
  fold_right (fun x => app (if (in_dec eqdec x l) then [f x] else [])) [] l
  = map f l.
Proof.
  induction l; try reflexivity.
  rewrite fold_right_cons_eq. rewrite fold_right_in_dec_incl.
  rewrite IHl. rewrite in_if_in_dec_eq. reflexivity.
  - now left.
  - apply incl_tl, incl_refl.
Qed.

Lemma union_in_dec_map  {A B : Type} {EDA : EqDec A} (f : A -> B) (l : list A) :
  list_union l (fun x => if in_dec eqdec x l then [f x] else []) = map f l.
Proof. apply fold_right_in_dec_map. Qed.

Lemma in_zip_pair_23_sig_1 {A B C : Type} {BED : EqDec B} {CED : EqDec C} (lA : list A) (lB : list B) (lC : list C) (b : B) (c : C) :
  length lA = length lB -> length lB = length lC ->
  (b, c) ∈ zip pair lB lC -> {a | (a, b, c) ∈ zip pair (zip pair lA lB) lC}.
Proof.
  revert lA lC. induction lB as [|b' lB]; try contradiction.
  intros lA lC HlenAB HlenBC Hbc.
  destruct lA as [|a' lA]; try discriminate.
  destruct lC as [|c' lC]; try discriminate.
  simpl in Hbc. destruct (eqdec (b', c') (b, c)) as [Heq|Hneq];
    [|destruct (in_dec eqdec (b, c) (zip pair lB lC)) as [Hin|Hnin]].
  - exists a'. injection Heq. intros Heqc Heqb. rewrite <- Heqc, <- Heqb.
    simpl. left. reflexivity.
  - simpl in HlenAB, HlenBC.
    injection HlenAB. intro HlenAB'.
    injection HlenBC. intro HlenBC'.
    destruct (IHlB lA lC) as [a Habc]; try assumption.
    exists a. simpl. right. assumption.
  - exfalso. destruct Hbc; contradiction.
Defined.

Lemma zip_pair_bij_fst_sig {A B : Type} {AED : EqDec A} (lA : list A) (lB : list B) :
  length lA = length lB -> forall a, a ∈ lA -> {p | p ∈ zip pair lA lB /\ fst p = a}.
Proof.
  intro H. pattern lA, lB. revert lA lB H. apply list_biind; try contradiction.
  intros a lA b lB IH a' Ha'.
  destruct (eqdec a a') as [Heqa|Hneqa];
    [|destruct (in_dec eqdec a' lA) as [Hin|Hnin]].
  - exists (a, b). simpl. tauto.
  - destruct (IH a' Hin) as [p Hp]. exists p. simpl. tauto.
  - exfalso. destruct Ha'; contradiction.
Qed.

Lemma zip_pair_bij_snd_sig {A B : Type} {BED : EqDec B} (lA : list A) (lB : list B) :
  length lA = length lB -> forall b, b ∈ lB -> {p | p ∈ zip pair lA lB /\ snd p = b}.
Proof.
  intro H. pattern lA, lB. revert lA lB H. apply list_biind; try contradiction.
  intros a lA b lB IH b' Hb'.
  destruct (eqdec b b') as [Heqb|Hneqb];
    [|destruct (in_dec eqdec b' lB) as [Hin|Hnin]].
  - exists (a, b). simpl. tauto.
  - destruct (IH b' Hin) as [p Hp]. exists p. simpl. tauto.
  - exfalso. destruct Hb'; contradiction.
Qed.
  
Lemma Forall_eq_zip_pair {A : Type} (l l' : list A) :
  length l = length l' -> Forall (fun xy => fst xy = snd xy) (zip pair l l') -> l = l'.
Proof.
  intro Hlen. pattern l, l'. revert l l' Hlen.
  apply list_biind; [reflexivity|].
  intros a l a' l' IH Hall. simpl in Hall.
  apply Forall_cons_iff in Hall. destruct Hall as [Ha Hl].
  simpl in Ha. rewrite Ha. apply f_equal.
  apply IH. assumption.
Qed.  

Lemma Forall_zip_pair_map_fst {A B C : Type} (R : C -> B -> Prop) (f : A -> C) (l : list A) (l' : list B) :
  Forall (fun xy => R (f (fst xy)) (snd xy)) (zip pair l l') ->
  Forall (fun xy => R (fst xy) (snd xy)) (zip pair (map f l) l').
Proof.
  revert l'. induction l; intros l' H; [|destruct l' as [|a' l']];
    try apply Forall_nil.
   simpl in H |- *. apply Forall_cons_iff in H.
   destruct H as [Ha Hl]. apply Forall_cons; try assumption.
   apply IHl. assumption.
Qed.   


Lemma zip_pair_in_map_23 {A B B1 B2 : Type} (f : B -> B1) (g : B -> B2) (lA : list A) (lB : list B) (a : A) (b : B) :
  (a, b) ∈ zip pair lA lB -> (a, f b, g b) ∈ zip pair (zip pair lA (map f lB)) (map g lB).
Proof.
  revert lA. induction lB as [|b' lB]; intro lA;
    [simpl; rewrite zip_nil_r; contradiction|].
  destruct lA as [|a' lA]; try contradiction.
  simpl. intros [H|H].
  - injection H. intros Heqb Heqa. left. rewrite Heqa, Heqb. reflexivity.
  - right. apply IHlB. assumption.
Qed.

Lemma zip_pair_map_in_23_inv {A B B1 B2 : Type} (f : B -> B1) (g : B -> B2) (lA : list A) (lB : list B) (a : A) (b1 : B1) (b2 : B2) :
  (a, b1, b2) ∈ zip pair (zip pair lA (map f lB)) (map g lB) ->
  exists b, b1 = f b /\ b2 = g b /\ (a, b) ∈ zip pair lA lB.
Proof.
  revert lA. induction lB as [|b lB]; intro lA;
    [simpl; rewrite zip_nil_r; contradiction|].
  destruct lA as [|a' lA]; try contradiction.
  simpl. intros [H|H].
  - injection H. intros Heqg Heqf Heqa. exists b.
    repeat split; try (apply eq_sym; assumption).
    left. rewrite Heqa. reflexivity.
  - specialize (IHlB lA H). destruct IHlB as [b' Hb'].
    exists b'. repeat split; tauto.
Qed.
  

Lemma fold_right_in_dec_incl_zip_pair_fst {A A' B C : Type} {EDA : EqDec A}
(op : B -> C -> C) (f g : A * A' -> B) (c0 : C) (l l0 : list A) (l' : list A') :
  l ⊆ l0 ->
  fold_right (fun x => op (if in_dec eqdec (fst x) l0 then f x else g x)) c0 (zip pair l l')
  = fold_right (fun x => op (if in_dec eqdec (fst x) l then f x else g x)) c0 (zip pair l l').
Proof.
  revert l0 l'. induction l; try reflexivity.
  intros l0 l' H.
  destruct l' as [|a' l']; try reflexivity. simpl zip.
  rewrite ! fold_right_cons_eq.
  rewrite ! in_if_in_dec_eq.
  rewrite IHl. rewrite <- (IHl (a :: l)). reflexivity.
  - apply incl_tl, incl_refl.
  - eapply incl_tran; try apply H. apply incl_tl, incl_refl.
  - now left.
  - apply H. now left.
Qed.

Lemma fold_right_in_dec_incl_zip_pair_snd {A A' B C : Type} {EDA : EqDec A'}
(op : B -> C -> C) (f g : A * A' -> B) (c0 : C) (l : list A) (l' l0 : list A') :
  l' ⊆ l0 ->
  fold_right (fun x => op (if in_dec eqdec (snd x) l0 then f x else g x)) c0 (zip pair l l')
  = fold_right (fun x => op (if in_dec eqdec (snd x) l' then f x else g x)) c0 (zip pair l l').
Proof.
  revert l0 l. induction l' as [|a' l' IHl'];
    try (intros; rewrite zip_nil_r; reflexivity).
  intros l0 l H.
  destruct l as [|a l]; try reflexivity. simpl zip.
  rewrite ! fold_right_cons_eq.
  rewrite ! in_if_in_dec_eq.
  rewrite IHl'. rewrite <- (IHl' (a' :: l')). reflexivity.
  - apply incl_tl, incl_refl.
  - eapply incl_tran; try apply H. apply incl_tl, incl_refl.
  - now left.
  - apply H. now left.
Qed.

Lemma fold_right_in_dec_zip_pair_fst {A A' B C : Type} {EDA : EqDec A}
(op : B -> C -> C) (f g : A * A' -> B) (c0 : C) (l : list A) (l' : list A') :
  fold_right (fun x => op (if (in_dec eqdec (fst x) l) then f x else g x)) c0 (zip pair l l')
  = fold_right (fun x => op (f x)) c0 (zip pair l l').
Proof.
  revert l'. induction l; try reflexivity.
  destruct l' as [|a' l']; try reflexivity. simpl zip.
  rewrite fold_right_cons_eq.
  rewrite fold_right_in_dec_incl_zip_pair_fst.
  rewrite IHl. rewrite in_if_in_dec_eq. reflexivity.
  - now left.
  - apply incl_tl, incl_refl.
Qed.

Lemma fold_right_in_dec_zip_pair_snd {A A' B C : Type} {EDA : EqDec A'}
(op : B -> C -> C) (f g : A * A' -> B) (c0 : C) (l : list A) (l' : list A') :
  fold_right (fun x => op (if (in_dec eqdec (snd x) l') then f x else g x)) c0 (zip pair l l')
  = fold_right (fun x => op (f x)) c0 (zip pair l l').
Proof.
  revert l'. induction l; try reflexivity.
  destruct l' as [|a' l']; try reflexivity. simpl zip.
  rewrite fold_right_cons_eq.
  rewrite fold_right_in_dec_incl_zip_pair_snd.
  rewrite IHl. rewrite in_if_in_dec_eq. reflexivity.
  - now left.
  - apply incl_tl, incl_refl.
Qed.

Lemma union_in_dec_zip_pair_fst {A A' B : Type} {EDA : EqDec A}
  (f g : A * A' -> list B) (l : list A) (l' : list A') :
  list_union (zip pair l l') (fun x => if in_dec eqdec (fst x) l then f x else g x)
  = list_union (zip pair l l') f.
Proof. apply fold_right_in_dec_zip_pair_fst. Qed.

Lemma union_in_dec_zip_pair_snd {A A' B : Type} {EDA' : EqDec A'}
  (f g : A * A' -> list B) (l : list A) (l' : list A') :
  list_union (zip pair l l') (fun x => if in_dec eqdec (snd x) l' then f x else g x)
  = list_union (zip pair l l') f.
Proof. apply fold_right_in_dec_zip_pair_snd. Qed.

Lemma map_fst_zip_pair {A B : Type} (l : list A) (l' : list B) :
  length l = length l' -> map fst (zip pair l l') = l.
Proof.
  revert l'. induction l; try reflexivity.
  intros l' Hlen. destruct l' as [|a' l']; try discriminate.
  simpl. apply f_equal. apply IHl.
  simpl in Hlen. injection Hlen. tauto.
Qed.

Definition distinct_all {A : Type} (ll : list (list A)) :=
  NoDupA (fun l l' => exists x, x ∈ l /\ x ∈ l') ll.

Lemma NoDup_union_distinct {A B : Type} (l : list A) (f : A -> list B) :
  NoDup (list_union l f) -> distinct_all (map f l).
Proof.
  intro H. induction l; [apply NoDupA_nil|].
  simpl. apply NoDupA_cons.
  - simpl in H. apply NoDup_app_distinct in H.
    intro Hctr. apply InA_alt in Hctr.
    destruct Hctr as [l' [[b [Hin1 Hin2]] Hinl']].
    apply (H _ Hin1). rewrite union_map.
    apply In_union_iff. exists l'. tauto.
  - apply IHl. simpl in H. apply NoDup_app_remove_l in H.
    assumption.
Qed.

Lemma union_empty {A B : Type} (l : list A) (f : A -> list B) (a : A) :
  a ∈ l -> list_union l f = [] -> f a = [].
Proof.
  induction l as [|a' l]; try contradiction.
  intros Ha H. simpl in H. apply app_eq_nil in H. destruct Ha as [Ha|Ha].
  - rewrite Ha in H. tauto.
  - apply IHl; tauto.
Qed.

Lemma NoDup_union {A B : Type} (l : list A) (f : A -> list B) (a : A) :
  a ∈ l -> NoDup (list_union l f) -> NoDup (f a).
Proof.
  intros Ha HND. induction l as [|a' l]; try contradiction.
  destruct Ha as [Ha|Ha].
  - rewrite Ha in HND. simpl in HND.
    apply NoDup_app_remove_r in HND.
    assumption.
  - simpl in HND. apply NoDup_app_remove_l in HND.
    apply IHl; assumption.
Qed.

Close Scope nat_scope.

Section ForallMore'.

  Context {A : Type}.
  Context `{AED : EqDec A}.
  
  Lemma ForallT_dec_E {P Q : A -> Type} (l : list A) :
    ForallT (fun x => P x + Q x) l -> ExistsT P l + ForallT Q l.
  Proof.
    intros Hdec. induction l; try (right; constructor; fail).
    pose proof (ForallT_inv Hdec) as Hdeca.
    pose proof (ForallT_inv_tail Hdec) as Hdecl.
    specialize (IHl Hdecl). destruct Hdeca as [HPa|HQa].
    - left. constructor 1. assumption.
    - destruct IHl as [HPl|HQl].
      + left. constructor; assumption.
      + right. constructor 2; assumption.
  Defined.

  Lemma ForallT_dec_F {P Q : A -> Type} (l : list A) :
    ForallT (fun x => P x + Q x) l -> ForallT P l + ExistsT Q l.
  Proof.
    intros Hdec. induction l; try (left; constructor; fail).
    pose proof (ForallT_inv Hdec) as Hdeca.
    pose proof (ForallT_inv_tail Hdec) as Hdecl.
    specialize (IHl Hdecl). destruct Hdeca as [HPa|HQa].
    - destruct IHl as [HPl|HQl].
      + left. constructor; assumption.
      + right. constructor 2. assumption.
    - right. constructor 1. assumption.
  Defined.

  Lemma ForallT_dec_EF {P Q : A -> Type} (ll : list (list A)) :
    ForallT (ForallT (fun x => P x + Q x)) ll ->
      ExistsT (ForallT P) ll + ForallT (ExistsT Q) ll.
  Proof.
    intros Hdec. induction ll as [|l ll]; try (right; constructor; fail).
    pose proof (ForallT_inv Hdec) as Hdecl.
    pose proof (ForallT_inv_tail Hdec) as Hdecll.
    specialize (IHll Hdecll). destruct (ForallT_dec_F l Hdecl) as [HPl|HQl].
    - left. constructor 1. assumption.
    - destruct IHll as [HPll|HQll].
      + left. constructor 2. assumption.
      + right. constructor; assumption.
  Defined.

  Lemma ForallT_dec_EEF {P Q : A -> Type} (lll : list (list (list A))) :
    ForallT (ForallT (ForallT (fun x => P x + Q x))) lll ->
      ExistsT (ExistsT (ForallT P)) lll +
      ForallT (ForallT (ExistsT Q)) lll.
  Proof.
    intros Hdec. induction lll as [|ll lll]; try (right; constructor; fail).
    pose proof (ForallT_inv Hdec) as Hdecll.
    pose proof (ForallT_inv_tail Hdec) as Hdeclll.
    specialize (IHlll Hdeclll). destruct (ForallT_dec_EF ll Hdecll) as [HPll|HQll].
    - left. constructor 1. assumption.
    - destruct IHlll as [HPlll|HQlll].
      + left. constructor 2. assumption.
      + right. constructor; assumption.
  Defined.

  
  Lemma ForallT_dec_E_sumbool {P Q : A -> Prop} (l : list A) :
    ForallT (fun x => {P x} + {Q x}) l -> ExistsT P l + ForallT Q l.
  Proof.
    intros Hdec. induction l; try (right; constructor; fail).
    pose proof (ForallT_inv Hdec) as Hdeca.
    pose proof (ForallT_inv_tail Hdec) as Hdecl.
    specialize (IHl Hdecl). destruct Hdeca as [HPa|HQa].
    - left. constructor 1. assumption.
    - destruct IHl as [HPl|HQl].
      + left. constructor; assumption.
      + right. constructor 2; assumption.
  Defined.

End ForallMore'.


Lemma Forall2_sig_r {A B} `{BED : EqDec B} {R : B -> A -> Prop} {l : list B} {l' : list A} :
  Forall2 R l l' -> forall x, List.In x l -> {x' | List.In x' l' /\ R x x'}.
Proof.
  intro H. apply Forall2_flip in H. apply Forall2_sig_l; assumption.
Defined.


Lemma ForallT_map : forall [A B : Type] (f : A -> B) (P : B -> Type) (l : list A),
    ForallT P (map f l) <+> ForallT (fun x : A => P (f x)) l.
Proof.
  intros A B f P l. split.
  - intro H. induction l; constructor; inversion H; try assumption.
    apply IHl. assumption.
  - intro H. induction H; constructor; assumption.
Defined.


Lemma all_msets_len {A : Type} (la : list A) (n : nat) :
  {ls | forall l, In l ls <-> length l = n /\ incl l la}.
Proof.
  induction n.
  - exists [[]]. intro l. split.
    + intro H. destruct H; try contradiction. rewrite <- H.
      split; [reflexivity | apply incl_nil_l].
    + intros [H _]. apply length_zero_iff_nil in H. now left.
  - destruct IHn as [ls Hls].
    exists (fold_right (fun l => app (map (fun x => x :: l) la)) [] ls). intro l. split.
    + intro H. destruct (In_fold_right_app H) as [l' [Hinl' Hinl]].
      rewrite in_map_iff in Hinl. destruct Hinl as [x [Heql Hinx]].
      specialize (Hls l'). destruct Hls as [Hls _]. specialize (Hls Hinl').
      destruct Hls as [Hlenl' Hincl']. rewrite <- Heql. split.
      * simpl. rewrite Hlenl'. reflexivity.
      * intros x0 Hx0. destruct Hx0 as [Hx0|Hx0]; try (now rewrite <- Hx0).
        apply Hincl'. assumption.
    + intros [Hlenl Hincl]. apply In_fold_right_app_iff.
      destruct l; try (simpl in Hlenl; discriminate).
      exists l. split.
      * apply Hls. simpl in Hlenl. split; try lia.
        eapply incl_tran; try apply Hincl. apply incl_tl, incl_refl.
      * rewrite in_map_iff. exists a. split; try reflexivity. apply Hincl. now left.
Defined.




(* Tactics on lists *)

Ltac specialize_Forall_H HF :=
  match type of HF with
  | Forall _ [] => clear HF
  | _ =>
      apply Forall_cons_iff in HF;
      match type of HF with
      | _ /\ Forall _ _ =>
          let H := fresh HF in destruct HF as [H HF]; specialize_Forall_H HF
      | _ => idtac
      end
  end.

Ltac specialize_Forall :=
  match goal with
  | [ HF : Forall _ _ |- _ ] => specialize_Forall_H HF
  end.

Ltac specialize_ForallT_H HF :=
  match type of HF with
  | ForallT _ [] => clear HF
  | _ =>
      let H := fresh HF in
      pose proof (ForallT_inv HF) as H;
      apply ForallT_inv_tail in HF;
      specialize_ForallT_H HF
  end.

Ltac specialize_list :=
  match goal with
  | Hall : forall x, List.In x _ -> _ |- _ => rewrite <- Forall_forall in Hall; specialize_Forall_H Hall
  end.


Ltac specialize_Forall2_H HF2 :=
  match type of HF2 with
  | Forall2 _ [] [] => clear HF2
  | _ =>
      apply Forall2_cons_iff in HF2;
      match type of HF2 with
      | _ /\ Forall2 _ _ _ =>
          let H := fresh in destruct HF2 as [H HF2]; specialize_Forall2_H HF2
      | _ => idtac
      end
  end.

Ltac NoDup_two :=
  let H := fresh in 
  apply NoDup_cons; [|apply NoDup_single];
  simpl; intros [H|H]; [discriminate|assumption].


Theorem not_and_iff_or_not [A B : Prop] : Decidable.decidable A -> ~ (A /\ B) <-> ~ A \/ ~ B.
Proof. intro dec. split; [now apply not_and | tauto]. Qed.


Lemma Some_eq_iff {A : Type} {x y : A} : Some x = Some y <-> x = y.
Proof.
  split.
  - intro H. injection H. tauto.
  - intro H. rewrite H. reflexivity.
Qed.


Lemma comp_disjunct {A : Type} {P : A -> Type} (Aeq_dec : eq_dec A) (a b : A) :
  P a -> P b -> forall x, x = a \/ x = b -> P x.
Proof.
  intros Pa Pb x Hx.
  destruct (Aeq_dec x a) as [Heq1|Hneq1];
    destruct (Aeq_dec x b) as [Heq2|Hneq2];
    try ((rewrite Heq1 || rewrite Heq2); assumption).
  simpl in Hx. exfalso. tauto.
Qed.

Lemma list_1_eq_iff {A : Type} {a b : A} : [a] = [b] <-> a = b.
Proof.
  split. intro H. now injection H. intro H. now rewrite H.
Qed.


Lemma eqb_swap_negb : forall b1 b2, eqb (negb b1) b2 = eqb b1 (negb b2).
Proof.
  intros b1 b2. destruct b1; destruct b2; reflexivity.
Qed.

Lemma eqb_true_r : forall b, eqb b true = b.
Proof.
  intro b. destruct b; reflexivity.
Qed.

Lemma eq_sym_iff {A : Type} : forall x y : A, x = y <-> y = x.
Proof. split; apply eq_sym; assumption. Qed.
