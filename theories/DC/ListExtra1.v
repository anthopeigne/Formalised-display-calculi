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
From AAC_tactics Require Import AAC.

Require Import Tactics.
Require Import EqDec.

Definition comp {A B C : Type} (g : B -> C) (f : A -> B) : A -> C := fun x => g (f x).
(*Notation "g ∘ f" := (compose g f).*)



Set Implicit Arguments.

Open Scope type_scope.

Definition wf_nat_ind {A : Type} (size : A -> nat) :=
  well_founded_induction_type (wf_inverse_image _ _ _ size Nat.lt_wf_0).


Section list_biind.
  Variables A B : Type.
  Variable P : list A -> list B -> Type.
  Hypothesis BC : P [] [].
  Hypothesis IH : forall (a : A) (l1 : list A) (b : B) (l2 : list B),
      P l1 l2 -> P (a :: l1) (b :: l2).

  Theorem list_biind : forall (l1 : list A) (l2 : list B), length l1 = length l2 -> P l1 l2.
  Proof.
    induction l1.
    - intros l2 H. apply eq_sym, length_zero_iff_nil in H. rewrite H. assumption.
    - intros l2 H. destruct l2; try discriminate.
      apply IH. apply IHl1. injection H. tauto.
  Defined.

End list_biind.

Unset Implicit Arguments.

Open Scope nat_scope.



Lemma in_some_dec {A B : Type} {EDB : EqDec B} (b : B) (l : list A) (f : A -> list B) :
  {a | a ∈ l & b ∈ f a} + {forall a, a ∈ l -> b ∉ f a}.
Proof.
  induction l as [|a' l]; try (right; tauto).
  destruct IHl as [[a Ha Hb]| H].
  - left. exists a; simpl; tauto.
  - destruct (in_dec eqdec b (f a')) as [Hb|Hb].
    + left. exists a'; simpl; tauto.
    + right. intros x [Hx|Hx].
      * rewrite <- Hx. assumption.
      * apply H. assumption.
Defined.


Lemma eq_dec_in_list [A : Type] (Aeq_dec : forall x y : A, {x = y} + {x <> y}) [P : A -> Type] [y : A] [ys : list A] [x : A] :
  x ∈ (y :: ys) -> ((x = y -> P x) -> (x ∈ ys -> P x) -> P x).
Proof.
  intros Hin Hy Hys.
  destruct (Aeq_dec x y) as [Heq|Hneq].
  - apply Hy. assumption.
  - apply not_eq_sym in Hneq. apply Hys.
    destruct Hin; [contradiction | assumption].
Defined.



Definition nxorb (b1 b2 : bool) : bool := if b1 then b2 else negb b2.

Lemma eqb_nxorb : forall b1 b2 b3, eqb (nxorb b1 b2) (nxorb b3 b2) = eqb b1 b3.
Proof. intros [|] [|] [|]; reflexivity. Qed.

Lemma eqb_nxorb_swap : forall b1 b2 b3, eqb (nxorb b1 b2) b3 = eqb b1 (nxorb b3 b2).
Proof. intros [|] [|] [|]; reflexivity. Qed.

Lemma nxorb_invol : forall b1 b2, nxorb (nxorb b1 b2) b2 = b1.
Proof. intros [|] [|]; reflexivity. Qed.


Section ListMore.

  Context {A B C D : Type}.
  Context `{AED : EqDec A}.


(* MISCELLANEOUS *)

  Lemma NoDup_single : forall a : A, NoDup [a].
  Proof.
    intro a. constructor; [apply in_nil|constructor].
  Qed.

  Lemma NoDupA_cons_inv (eqA : A -> A -> Prop) (x : A) (l : list A) :
    NoDupA eqA (x :: l) -> ~ InA eqA x l /\ NoDupA eqA l.
  Proof. intro H. inversion H. tauto. Qed.

  Lemma in_singleton_eq : forall (x a : A), In x [a] -> a = x.
  Proof.
    intros x a H. destruct H as [H|H].
    - assumption.
    - contradiction.
  Qed.

  Lemma incl_cons_cons (l l' : list A) (a : A) : incl l l' -> incl (a :: l) (a :: l').
  Proof.
    intro H. apply incl_cons; try now left. apply incl_tl. assumption.
  Qed.

  Lemma not_in_map (f : A -> B) (l : list A) (x : A) :
    ~ In (f x) (map f l) -> ~ In x l.
  Proof.
    intros Hnin. contradict Hnin. apply in_map. assumption.
  Qed.

  Lemma not_In_incl_drop_hd (l l' : list A) (a : A) :
    ~ In a l -> incl l (a :: l') -> incl l l'.
  Proof.
    intros Hnin Hinc x Hx. specialize (Hinc x Hx).
    destruct Hinc as [Heq|Hinc]; try assumption.
    contradict Hnin. rewrite Heq. assumption.
  Qed.

  Lemma app_singl_eq_cons (l : list A) (a : A) : a :: l = [a] ++ l.
  Proof. reflexivity. Qed.


(* ERASE *)

  Fixpoint listerase (l1 l2 : list A) : list A :=
    match l2 with
    | []      => l1
    | a :: l2' => erase a (listerase l1 l2')
    end.

  Lemma count_In : forall (l : list A) (x : A), In x l <-> count l x > 0.
  Proof. apply count_occ_In. Qed.

  Lemma count_not_In : forall (l : list A) (x : A), ~ In x l <-> count l x = 0.
  Proof. apply count_occ_not_In. Qed.
  
  Lemma Permutation_count : forall (l1 l2 : list A),
      Permutation l1 l2 <-> (forall x : A, count l1 x = count l2 x).
  Proof. apply Permutation_count_occ. Qed.

  Lemma NoDup_count : forall (l : list A), NoDup l <-> (forall x : A, count l x <= 1).
  Proof. apply NoDup_count_occ. Qed.

  Lemma count_app : forall (l1 l2 : list A) (x : A),
      count (l1 ++ l2) x = (count l1 x + count l2 x).
  Proof. apply count_occ_app. Qed.

  Lemma count_cons_eq : forall (l : list A) [x y : A],
      x = y -> count (x :: l) y = S (count l y).
  Proof. apply count_occ_cons_eq. Qed.

  Lemma count_cons_neq : forall (l : list A) [x y : A],
      x <> y -> count (x :: l) y = count l y.
  Proof. apply count_occ_cons_neq. Qed.

  Lemma count_bound (x : A) (l : list A) : count l x <= length l.
  Proof. apply count_occ_bound. Qed.

  Lemma count_ltlen_ex (a : A) (l : list A) :
    count l a < length l -> {x : A | x <> a /\ In x l}.
  Proof.
    intro H. induction l as [|a0 l]; try (simpl in H; lia).
    destruct (eqdec a0 a) as [Heq|Hneq].
    - destruct IHl as [x [Hneqx Hinx]].
      rewrite count_cons_eq in H; try assumption.
      simpl in H. lia.
      exists x. split; try assumption. now right.
    - exists a0. split; try assumption. now left.
  Defined.

  Lemma count_ge_length_ge :
    forall (l : list A) x n, count l x >= n -> length l >= n.
  Proof.
    intros l x n H. eapply Nat.le_trans; try eassumption. apply count_bound.
  Qed.

  Lemma count_map_inj {EDB : EqDec B} :
    forall (l : list A) (f : A -> B) a, ssrfun.injective f -> count (map f l) (f a) = count l a.
  Proof.
    intros l f a Hinj. induction l; [reflexivity|].
    simpl. rewrite IHl.
    destruct (eqdec (f a0) (f a)) as [Heqf|Hneqf];
    destruct (eqdec a0 a) as [Heq|Hneq]; try reflexivity.
    - contradict Hneq. apply Hinj. assumption.
    - contradict Hneqf. rewrite Heq. reflexivity.
  Qed.

  Lemma erase_cons_eq (l : list A) (a : A) : erase a (a :: l) = l.
  Proof. simpl. destruct (eqdec a a); tauto. Qed.
  
  Lemma erase_cons_neq (l : list A) (a b : A) : a <> b -> erase a (b :: l) = b :: erase a l.
  Proof. intro Hneq. simpl. destruct (eqdec a b); tauto. Qed.

  Lemma count_erase_same (l : list A) (a : A) :
    count (erase a l) a = count l a - 1.
  Proof.
    induction l; simpl; try reflexivity.
    destruct (eqdec a a0) as [Heq|Hneq].
    - apply eq_sym in Heq. destruct (eqdec a0 a); try contradiction. lia.
    - simpl. apply not_eq_sym in Hneq. destruct (eqdec a0 a); try contradiction. apply IHl.
  Qed.

  Lemma count_erase_not_same (l : list A) (a b : A) :
    a <> b -> count (erase a l) b = count l b.
  Proof.
    intros Hab. induction l; simpl; try reflexivity.
    destruct (eqdec a a0) as [Heq|Hneq].
    - rewrite <- Heq. destruct (eqdec a b); try contradiction. reflexivity.
    - simpl. destruct (eqdec a0 b); rewrite IHl; reflexivity.
  Qed.

  Lemma count_erase_same_In (l : list A) (a : A) :
      In a l -> S (count (erase a l) a) = count l a.
  Proof.
    intro Hina. rewrite count_In in Hina.
    pose proof (count_erase_same l a). lia.
  Qed.

  Lemma erase_not_In (l : list A) (x : A) :
    ~ In x l -> erase x l = l.
  Proof.
    intro Hnin. induction l; try reflexivity.
    simpl. destruct (eqdec x a) as [Heq|Hneq].
    - rewrite Heq in Hnin. simpl in Hnin. tauto.
    - rewrite IHl; try reflexivity. simpl in Hnin. tauto.
  Qed.

  Lemma erase_incl (l : list A) (x : A) :
    incl (erase x l) l.
  Proof. intro a. apply set_remove_1. Qed.

  Lemma erase_app_in_l (l1 l2 : list A) (x : A) :
    In x l1 -> erase x (l1 ++ l2) = (erase x l1) ++ l2.
  Proof.
    intros Hin. induction l1; try contradiction.
    destruct Hin as [Heq|Hin].
    - rewrite Heq. simpl. destruct (eqdec x x); try contradiction.
      reflexivity.
    - simpl. destruct (eqdec x a); try reflexivity.
      rewrite IHl1; tauto.
  Qed.

  Lemma erase_app_not_in_l (l1 l2 : list A) (x : A) :
    ~ In x l1 -> erase x (l1 ++ l2) = l1 ++ (erase x l2).
  Proof.
    intros Hnin. induction l1; try reflexivity.
    simpl. destruct (eqdec x a) as [Heq|Hneq];
      try (contradict Hnin; now left).
    destruct (in_dec eqdec x l1) as [Hin'|Hnin'];
      try (contradict Hnin; now right).
    rewrite IHl1; tauto.
  Qed.

  Lemma count_listerase (l1 l2 : list A) :
    forall x, count (listerase l1 l2) x = count l1 x - count l2 x.
  Proof.
    induction l2; intro x.
    - simpl. lia.
    - simpl. destruct (eqdec a x) as [Heq|Hneq].
      + rewrite Heq, count_erase_same, IHl2. lia.
      + rewrite count_erase_not_same; try assumption.
        rewrite IHl2. reflexivity.
  Qed.



(* ZIP *)

  Fixpoint zip {E : Type} (f : A -> B -> E) (lA : list A) (lB : list B) : list E :=
    match lA, lB with
    | a :: tA, b :: tB => f a b :: zip f tA tB
    | _, _ => []
    end.

  Lemma zip_nil_r {E : Type} (f : A -> B -> E) (l : list A) : zip f l [] = [].
  Proof. destruct l; reflexivity. Qed.

  Lemma in_zip_pair_fst {lA : list A} {lB : list B} {p : A * B} :
    p ∈ zip pair lA lB -> fst p ∈ lA.
  Proof.
    revert lB. induction lA; try tauto.
    intros lB H. destruct lB; try contradiction.
    destruct H as [H|H].
    - rewrite <- H. now left.
    - right. apply (IHlA lB). assumption.
  Qed.

  Lemma in_zip_pair_snd {lA : list A} {lB : list B} {p : A * B} :
    p ∈ zip pair lA lB -> snd p ∈ lB.
  Proof.
    revert lA. induction lB; try now setoid_rewrite zip_nil_r.
    intros lA H. destruct lA; try contradiction.
    destruct H as [H|H].
    - rewrite <- H. now left.
    - right. apply (IHlB lA). assumption.
  Qed.

  Lemma zip_pair_in_map_l (f : A -> A)  (lA : list A) (lB : list B) (a : A) (b : B) :
    (a, b) ∈ zip pair lA lB -> (f a, b) ∈ zip pair (map f lA) lB.
  Proof.
    revert lB. induction lA as [|a' lA]; intro lB;
      [simpl; contradiction|].
    destruct lB as [|b' lB]; try contradiction.
    simpl. intros [H|H].
    - injection H. intros Heqb Heqa. left. rewrite Heqa, Heqb. reflexivity.
    - right. apply IHlA. assumption.
  Qed.

  Lemma zip_pair_in_map_r (f : B -> B)  (lA : list A) (lB : list B) (a : A) (b : B) :
    (a, b) ∈ zip pair lA lB -> (a, f b) ∈ zip pair lA (map f lB).
  Proof.
    revert lA. induction lB as [|b' lB]; intro lA;
      [simpl; rewrite zip_nil_r; contradiction|].
    destruct lA as [|a' lA]; try contradiction.
    simpl. intros [H|H].
    - injection H. intros Heqb Heqa. left. rewrite Heqa, Heqb. reflexivity.
    - right. apply IHlB. assumption.
  Qed.

  Lemma zip_pair_bij_fst (lA : list A) (lB : list B) :
    length lA = length lB -> forall a, a ∈ lA -> exists p, p ∈ zip pair lA lB /\ fst p = a.
  Proof.
    intro H. pattern lA, lB. revert lA lB H. apply list_biind; try contradiction.
    intros a lA b lB IH a' Ha'. destruct Ha' as [Ha'|Ha'].
    - exists (a, b). simpl. tauto.
    - destruct (IH a' Ha') as [p Hp]. exists p. simpl. tauto.
  Qed.

  Lemma zip_pair_bij_snd (lA : list A) (lB : list B) :
    length lA = length lB -> forall b, b ∈ lB -> exists p, p ∈ zip pair lA lB /\ snd p = b.
  Proof.
    intro H. pattern lA, lB. revert lA lB H. apply list_biind; try contradiction.
    intros a lA b lB IH b' Hb'. destruct Hb' as [Hb'|Hb'].
    - exists (a, b). simpl. tauto.
    - destruct (IH b' Hb') as [p Hp]. exists p. simpl. tauto.
  Qed.

  Lemma map_eq_zip_pair {lA : list A} {lB : list B} {f : A -> B} :
    map f lA = lB -> forall p, p ∈ zip pair lA lB -> f (fst p) = snd p.
  Proof.
    intro H. pose proof (f_equal (@length _) H) as Hlen.
    rewrite map_length in Hlen. revert H. pattern lA, lB.
    revert lA lB Hlen. apply list_biind; try contradiction.
    intros a lA b lB IH H p Hp. destruct Hp as [Hp|Hp].
    - rewrite <- Hp. simpl in H |- *. injection H. tauto.
    - apply IH. injection H. tauto. assumption.
  Qed.

  Lemma zip_pair_eq_length (lA : list A) (lB : list B) :
    length lA = length lB -> length (zip pair lA lB) = length lA.
  Proof.
    revert lA lB. apply list_biind; [reflexivity|].
    intros a lA b lB Hlen. simpl. apply f_equal. assumption.
  Qed.

  
(* SET EQUALITY *)

  Lemma set_eq_refl (l : list A) : set_eq l l.
  Proof. unfold set_eq. tauto. Qed.

  Lemma set_eq_sym (l l' : list A) : set_eq l l' -> set_eq l' l.
  Proof. unfold set_eq. intros H x. rewrite H. tauto. Qed.

  Lemma set_eq_tran (l1 l2 l3 : list A) :
    set_eq l1 l2 -> set_eq l2 l3 -> set_eq l1 l3.
  Proof. unfold set_eq. intros H1 H2. setoid_rewrite H1. setoid_rewrite H2. tauto. Qed.

  Definition Equivalence_set_eq : Equivalence set_eq :=
  {|
    Equivalence_Reflexive := set_eq_refl;
    Equivalence_Symmetric := set_eq_sym;
    Equivalence_Transitive := set_eq_tran
  |}.

  Lemma set_eq_double_incl (l l' : list A) : set_eq l l' <-> incl l l' /\ incl l' l.
  Proof.
    split.
    - intro H. split; intro x; apply H.
    - intros [H1 H2]. intro x. split; [apply H1 | apply H2].
  Qed.

  Lemma set_eq_incl (l l' : list A) : set_eq l l' -> incl l l'.
  Proof. rewrite set_eq_double_incl. tauto. Qed.

  Lemma set_eq_app_app (l1 l2 m1 m2 : list A) :
    set_eq l1 m1 -> set_eq l2 m2 -> set_eq (l1 ++ l2) (m1 ++ m2).
  Proof.
    repeat rewrite set_eq_double_incl. intros H1 H2.
    split; apply incl_app_app; tauto.
  Qed.

  Lemma set_eq_cons (l1 l2 : list A) (a : A) :
    set_eq l1 l2 -> set_eq (a :: l1) (a :: l2).
  Proof.
    intro H. fold ([a] ++ l1). fold ([a] ++ l2).
    apply set_eq_app_app; [apply set_eq_refl | assumption].
  Qed.



(* MULTISET EQUALITY *)

  Lemma mset_eq_double_incl (l l' : list A) : mset_eq l l' <-> mset_incl l l' /\ mset_incl l' l.
  Proof.
    split.
    - intro H. split; intro x; rewrite H; apply le_n.
    - intros [H1 H2] x. specialize (H1 x). specialize (H2 x). lia.
  Qed.

  Lemma mset_eq_Permutation (l l' : list A) :
    mset_eq l l' <-> Permutation l l'.
  Proof. unfold mset_eq. rewrite <- Permutation_count. tauto. Qed.

  Lemma mset_eq_length (l l' : list A) :
    mset_eq l l' -> length l = length l'.
  Proof. rewrite mset_eq_Permutation. apply Permutation_length. Qed.

  Lemma mset_eq_refl (l : list A) : mset_eq l l.
  Proof. intro x. reflexivity. Qed.

  Lemma mset_eq_sym (l l' : list A) : mset_eq l l' -> mset_eq l' l.
  Proof. intros H x. rewrite H. reflexivity. Qed.

  Lemma mset_eq_tran (l1 l2 l3 : list A) :
    mset_eq l1 l2 -> mset_eq l2 l3 -> mset_eq l1 l3.
  Proof. unfold mset_eq. intros H1 H2. setoid_rewrite H1. setoid_rewrite H2. tauto. Qed.

  Definition Equivalence_mset_eq : Equivalence mset_eq :=
  {|
    Equivalence_Reflexive := mset_eq_refl;
    Equivalence_Symmetric := mset_eq_sym;
    Equivalence_Transitive := mset_eq_tran
  |}.

  Lemma mset_eq_app_app (l1 l2 m1 m2 : list A) :
    mset_eq l1 m1 -> mset_eq l2 m2 -> mset_eq (l1 ++ l2) (m1 ++ m2).
  Proof.
    unfold mset_eq. intros H1 H2 x. repeat rewrite count_app.
    rewrite H1, H2. reflexivity.
  Qed.

  Lemma mset_eq_app_comm (l1 l2 : list A) : mset_eq (l1 ++ l2) (l2 ++ l1).
  Proof. intro x. repeat rewrite count_app. lia. Qed.

  Lemma mset_eq_app_swap_app (l1 l2 l3 : list A) :
    mset_eq (l1 ++ l2 ++ l3) (l2 ++ l1 ++ l3).
  Proof.
    repeat rewrite app_assoc.
    apply mset_eq_app_app; try apply mset_eq_refl.
    apply mset_eq_app_comm.
  Qed.

  Lemma mset_eq_incl (l l' : list A) : mset_eq l l' -> mset_incl l l'.
  Proof. intros H x. rewrite H. apply le_n. Qed.

  Lemma mset_eq_singl_eq (l : list A) (a : A) :
    mset_eq l [a] -> l = [a].
  Proof.
    intro H. pose proof mset_eq_length _ _ H as Heqlen.
    destruct l; try discriminate; destruct l; try discriminate.
    specialize (H a). destruct (eqdec a0 a) as [Heq|Hneq];
      try (rewrite Heq; reflexivity).
    rewrite count_cons_neq in H; try assumption.
    rewrite count_cons_eq in H; try reflexivity.
    simpl in H. discriminate.
  Qed.

  Lemma mset_eq_cons_append (l : list A) (x : A) : mset_eq (x :: l) (l ++ [x]).
  Proof.
    rewrite mset_eq_Permutation. apply Permutation_cons_append.
  Qed.

  Lemma mset_eq_app_inv_l (l l1 l2 : list A) : mset_eq (l ++ l1) (l ++ l2) -> mset_eq l1 l2.
  Proof.
    rewrite ! mset_eq_Permutation. apply Permutation_app_inv_l.
  Qed.

  Lemma mset_eq_length_2 {a1 a2 b1 b2 : A} :
    mset_eq [a1; a2] [b1; b2] -> a1 = b1 /\ a2 = b2 \/ a1 = b2 /\ a2 = b1.
  Proof.
    rewrite mset_eq_Permutation. apply Permutation_length_2.
  Qed.

  Lemma mset_eq_length_2_inv {l : list A} {a1 a2 : A} :
    mset_eq [a1; a2] l -> l = [a1; a2] \/ l = [a2; a1].
  Proof.
    rewrite mset_eq_Permutation. apply Permutation_length_2_inv.
  Qed.

  Lemma mset_incl_refl (l : list A) : mset_incl l l.
  Proof. apply mset_eq_incl, mset_eq_refl. Qed.

  Lemma mset_incl_tran (l1 l2 l3 : list A) : mset_incl l1 l2 -> mset_incl l2 l3 -> mset_incl l1 l3.
  Proof. intros H1 H2 x. eapply Nat.le_trans; try apply H1. apply H2. Qed.

  Lemma mset_incl_refl_tl (l : list A) (a : A) : mset_incl l (a :: l).
  Proof.
    intros x. simpl. destruct (eqdec a x); [apply le_S | idtac]; apply le_n.
  Qed.

  Lemma mset_incl_incl (l l' : list A) : mset_incl l l' -> incl l l'.
  Proof.
    intros H x Hx. specialize (H x).
    rewrite count_In in Hx |- *. lia.
  Qed.

  Lemma mset_incl_not_In (l l' : list A) (a : A) : mset_incl l l' -> ~ In a l' -> ~ In a l.
  Proof.
    intros Hincl Hnin. rewrite count_not_In in Hnin |- *.
    specialize (Hincl a). lia.
  Qed.

  Lemma mset_incl_l_nil (l : list A) : mset_incl l [] -> l = [].
  Proof. intro H. apply incl_l_nil, mset_incl_incl. assumption. Qed.

  Lemma mset_incl_appr (l1 l2 l3 : list A) : mset_incl l1 l3 -> mset_incl l1 (l2 ++ l3).
  Proof. intros H x. rewrite count_app. specialize (H x). lia. Qed.

  Lemma mset_incl_appl (l1 l2 l3 : list A) : mset_incl l1 l2 -> mset_incl l1 (l2 ++ l3).
  Proof. intros H x. rewrite count_app. specialize (H x). lia. Qed.

  Lemma mset_incl_app_app (l1 l2 m1 m2 : list A) :
    mset_incl l1 m1 -> mset_incl l2 m2 -> mset_incl (l1 ++ l2) (m1 ++ m2).
  Proof.
    intros H1 H2 x. repeat rewrite count_app.
    specialize (H1 x). specialize (H2 x). lia.
  Qed.

  Lemma set_eq_incl_r (l1 l2 l2' : list A) :
    set_eq l2 l2' -> (incl l1 l2 <-> incl l1 l2').
  Proof.
    intro H. unfold incl. unfold set_eq in H. setoid_rewrite H. tauto.
  Qed.

  Lemma set_eq_incl_l (l1 l1' l2 : list A) :
    set_eq l1 l1' -> (incl l1 l2 <-> incl l1' l2).
  Proof.
    intro H. unfold incl. unfold set_eq in H. setoid_rewrite H. tauto.
  Qed.

  Lemma mset_eq_incl_l (l1 l1' l2 : list A) :
    mset_eq l1 l1' -> (mset_incl l1 l2 <-> mset_incl l1' l2).
  Proof. unfold mset_eq, mset_incl. intro H. setoid_rewrite H. tauto. Qed.

  Lemma mset_eq_set_eq {l l' : list A} :
    mset_eq l l' -> set_eq l l'.
  Proof.
    intro H. unfold mset_eq in H. unfold set_eq.
    setoid_rewrite (count_occ_In eqdec l).
    setoid_rewrite (count_occ_In eqdec l').
    setoid_rewrite H. tauto.
  Qed.

  Lemma mset_incl_NoDup (l l' : list A) : NoDup l' -> mset_incl l l' -> NoDup l.
  Proof.
    repeat rewrite NoDup_count. unfold mset_incl.
    intros HND Hinc. intros x. specialize (HND x). specialize (Hinc x). lia.
  Qed.

  Lemma mset_eq_NoDup (l l' : list A) : mset_eq l l' -> NoDup l -> NoDup l'.
  Proof.
    intros. apply (mset_incl_NoDup l' l); try assumption.
    apply mset_eq_incl, mset_eq_sym. assumption.
  Qed.

  Lemma NoDup_l_mset_incl_iff (l l': list A) : NoDup l -> mset_incl l l' <-> incl l l'.
  Proof.
    rewrite NoDup_count. unfold mset_incl. unfold incl.
    setoid_rewrite count_In. intros HND. split.
    - intros H x. specialize (HND x). specialize (H x). lia.
    - intros H x. specialize (HND x). specialize (H x). lia.
  Qed.

  Lemma mset_eq_erase_cons (l l' : list A) (a : A) :
    In a l -> mset_eq (erase a l) l' ->
      mset_eq l (a :: l').
  Proof.
    intros Hina Hmeq. intros x.
    destruct (eqdec a x) as [Heq|Hneq].
    - rewrite <- Heq. rewrite count_cons_eq; try reflexivity.
      specialize (Hmeq a). rewrite count_erase_same in Hmeq.
      rewrite count_In in Hina. lia.
    - rewrite count_cons_neq; try assumption.
      specialize (Hmeq x). rewrite count_erase_not_same in Hmeq; try assumption.
  Qed.

  Lemma mset_incl_cons_cons (l l' : list A) (a : A) :
    mset_incl l l' -> mset_incl (a :: l) (a :: l').
  Proof.
    intros H x.
    destruct (eqdec a x) as [Heq|Hneq].
    - rewrite <- Heq. repeat rewrite count_cons_eq; try reflexivity.
      specialize (H a). lia.
    - repeat rewrite count_cons_neq; try assumption.
      apply H.
  Qed.

  Lemma mset_incl_cons_l (l l' : list A) (a : A) :
    mset_incl (a :: l) l' -> mset_incl l l'.
  Proof. intros H x. specialize (H x). simpl in H. destruct (eqdec a x); lia. Qed.

  Lemma mset_incl_tl (l l' : list A) (a : A) :
    mset_incl l l' -> mset_incl l (a :: l').
  Proof.
    intro H. eapply mset_incl_tran; try eassumption. apply mset_incl_refl_tl.
  Qed.

  Lemma mset_incl_filter (f : A -> bool) (l : list A) :
    mset_incl (filter f l) l.
  Proof.
    induction l.
    - simpl. apply mset_incl_refl.
    - simpl. destruct (f a); try now apply mset_incl_cons_cons.
      now apply mset_incl_tl.
  Qed.

  Fixpoint mset_compl (l Ω : list A) : list A :=
    match l with
    | [] => Ω
    | a :: l' => erase a (mset_compl l' Ω)
    end.

  Lemma mset_compl_ppty (l Ω : list A) : mset_incl l Ω -> mset_eq (l ++ (mset_compl l Ω)) Ω.
  Proof.
    intro Hinc. induction l.
    - simpl. apply mset_eq_refl.
    - lapply IHl. 2:{ eapply mset_incl_tran; try apply Hinc. apply mset_incl_refl_tl. }
      intros Hmeq x. specialize (Hmeq x). specialize (Hinc x).
      rewrite count_app in Hmeq |- *.
      simpl. destruct (eqdec a x) as [Heq|Hneq].
      + rewrite <- Heq in Hmeq, Hinc |- *. rewrite <- Hmeq. rewrite count_erase_same.
        simpl in Hinc. destruct (eqdec a a); try contradiction. lia.
      + rewrite (count_erase_not_same _ _ _ Hneq). assumption.
  Qed.

  Lemma mset_eq_app_mset_compl (l1 l2 l3 : list A) :
    mset_eq (l1 ++ l2) l3 -> mset_eq l2 (mset_compl l1 l3).
  Proof.
    intro Heq.
    assert (mset_incl l1 l3) as Hinc13.
    { pose proof (mset_eq_incl _ _ Heq) as Hinc.
      apply (mset_incl_tran _ (l1 ++ l2)).
      apply mset_incl_appl, mset_incl_refl.
      assumption. }
    pose proof (mset_eq_tran _ _ _ Heq (mset_eq_sym _ _ (mset_compl_ppty l1 l3 Hinc13))) as H.
    apply mset_eq_app_inv_l in H. assumption.
  Qed.

  Lemma mset_compl_length (l Ω : list A) :
    mset_incl l Ω -> length (mset_compl l Ω) = length Ω - length l.
  Proof.
    intro H. pose proof (mset_compl_ppty l Ω H) as Hmeq.
    apply mset_eq_length in Hmeq.
    rewrite app_length in Hmeq. lia.
  Qed.

  Lemma mset_compl_mset_incl (l Ω : list A) :
    mset_incl l Ω -> mset_incl (mset_compl l Ω) Ω.
  Proof.
    intro H. apply mset_compl_ppty in H.
    apply mset_eq_incl in H. eapply mset_incl_tran; try eassumption.
    apply mset_incl_appr, mset_incl_refl.
  Qed.

  Lemma mset_compl_mset_eq_l (l l' Ω : list A) :
    mset_incl l Ω -> mset_eq l l' -> mset_eq (mset_compl l Ω) (mset_compl l' Ω).
  Proof.
    intros Hinc Hmeq. apply mset_eq_app_mset_compl.
    eapply mset_eq_tran; [idtac | apply mset_compl_ppty; eassumption].
    apply mset_eq_app_app.
    - apply mset_eq_sym. assumption.
    - apply mset_eq_refl.
  Qed.
  
  Fixpoint power_mset (l : list A) : list (list A) :=
    match l with
    | []      => [[]]
    | a :: l' => (map (cons a) (power_mset l')) ++ (power_mset l')
    end.

  Lemma power_mset_all (l' : list A) :
    forall l, mset_incl l l' <-> InA mset_eq l (power_mset l').
  Proof.
    induction l'.
    - intro l. split.
      + intro H. rewrite (mset_incl_l_nil _ H). simpl. constructor 1.
        apply mset_eq_refl.
      + intro H. simpl in H. inversion H; now apply mset_eq_incl.
    - intro l. split.
      + intro Hminc. simpl. rewrite InA_app_iff. pose proof (Hminc a) as Hca.
        rewrite count_cons_eq in Hca; try reflexivity.
        destruct (le_lt_eq_dec _ _ Hca) as [Hcalt|Hcale].
        * right. apply IHl'. intro x. destruct (eqdec a x) as [Heqa|Hneqa].
         -- rewrite <- Heqa. lia.
         -- specialize (Hminc x). rewrite count_cons_neq in Hminc; assumption.
        * left. assert (In a l) as Hina by (rewrite count_In; lia).
          cut (InA mset_eq (erase a l) (power_mset l')).
          { repeat rewrite InA_alt. intros [l0 [Hmeql0 Hinl0]].
            exists (a :: l0). split.
            - apply (mset_eq_erase_cons); assumption.
            - apply in_map_iff. exists l0. split; tauto. }
          apply IHl'. intro x. destruct (eqdec a x) as [Heqa|Hneqa].
         -- rewrite <- Heqa. pose proof (count_erase_same_In l a Hina). lia.
         -- rewrite (count_erase_not_same _ _ _ Hneqa).
            specialize (Hminc x).
            rewrite (count_cons_neq _ Hneqa) in Hminc.
            assumption.
      + intro HInA. simpl in HInA. rewrite InA_app_iff in HInA.
        destruct HInA as [HInA|HInA].
        * rewrite InA_alt in HInA. destruct HInA as [l0 [Hmeql0 Hinl0]].
          rewrite in_map_iff in Hinl0. destruct Hinl0 as [l1 [Heql0 Hinl1]].
          apply (In_InA Equivalence_mset_eq) in Hinl1.
          apply IHl' in Hinl1. apply mset_eq_incl in Hmeql0.
          eapply mset_incl_tran; try eassumption.
          rewrite <- Heql0. apply mset_incl_cons_cons. assumption.
        * apply IHl' in HInA. eapply mset_incl_tran; try eassumption.
          apply mset_incl_refl_tl.
  Qed.    


(* AAC Instances *)

  #[export] Instance mset_eq_Equiv : Equivalence mset_eq := {|
    Equivalence_Reflexive := mset_eq_refl;
    Equivalence_Symmetric := mset_eq_sym;
    Equivalence_Transitive := mset_eq_tran |}.

  #[export] Instance mset_eq_app_Assoc :
    Associative mset_eq (@app A).
  Proof. intros x y z. rewrite app_assoc. apply mset_eq_refl. Qed.

  #[export] Instance mset_eq_app_Comm :
    Commutative mset_eq (@app A).
  Proof. intros x y. rewrite mset_eq_Permutation. apply Permutation_app_comm. Qed.

  #[export] Instance mset_eq_app_Prop :
    Proper (mset_eq ==> mset_eq ==> mset_eq) (@app A).
  Proof. intros x x' Heqx y y' Heqy. apply mset_eq_app_app; assumption. Qed.


  #[export] Instance set_eq_Equiv : Equivalence (@set_eq A).
  Proof.
    constructor.
    - intro x. apply set_eq_refl.
    - intros x y. apply set_eq_sym.
    - intros x y z. apply set_eq_tran.
  Qed.

  #[export] Instance set_eq_app_Assoc : Associative set_eq (@app A).
  Proof. intros x y z. rewrite app_assoc. apply set_eq_refl. Qed.

  #[export] Instance set_eq_app_Comm : Commutative set_eq (@app A).
  Proof. intros x y x0. repeat rewrite in_app_iff. split; intros [H|H]; tauto. Qed.

  #[export] Instance set_eq_app_Unit : Unit set_eq (@app A) (@nil A).
  Proof.
    constructor.
    - intro x. simpl. apply set_eq_refl.
    - intro x. rewrite app_nil_r. apply set_eq_refl.
  Qed.

  #[export] Instance set_eq_app_Prop :
    Proper (set_eq ==> set_eq ==> set_eq) (@app A).
  Proof. intros x x' Heqx y y' Heqy. apply set_eq_app_app; assumption. Qed.


(* ERASE AGAIN *)



  Lemma erase_In_length (l : list A) (x : A) :
    In x l -> S (length (erase x l)) = length l.
  Proof.
    intro Hx. apply (@eq_trans _ _ (length (x :: (erase x l))));
      try reflexivity.
    apply (mset_eq_length). intro y. simpl.
    destruct (eqdec x y) as [Heq|Hneq].
    - rewrite <- Heq. rewrite count_erase_same.
      rewrite count_In in Hx. lia.
    - rewrite count_erase_not_same; try assumption. reflexivity.
  Qed.

  Lemma erase_In_length' (l : list A) (x : A) :
    In x l -> length (erase x l) = length l - 1.
  Proof.
    intro H. pose proof (erase_In_length _ _ H).
    rewrite (count_occ_In eqdec) in H. lia.
  Qed.

  Lemma erase_not_In_length (l : list A) (x : A) :
    ~ In x l -> length (erase x l) = length l.
  Proof.
    intro Hnin. rewrite (erase_not_In _ _ Hnin). reflexivity.
  Qed.

  Lemma erase_or_length (l : list A) (x : A) :
    length (erase x l) = length l \/
    length (erase x l) = length l - 1.
  Proof.
    destruct (in_dec eqdec x l).
    - right. now apply erase_In_length'.
    - left. now apply erase_not_In_length.
  Qed.

  Lemma erase_length_bound (l : list A) (a : A) : length (erase a l) <= length l.
  Proof. destruct (erase_or_length l a); lia. Qed.

  Lemma erase_length_bound' (l : list A) (a : A) : length l <= S (length (erase a l)).
  Proof. destruct (erase_or_length l a); lia. Qed.
  
  Lemma mset_incl_erase (l : list A) (a : A) : mset_incl (erase a l) l.
  Proof.
    intro x. destruct (eqdec a x) as [Heq|Hneq].
    - rewrite Heq. rewrite count_erase_same. lia.
    - rewrite  count_erase_not_same; [constructor | assumption].
  Qed.

  Lemma mset_incl_erase_erase (l l' : list A) (a : A) :
    mset_incl l l' ->
    mset_incl (erase a l) (erase a l').
  Proof.
    intro H. intro x. destruct (eqdec a x) as [Heq|Hneq].
    - rewrite <- Heq. repeat rewrite count_erase_same.
      specialize (H a). lia.
    - repeat rewrite count_erase_not_same; try assumption. apply H.
  Qed.

  Lemma mset_incl_length (E F : list A) : mset_incl E F -> length E <= length F.
  Proof.
    revert F E. induction F; intros E Hincl.
    - apply mset_incl_l_nil in Hincl. rewrite Hincl. constructor.
    - assert (length (erase a E) <= length F) as Hlen.
      { apply IHF. intro x. specialize (Hincl x). simpl in Hincl.
        destruct (eqdec a x) as [Heq|Hneq].
        - rewrite Heq. rewrite count_erase_same. lia.
        - rewrite count_erase_not_same; assumption. }
      simpl. pose proof (erase_length_bound' E a). lia.
  Qed.

  Lemma listerase_app_mset_eq (l1 l2 : list A) :
    mset_incl l2 l1 -> mset_eq ((listerase l1 l2) ++ l2) l1.
  Proof.
    intros H x. rewrite count_app, count_listerase.
    specialize (H x). lia.
  Qed.

  Lemma listerase_mset_incl (l1 l2 : list A) : mset_incl (listerase l1 l2) l1.
  Proof.
    intro x. rewrite count_listerase. lia.
  Qed.

  Lemma listerase_incl (l1 l2 : list A) : incl (listerase l1 l2) l1.
  Proof.
    apply mset_incl_incl. apply listerase_mset_incl.
  Qed.

  Lemma listerase_nil_mset_eq (l1 l2 : list A) :
    mset_incl l2 l1 -> listerase l1 l2 = [] -> mset_eq l1 l2.
  Proof.
    intros Hinc Hnil x. pose proof (count_listerase l1 l2 x) as Hcnt.
    rewrite Hnil in Hcnt. simpl in Hcnt.
    specialize (Hinc x). lia.
  Qed.
    



(* LIST MINUS *)

  Fixpoint listminus (l1 l2 : list A) : list A :=
    match l2 with
    | []      => l1
    | a :: l2' => remove eqdec a (listminus l1 l2')
    end.

  Lemma in_listminus_iff (l1 l2 : list A) :
    forall x, In x (listminus l1 l2) <-> (In x l1 /\ ~ In x l2).
  Proof.
    revert l1. induction l2; intros l1 x; try tauto.
    simpl. split.
    - intro H. apply in_remove in H.
      destruct H as [Hin Hneq].
      apply IHl2 in Hin. destruct Hin as [Hin Hnin].
      apply not_eq_sym in Hneq. tauto.
    - intros [Hin Hnin]. apply in_in_remove.
      apply not_eq_sym. tauto.
      apply IHl2. tauto.
  Qed.

  Lemma incl_listminus (l1 l2 : list A) : incl (listminus l1 l2) l1.
  Proof. intros x Hx. apply in_listminus_iff in Hx. tauto. Qed.

  Lemma not_in_listminus (l1 l2 : list A) : forall x, In x l2 -> ~ In x (listminus l1 l2).
  Proof. intros x Hx Hctr. apply in_listminus_iff in Hctr. tauto. Qed.

  Lemma listminus_recover (l1 l2 : list A) : set_eq ((listminus l1 l2) ++ l2) (l1 ++ l2).
  Proof.
    intro x. repeat rewrite in_app_iff. split; intro H.
    - destruct H as [H|H].
      + left. apply (incl_listminus _ l2). assumption.
      + now right.
    - destruct (in_dec eqdec x l2) as [Hin|Hnin].
      + now right.
      + destruct H as [H|]; try contradiction.
        left. apply in_listminus_iff. tauto.
  Qed.

  Lemma listminus_nil_l : forall F : list A, listminus [] F = [].
  Proof.
    induction F.
    - reflexivity.
    - simpl. rewrite IHF. reflexivity.
  Qed.

  Lemma listminus_remove_comm : forall (E F : list A) (a : A),
      remove eqdec a (listminus E F) = listminus (remove eqdec a E) F.
  Proof.
    intros E F. revert E. induction F.
    - simpl. intros E a. reflexivity.
    - simpl. intros E x. rewrite <- IHF.
      rewrite remove_remove_comm. reflexivity.
  Qed.

  Lemma listminus_empty : forall E F : list A, listminus E F = [] -> E ⊆ F.
  Proof.
    intros E F. revert E. induction F.
    - intros E H. simpl in H. rewrite H. apply incl_refl.
    - intros E H. simpl in H. rewrite listminus_remove_comm in H.
      intros x Hx. destruct (eqdec x a) as [Heq|Hneq].
      + rewrite Heq. left. reflexivity.
      + right. apply (IHF _ H). apply in_in_remove; assumption.
  Qed.


  Fixpoint find_dup (l : list A) : option A :=
    match l with
    | x :: xs => if in_dec eqdec x xs then Some x else find_dup xs
    | []     => None
    end.

  Lemma find_dup_in (l : list A) (x : A) : find_dup l = Some x -> List.In x l.
  Proof.
    intro H. induction l; try discriminate.
    simpl in H. destruct (in_dec eqdec a l).
    - injection H. intro Heqa. rewrite Heqa. now left.
    - right. apply IHl. assumption.
  Qed.

  Lemma find_dup_is_dup (l : list A) (x : A) : find_dup l = Some x -> count l x >= 2.
  Proof.
    intro Hdup. induction l; try discriminate.
    simpl in Hdup. destruct (in_dec eqdec a l) as [Hin|Hnin].
    - injection Hdup. intro Heqa. rewrite Heqa in Hin |- *.
      rewrite count_cons_eq; try reflexivity.
      rewrite count_In in Hin. lia.
    - specialize (IHl Hdup). simpl.
      destruct (eqdec a x); lia.
  Qed.

  Lemma find_dup_not_NoDup (l : list A) (x : A) : find_dup l = Some x -> ~ NoDup l.
  Proof.
    intros Hdup HND. rewrite NoDup_count in HND.
    apply find_dup_is_dup in Hdup. specialize (HND x). lia.
  Qed.

  Lemma find_dup_eq_nodup : forall l, find_dup l = None -> l = nodup eqdec l.
  Proof.
    induction l; try tauto.
    simpl. destruct (in_dec eqdec a l); try discriminate.
    intro H. rewrite <- IHl; try assumption. reflexivity.
  Qed.

  Lemma find_dup_NoDup : forall l, find_dup l = None -> NoDup l.
  Proof.
    intros l H. rewrite find_dup_eq_nodup; try assumption. apply NoDup_nodup.
  Qed.

  Definition distinct (l l' : list A) : Prop := forall x, In x l -> ~ In x l'.

  Lemma NoDup_app_distinct (l l' : list A) : NoDup (l ++ l') -> distinct l l'.
  Proof.
    intro ND. unfold distinct. induction l'; try tauto.
    intros x Hx Hcont. apply NoDup_remove in ND.
    destruct ND as [ND Hnin]. specialize (IHl' ND).
    destruct Hcont as [Hcont|Hcont].
    - contradict Hnin. rewrite Hcont. apply in_app_iff. tauto.
    - apply (IHl' x); assumption.
  Qed.

End ListMore.
