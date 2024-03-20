Require Export A_8_1.
Require Import Lia.

Module A9_1.

Lemma IsFun : ∀ (X Y : Type) (f : X -> Y),
  Function \{\ λ x y, y = f x \}\.
Proof.
  intros X Y f n v1 v2 H0 H1.
  applyAxiomII' H0. applyAxiomII' H1.
  rewrite H1. assumption.
Qed.

Lemma FunIsSeq : ∀ (f : nat -> R),
  IsSeq \{\ λ n y, y = f n \}\.
Proof.
  intros f. split; [apply IsFun | apply AxiomI].
  intros n. split; intros H0; applyAxiomII H0;
  apply AxiomII; auto.
  exists (f n). apply AxiomII'.
  reflexivity.
Qed.

Lemma FunValue : ∀ (X Y : Type) (f : X -> Y) (x : X)
  (o : Y), \{\ λ x y, y = f x \}\[x | o] = f x.
Proof.
  intros X Y f x o.
  apply f_x_T; [apply IsFun | apply AxiomII'].
  reflexivity.
Qed.

Lemma FunValueR : ∀ (X : Type) (f : X -> R) (x : X),
  \{\ λ t y, y = f t \}\[x] = f x.
Proof.
  intros X f n. apply FunValue.
Qed.

(* 定义：T为闭区间[a, b]的分割 *)
Definition seg (T : Seq) a b n := Function T /\ (0 < n)%nat
  /\ (∀ k, (k < n)%nat -> T[k] < T[S k]) /\ T[O] = a /\ T[n] = b.

Lemma Increase_seg : ∀ T a b n, seg T a b n
  -> (∀ n1 n2, (n1 < n)%nat -> (n2 < n)%nat -> (n1 < n2)%nat -> T[n1] < T[n2]).
Proof.
  intros. generalize dependent n1. induction n2; intros.
  - exfalso. apply (Nat.nlt_0_r n1). auto.
  - assert (∀ n1, (n1 < n)%nat -> (n1 < n2)%nat -> T[n1] < T[n2]).
    { apply IHn2; lia. } destruct H as [H[]].
    assert (T[n2] < T [S n2]). { apply H5; lia. }
    destruct (classic (n1 = n2)).
    + rewrite H7; auto.
    + assert (T[n1] < T[n2]). { apply H3; lia. } lra.
Qed.

Lemma equal_seg: ∀ T a b n, seg T a b n -> (∀ n1 n2, (n1 < n)%nat
  -> (n2 < n)%nat -> T[n1] = T[n2] -> (n1 = n2)%nat).
Proof.
  intros. destruct (classic (n1 = n2)); auto.
  apply nat_total_order in H3 as [];
  apply (Increase_seg T a b n H) in H3; auto; lra.
Qed.

(* 定义：x为分割T的模 *)
Definition segMold T n x := (∃ k, (k < n)%nat /\ T[S k] - T[k] = x)
  /\ (∀ m, (m < n)%nat -> T[S m] - T[m] <= x).
Definition mold T n := cR \{ λ x, segMold T n x \}.

(* 引理：任何分割都存在模 *)
Lemma Lemma9_1_1 : ∀ T a b n, seg T a b n -> ∃ x, segMold T n x.
Proof.
  intros T a b n [H3 [H0 [H1 []]]]. clear H H2. induction n as [|n IHn].
  - apply Nat.lt_irrefl in H0. contradiction.
  - destruct (classic (n = 0%nat)).
    + rewrite H. exists (T[1%nat] - T[0%nat]).
      split; intros; eauto. assert (m = 0%nat). lia.
      rewrite H4. lra.
    + assert (∀ k, (k < n)%nat -> T[k] < T[S k]). { intros. apply H1. lia. }
      assert (∃ x, segMold T n x) as [x[[k[]]]]. { apply IHn; auto. lia. }
      destruct (Rlt_or_le x (T[S n] - T[n])) as [].
      * exists (T[S n] - T[n]). split; intros; eauto.
        destruct (classic (m = n)). rewrite H9. lra.
        assert (T[S m] - T[m] <= x). { apply H6. lia. } lra.
      * exists x. split; intros; eauto.
        destruct (classic (m = n)). rewrite H9; auto.
        apply H6. lia.
Qed.

(* 引理：分割的任何小区间长度均小于等于模 *)
Lemma Lemma9_1_2 : ∀ T a b n k, (k < n)%nat -> seg T a b n
  -> T[S k] - T[k] <= (mold T n).
Proof.
  intros T a b n k H0 H1. apply Lemma9_1_1 in H1 as H2. destruct H2 as [x H2].
  assert (H3 : NotEmpty \{ λ x, segMold T n x \}).
  { exists x. apply AxiomII. assumption. }
  apply AxiomcR in H3. applyAxiomII H3. destruct H3 as [H3 H4]. auto.
Qed.

(* 定义：分割T上的点集{ξ} *)
Definition segPoint (T ξ : Seq) :=
  IsSeq ξ /\ ∀ n, T[n] <= ξ[n] <= T[S n].


(* 定义3：J为f在区间[a, b]上的定积分 *)
Definition defIntegral (f : Fun) (a b J : R) :=
  Function f /\ a < b /\ (\[a, b\]) ⊂ dom[f] /\
  ∀ ε, 0<ε -> (∃ δ, 0<δ /\ (∀ T ξ n, seg T a b (S n) ->
    segPoint T ξ -> (mold T (S n) < δ)
    -> Abs[Σ \{\ λ i s, s = f[ξ[i]] * (T[S i] - T[i]) \}\ n - J] < ε)).
    



End A9_1.

Export A9_1.
