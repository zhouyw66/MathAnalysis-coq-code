Require Export A_9_1.

Module A9_2.

(* 牛顿-莱布尼兹公式 *)
Theorem Theorem9_1 : ∀ f F a b, Function f ->
  a < b -> ContinuousClose f a b ->
  (∀ x, a <= x <= b -> derivative F x f[x])
  -> defIntegral f a b (F[b] - F[a]).
Proof.
  intros f F a b H0 H1 H2 H3.
  assert (H4 : (\[a, b\]) ⊂ dom[f]).
  { intros x I1. applyAxiomII I1.
    destruct H2 as [I2 [I3 I4]].
    destruct I1 as [I1 I5].
    destruct I1 as [I1 | I1].
    - destruct I5 as [I5 | I5].
      + apply I2. split; assumption.
      + rewrite I5. apply I4.
    - rewrite I1. apply I3. }
  repeat split; auto.
  intros ε H6. apply Theorem4_9 in H2 as H7.
  destruct H7 as [H7 [H8 H9]].
  assert (H22 : 0 < ε/(b - a)).
  { apply Rdiv_lt_0_compat; lra. }
  generalize (H9 (ε/(b - a)) H22). intros [δ [H10 H11]].
  exists δ. split; auto.
  intros T ξ n H12 H13 H14.
  assert (H15 : ∀ u n, F[u[S n]] - F[u[O]] =
    Σ \{\ λ i v, v = F[u[S i]] - F[u[i]] \}\ n).
  { intros u m. induction m as [|m IHm].
    - simpl. rewrite FunValueR. reflexivity.
    - simpl. rewrite FunValueR. rewrite <- IHm. field. }
  generalize (H15 T n). intros H16.
  generalize H12; intros [H17 [H18 [H19 [H20 H21]]]].
  rewrite H20 in H16. rewrite H21 in H16.
  clear H15.
  assert (H23 : ∀ k, (k <= S n)%nat -> a <= T[k] <= b).
  { intros k I1. split.
    - rewrite <- H20. destruct (Nat.eq_0_gt_0_cases k) as [I2 | I2].
      + rewrite I2. lra. 
      + apply EqualIncrease; auto. split; auto.
        intros m. left. apply H19.
    - rewrite <- H21. apply le_lt_or_eq in I1 as [I1 | I1].
      + apply EqualIncrease; auto. split; auto.
        intros m. left. apply H19.
      + rewrite I1. lra. }
  assert (H24 : ∀ k, (k <= n)%nat ->
    (∀ x, T[k] < x < T[S k] -> derivable F x)).
  { intros k I1 x I2. exists (f[x]). apply H3.
    apply le_S in I1 as I3. apply Peano.le_n_S in I1.
    apply H23 in I3. apply H23 in I1. lra. }
  assert (H25 : ∀ k, (k <= n)%nat -> ContinuousClose F T[k] T[S k]).
  { intros k I1. assert (I4 : a <= T[k] <= b).
    { apply le_S in I1 as I3.
      apply Peano.le_n_S in I1.
      apply H23 in I3. apply H23 in I1. lra. }
    split; [idtac | split].
    - intros x I2. apply Theorem5_1. exists (f[x]).
      apply H3. apply le_S in I1 as I3.
      apply Peano.le_n_S in I1.
      apply H23 in I3. apply H23 in I1. lra.
    - assert (I2 : derivable F T[k]).
      { exists (f[T[k]]). apply H3. assumption. }
      apply Theorem5_1 in I2 as [c I2].
      split; auto. apply Theorem3_1. assumption.
    - assert (I2 : derivable F T[S k]).
      { exists (f[T[S k]]). apply H3.
        apply Peano.le_n_S in I1.
        apply H23 in I1. assumption. }
      apply Theorem5_1 in I2 as [c I2].
      split; auto. apply Theorem3_1. assumption. }
  assert (H26 : ∀ k, (k <= n)%nat -> ∃ η', T[k] < η' < T[S k] /\
    f[η'] * (T[S k] - T[k]) = F[T[S k]] - F[T[k]]).
  { intros k I1. generalize (H24 k I1); intros I2.
    generalize (H25 k I1); intros I3.
    generalize (Theorem6_2 F T[k] T[S k] (H19 k) I3 I2).
    intros [η' [I4 I5]]. exists η'. split; auto.
    assert (I6 : a <= η' <= b).
    { apply le_S in I1 as I6.
      apply Peano.le_n_S in I1 as I7.
      apply H23 in I6. apply H23 in I7. lra. }
    apply H3 in I6.
    assert (I7 : f[η'] = (F[T[S k]] - F[T[k]]) / (T[S k] - T[k])).
    { eapply derivativeUnique; eauto. }
    rewrite I7. field. generalize (H19 k). lra. }
  assert (H27 : ∃ η, η = \{\ λ k v, v =
    cR \{ λ η', T[k] < η' < T[S k] /\
      f[η'] * (T[S k] - T[k]) =
        F[T[S k]] - F[T[k]] \} \}\).
  { exists \{\ λ k v, v =
    cR \{ λ η', T[k] < η' < T[S k] /\
      f[η'] * (T[S k] - T[k]) =
        F[T[S k]] - F[T[k]] \} \}\.
    reflexivity. }
  destruct H27 as [η H27].
  assert (H28 : ∀ i, (i <= n)%nat ->
    T[i] < η[i] < T[S i] /\ f[η[i]] * (T[S i] - T[i]) =
      F[T[S i]] - F[T[i]]).
  { intros i I1.
    assert (I2 : NotEmpty \{ λ η', T[i] < η' < T[S i]
      /\ f[η'] * (T[S i] - T[i]) =
      F[T[S i]] - F[T[i]] \}).
    { apply H26 in I1 as [η' I1].
      exists η'. apply AxiomII.
      assumption. }
    apply AxiomcR in I2 as I3.
    assert (I4 : η[i] = cR \{ λ η', T[i] < η' < T[S i] /\
      f[η'] * (T[S i] - T[i]) = F[T[S i]] - F[T[i]] \}).
    { rewrite H27. apply FunValueR. }
    rewrite <- I4 in I3. clear I4.
    applyAxiomII I3. assumption. }
  assert (H29 : ∀ k, (k <= n)%nat ->
    Σ \{\ λ i v, v = F[T[S i]] - F[T[i]] \}\ k =
    Σ \{\ λ i v, v = f[η[i]] * (T[S i] - T[i]) \}\ k).
  { intros k. induction k as [|k IHk].
    - intros I1. simpl. rewrite FunValueR.
      rewrite FunValueR. symmetry.
      apply H28. assumption.
    - intros I1. apply le_Sn_le in I1 as I2.
      apply IHk in I2. simpl.
      rewrite FunValueR. rewrite FunValueR.
      rewrite I2. apply H28 in I1 as [I1 I3].
      rewrite I3. field. }
  generalize (H29 n (le_n n)); intros H30.
  rewrite H30 in H16. clear H29 H30.
  rewrite H16. clear H27 H26 H9.
  assert (H29 : ∀ k, Σ \{\ λ i s, s = f[ξ[i]] *
    (T[S i] - T[i]) \}\ k - Σ \{\ λ i v, v =
    f[η[i]] * (T[S i] - T[i])\}\ k =
    Σ \{\ λ i s, s = (f[ξ[i]] - f[η[i]])
      * (T[S i] - T[i]) \}\ k).
  { intros k. induction k as [|k IHk].
    - simpl. rewrite FunValueR.
      rewrite FunValueR. rewrite FunValueR.
      field.
    - simpl. rewrite FunValueR.
      rewrite FunValueR. rewrite FunValueR.
      rewrite <- IHk. field. }
  rewrite H29. clear H29.
  assert (H29 : ∀ k, Abs[Σ \{\ λ i s, s =
    (f[ξ[i]] - f[η[i]]) * (T[S i] - T[i]) \}\ k]
    <= Σ \{\ λ i s, s = Abs[f[ξ[i]] - f[η[i]]]
    * (T[S i] - T[i]) \}\ k).
  { intros k. induction k as [|k IHk].
    - simpl. rewrite FunValueR.
      rewrite FunValueR. rewrite Abs_mult.
      rewrite (Abs_ge (T[1%nat] - T[0%nat])); try lra.
      left. apply Rlt_Rminus. apply H19.
    - simpl. rewrite FunValueR.
      rewrite FunValueR.
      generalize (Abs_plus_le (Σ \{\ λ i s, s =
        (f[ξ[i]] - f[η[i]]) * (T[S i] - T[i])\}\ k)
        ((f[ξ[S k]] - f[η[S k]]) * (T[S (S k)] - T[S k]))).
      intros I1. assert (I2 :  Abs[(f[ξ[S k]] - f[η[S k]])
        * (T[S (S k)] - T[S k])] =  Abs[(f[ξ[S k]] - f[η[S k]])]
        * (T[S (S k)] - T[S k])).
      { rewrite Abs_mult.
        rewrite (Abs_ge (T[S (S k)] - T[S k])); auto.
        left. apply Rlt_Rminus. apply H19. }
      lra. }
  generalize (H29 n); intros H30. clear H29.
  apply Rle_lt_trans with (r2 := Σ \{\ λ i s,
    s = Abs[f[ξ[i]] - f[η[i]]] * (T[S i] - T[i]) \}\ n); auto.
  clear H30.
  assert (H29 : ∀ k, (k <= n)%nat ->
    Σ \{\ λ i s, s = Abs[f[ξ[i]] - f[η[i]]]
    * (T[S i] - T[i]) \}\ k < Σ \{\ λ i s,
    s = ε / (b - a) * (T[S i] - T[i]) \}\ k).
  { intros k. destruct H13 as [I5 I6].
    induction k as [|k IHk].
    - intros I1. simpl. rewrite FunValueR.
      rewrite FunValueR.
      generalize (H19 O). intros I2.
      apply Rmult_lt_compat_r; try lra.
      assert (I3 : a <= T[O] <= b). lra.
      assert (I4 : a <= T[1%nat] <= b).
      { apply H23. apply le_n_S. assumption. }
      generalize (I6 O). intros I9.
      apply H28 in I1 as [I7 I8].
      apply H11.
      + apply AxiomII. lra.
      + apply AxiomII. lra.
      + generalize (Lemma9_1_2 T a b (S n) O
          (Nat.lt_0_succ n) H12).
        intros I10. apply Abs_R. lra.
    - intros I1. apply le_Sn_le in I1 as I2.
      apply le_S in I1 as I3.
      apply le_n_S in I1 as I4.
      apply H23 in I4. apply H23 in I3.
      apply IHk in I2 as I7.
      simpl. rewrite FunValueR.
      rewrite FunValueR. apply Rplus_lt_compat; auto.
      generalize (H19 (S k)); intros I8.
      apply Rmult_lt_compat_r; try lra.
      generalize (I6 (S k)). intros I9.
      apply le_lt_n_Sm in I1 as I12.
      apply H28 in I1 as [I10 I11].
      apply H11.
      + apply AxiomII. lra.
      + apply AxiomII. lra.
      + generalize (Lemma9_1_2 T a b (S n) (S k)
          I12 H12).
        intros I13. apply Abs_R. lra. }
  generalize (H29 n (le_n n)). intros H30.
  clear H29. apply Rlt_le_trans with (r2 :=
    Σ \{\ λ i s, s = ε / (b - a) *
    (T[S i] - T[i]) \}\ n); auto. clear H30.
  assert (H29 : ∀ u k, u[S k] - u[O] =
    Σ \{\ λ i v, v = u[S i] - u[i] \}\ k).
  { intros u m. induction m as [|m IHm].
    - simpl. rewrite FunValueR. reflexivity.
    - simpl. rewrite FunValueR. rewrite <- IHm. field. }
  generalize (H29 T n); intros H30.
  clear H29. rewrite H20 in H30.
  rewrite H21 in H30.
  assert (H31 : ∀ k, Σ \{\ λ i s, s = ε / (b - a) *
    (T[S i] - T[i]) \}\ k = ε / (b - a) *
    Σ \{\ λ i s, s = T[S i] - T[i] \}\ k).
  { intros k. induction k as [|k IHk].
    - simpl. rewrite FunValueR. rewrite FunValueR.
      reflexivity.
    - simpl. rewrite FunValueR. rewrite FunValueR.
      rewrite IHk. field. lra. }
  rewrite H31. rewrite <- H30.
  right. field. lra.
Qed.





End A9_2.

Export A9_2.







