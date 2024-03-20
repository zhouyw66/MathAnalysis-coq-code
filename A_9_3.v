Require Export A_9_1.
Require Import Lia.

Module A9_3.

Lemma Rmult_comm_plus: forall A B C, A*B*C = A*C*B.
Proof.
 intros. rewrite Rmult_assoc. 
 replace (B * C) with (C *B);[|apply Rmult_comm].
 rewrite <- Rmult_assoc. auto.
Qed. 

Lemma Rmult_minus_distr_r:
  forall r1 r2 r3, (r2 - r3) * r1 = r2 * r1 - r3 * r1.
Proof. intros; ring. Qed.

Lemma Sn : forall n:nat, 0 < INR(S n).
Proof. 
  intros. rewrite S_INR. apply Rplus_le_lt_0_compat.
  apply pos_INR. lra.
Qed.
Hint Resolve Sn :core. 

Lemma Sn' : forall n: nat, INR (S n) <> 0.
Proof.
  intros. intro. pose proof (Sn n). rewrite H in H0. lra.
Qed.
Hint Resolve Sn' :core.  

Lemma plus_min : forall B C,
  B >= 0 -> C >= 0 -> B + C >= B - C.
Proof.
  intros. lra.
Qed.

Lemma plus_min' : forall B C,
  Abs[B + C] >= Abs[B] - Abs[C].
Proof.
  intros. cut(B + C = B - (- C)); intros;[|lra].
  rewrite H. pose proof (Abs_abs_minus' B (-C)). 
  rewrite <- Abs_eq_neg in H0; lra. 
Qed.
(* 数列的第k项开始一直到第n项的和 *)
Fixpoint Σ'' (T : Seq) (n k: nat) :=
  match k with
  | 0%nat => Σ T n
  | S k => Σ'' T n k - T[k]%nat
  end.

(* n项数列的后k项求和  *)
Fixpoint Σ' (T : Seq) (n k: nat) :=
  match k with
  | 0%nat => 0
  | S k => T[n - k]%nat + Σ' T n k
  end.
  
Fixpoint Σ''' (T : Seq) (n k: nat) :=
  match n with
  | 0%nat => 0
  | S n' => if k <=? n' then T[n] + Σ''' T n' k
            else 0
  end.



Lemma Lemma9_2:∀(f:Fun)(T :Seq)(n:nat)(a b:R),seg T a b (S n) 
 -> (∀k:nat,(0<= k <= n)%nat -> 
 IntervalBoundedFun f (\[ T[k], T[S k] \]))
 -> IntervalBoundedFun f (\[ a, b \]).
Proof. 
  intros. generalize dependent T.
  generalize dependent a. generalize dependent b.
  induction n.
  - intros. pose proof (H0 0%nat). assert ((0 <= 0 <= 0)%nat).
    split; apply Nat.le_refl. apply H1 in H2.
    red in H. destruct H as [_[_[_[H H']]]].
    rewrite H in H2. rewrite H' in H2. auto.
  - intros.   
    assert (seg T a (T[S n]) (S n)).
    { red in H. destruct H as [_[H [H' [H1 H1']]]].  
      red. split. apply Nat.lt_0_succ. split. tauto.
      split. auto. auto. }
    assert (IntervalBoundedFun f (\[ a, T [S n] \])).
    { apply IHn in H1 as H1'. auto.
      intros. apply H0. destruct H2. split. auto.
      apply le_S. auto. }
    pose proof (H0 (S n)).
    assert ((0 <= S n <= S n)%nat).
    { split. apply Nat.lt_le_incl. apply Nat.lt_0_succ.
      auto. }
    apply H3 in H4. clear H3. 
    red in H. destruct H as [_[H [H' [H5 H5']]]]. 
    rewrite H5' in H4.
    red. red in H2, H4.
    destruct H2 as [H2[H6 H6']].
    destruct H4 as [H4[H7 H7']].  
    split; auto. split.  
    + red. intros.
      assert (z ∈ \[ a, T [S n] \] \/ z ∈ \[ T [S n], b \]).
      { destruct (classic (z ∈ \[ a, T [S n] \])).
        left. auto.
        assert (a < T [S n] < b).
        { split. 
          - red in H1. destruct H1 as [H1[H1'[H9[H10 H10']]]].
            rewrite <- H10. assert (T [0%nat] <= T [S n]).
            { apply EqualIncrease. red. split; auto. intros.
              pose proof (H9 n0). left. auto. auto. }
            destruct H11. auto. 
             assert (∀m, T [O] < T [S m]).
             { induction m. pose proof (H9 O). auto.
               pose proof (H9 (S m)). lra. }
               pose proof (H12 n). rewrite H11 in H13. lra.
          - pose proof (H' (S n)). rewrite H5' in H9. auto. } 
      red in H1. destruct H1 as [H1[H1'[H10''[H10 H10']]]].
      right. applyAxiomII H3. apply AxiomII. 
      split. 
      - red in H8. apply NNPP. intro.
        apply H8. apply Rnot_ge_lt in H11. apply AxiomII.
        split; auto. tauto. left. auto.
      - tauto. } 
      destruct H8. apply H6. auto. apply H7. auto.
    + destruct H6' as [M H6']. destruct H7' as [M' H7'].
      exists (Abs[M]+Abs[M']). intros.
      assert (x ∈ \[ a, T [S n] \] \/ x ∈ \[ T [S n], b \]).
      { destruct (classic (x ∈ \[ a, T [S n] \])).
        left. auto.
        assert (a < T [S n] < b).
        { split. 
          - red in H1. destruct H1 as [H1[H1'[H9[H10 H10']]]].
            rewrite <- H10. assert (T [0%nat] <= T [S n]).
            { apply EqualIncrease. red. split; auto. intros.
              pose proof (H9 n0). left. auto. auto. }
            destruct H11. auto. 
             assert (∀m, T [O] < T [S m]).
             { induction m. pose proof (H9 O). auto.
               pose proof (H9 (S m)). lra. }
               pose proof (H12 n). rewrite H11 in H13. lra.
          - pose proof (H' (S n)). rewrite H5' in H9. auto. } 
      red in H1. destruct H1 as [H1[H1'[H10''[H10 H10']]]].
      right. applyAxiomII H3. apply AxiomII. 
      split. 
      - red in H8. apply NNPP. intro.
        apply H8. apply Rnot_ge_lt in H11. apply AxiomII.
        split; auto. tauto. left. auto.
      - tauto. }
      destruct H8. apply H6' in H8. 
      assert (Abs [M] = M).
      { assert ( Abs [f [x]] >=0 ). apply (Abs_Rge0 f[x]).
        assert (M >= 0). lra. apply Abs_ge. auto. }
      rewrite H9. 
      assert (Abs [M'] >= 0). apply Abs_Rge0. lra.
      apply H7' in H8.
      assert (Abs [M'] = M').
      { assert ( Abs [f [x]] >=0 ). apply (Abs_Rge0 f[x]).
        assert (M' >= 0). lra. apply Abs_ge. auto. }
      rewrite H9. 
      assert (Abs [M] >= 0). apply Abs_Rge0. lra.
Qed.

Lemma Lemma9_3:∀(f:Fun)(T :Seq)(n:nat)(a b x:R),seg T a b (S n) 
 -> ~ IntervalBoundedFun f (\[ a, b \]) 
 -> (∃k:nat,(0<= k <= n)%nat /\
  ~ IntervalBoundedFun f (\[ T[k], T[S k] \])).
Proof. 
  intros. apply NNPP. intro. 
  assert (∀ k, (0 <= k <= n)%nat -> 
          IntervalBoundedFun f (\[ T [k], T [S k] \])). 
  { intros. red in H1. apply NNPP. intro. apply H1. 
     exists k. split. auto. auto. } 
  apply (Lemma9_2 f T n a b ) in H2; auto.
Qed.


Lemma Exists_seg :∀ (a b :R) (n : nat),a < b -> ∃T:Seq, 
T =\{\ λ k v, (k = O /\ v = a) \/ (k = S n /\ v = b) \/ 
((k <> O /\ k <> S n) /\ v = INR k * (b - a)/ INR(S n) + a) \}\ /\
seg T a b (S n).
Proof.
  intros a b n J. 
  assert(∃T : Seq, T = \{\ λ k v, (k = O /\ v = a) \/
   (k = S n /\ v = b) \/ ((k <> O /\ k <> S n) /\ 
   v = INR k * (b - a)/ INR(S n) + a) \}\).
  { exists \{\ λ k v, (k = O /\ v = a) \/
   (k = S n /\ v = b) \/ ((k <> O /\ k <> S n) /\
    v = INR k * (b - a)/ INR(S n) + a) \}\; auto. } 
  destruct H as [T]. exists T. split. auto.
  red. split. apply Nat.lt_0_succ.  
  assert(L1:Function T). 
  rewrite H.
  red. intros.
  applyAxiomII' H0. applyAxiomII' H1. destruct H0,H1.
  destruct H0,H1; rewrite H2; auto.
  destruct H0,H1. rewrite H0 in H1.
  destruct H1. discriminate H1.
  destruct H1. destruct H1. contradiction. destruct H0. 
  destruct H0, H1. rewrite H0 in H1. discriminate H1.
  destruct H0, H1. destruct H0. rewrite H1 in H0. 
  contradiction. destruct H0, H1. destruct H0,H1.
  rewrite H2. auto. destruct H0,H1.
  destruct H1. rewrite H0 in H4. contradiction.
  destruct H0. destruct H0,H1. rewrite H1 in H3. contradiction.
  destruct H0, H1. rewrite H2. auto.
  split. red. split; auto.
  apply AxiomI. rewrite H.
  split; intros. apply AxiomII . auto.
  apply AxiomII. 
  pose proof (Nat.eq_dec z O).
  destruct H1. exists a. 
  apply AxiomII'. left.
  split; auto. 
  pose proof (Nat.eq_dec z (S n)).
  destruct H1. exists b.
  apply AxiomII'. right.
  left. split; auto.
  exists (INR z * (b - a) / INR (S n) + a).
  apply AxiomII'. right. right.
  split; auto. split. intros.
  assert(L2:T [0%nat]  = a).
  { rewrite H. apply f_x. rewrite <- H. auto.
    apply AxiomII. exists 0%nat,a. split; auto. }
  assert(L3:T [S n] = b).
  { rewrite H. apply f_x. rewrite <- H. auto.
    apply AxiomII. exists (S n),b. split; auto. }
  assert(L4:∀k,(k <> 0%nat /\ k <> S n) ->T[k] = INR k * (b - a) / INR (S n) + a). 
  { intros. rewrite H. apply f_x.
    rewrite <- H. auto. apply AxiomII. 
    exists k0, (INR k0 * (b - a) / INR (S n) + a).
    auto. }
  pose proof (Nat.eq_dec k O).
  destruct H0. rewrite e.
  pose proof (Nat.eq_dec n O). destruct H0. 
  rewrite e0 in L3. rewrite L2; rewrite L3; auto.
  assert(1%nat <> 0%nat /\ 1%nat <> S n ).
  { split. auto.
    intro. 
    apply Nat.neq_0_r in n0. destruct n0. 
    rewrite H1 in H0. inversion H0. } 
  apply L4 in H0. rewrite L2. rewrite H0.
  assert (INR 1 * (b - a) / INR (S n) > 0).
  { apply Rmult_gt_0_compat. apply Rmult_gt_0_compat.
    simpl. lra. lra. apply Rinv_0_lt_compat.
    rewrite S_INR. rewrite Rplus_comm.
    apply Rplus_lt_le_0_compat. lra. apply pos_INR. } 
  lra.
  pose proof (Nat.eq_dec k (S n)).
  destruct H0. rewrite e. 
  rewrite L3. assert(S (S n) <> 0%nat /\ S (S n) <> S n).
  { split. rewrite <- e. apply Nat.neq_succ_0.
    apply Nat.neq_succ_diag_l. }
  apply L4 in H0. rewrite H0.    
  assert (b - a < INR (S (S n)) * (b - a) / INR (S n)).
  { unfold Rdiv.  
    apply (Rmult_lt_reg_r (INR (S n)) (b - a) 
    (INR (S (S n)) * (b - a) * / INR (S n))). 
    rewrite S_INR. apply Rplus_le_lt_0_compat.  
    apply pos_INR. lra. rewrite Rmult_assoc.  
    rewrite Rinv_l. rewrite Rmult_assoc. rewrite Rmult_1_r.
    rewrite Rmult_comm. apply Rmult_lt_compat_r. lra.
    apply lt_INR. apply Nat.lt_succ_diag_r. 
    apply not_0_INR. apply Nat.neq_succ_0. } 
  lra. 
  rewrite (L4 k); auto. 
  pose proof (Nat.eq_dec (S k) (S n)). 
  destruct H0. rewrite e. rewrite L3. inversion e.
  apply (Rplus_lt_reg_r (-a) (INR n * (b - a) / INR (S n) + a)
  (b)).
  replace (INR n * (b - a) / INR (S n) + a + - a) 
  with (INR n * (b - a) / INR (S n));[|lra].
  replace (b + - a) with (b - a);[|lra]. 
  unfold Rdiv. rewrite Rmult_comm_plus.
  apply (Rmult_lt_reg_r (/(b - a)) 
  (INR n * / INR (S n) * (b - a)) (b - a)).
  apply Rinv_0_lt_compat; lra.
  rewrite Rmult_assoc. rewrite Rinv_r.
  rewrite Rmult_1_r. 
  apply (Rmult_lt_reg_r (INR (S n)) 
  (INR n * / INR (S n)) (1)). 
  auto. rewrite Rmult_assoc.
  rewrite Rinv_l. rewrite Rmult_1_l. rewrite Rmult_1_r.
  apply lt_INR. apply Nat.lt_succ_diag_r. auto. lra. 
  pose proof (L4 (S k)). 
  assert (S k <> 0%nat /\  S k <> S n).
  { split. apply Nat.neq_succ_0. auto. }
  apply H0 in H1. rewrite H1.
  apply (Rplus_lt_reg_r (-a) (INR k * (b - a) / INR (S n) + a)
  (INR (S k) * (b - a) / INR (S n) + a)).
  replace (INR k * (b - a) / INR (S n) + a + - a) 
  with (INR k * (b - a) / INR (S n));[|lra].
  replace (INR (S k) * (b - a) / INR (S n) + a + - a) 
  with (INR (S k) * (b - a) / INR (S n));[|lra].
  unfold Rdiv. 
  apply (Rmult_lt_reg_r (INR (S n)) 
  (INR k * (b - a) * / INR (S n)) 
   (INR (S k) * (b - a) * / INR (S n))). auto.
  rewrite Rmult_assoc. rewrite Rinv_l.
  rewrite Rmult_1_r. 
  rewrite Rmult_assoc. rewrite Rinv_l. rewrite Rmult_1_r.
  apply Rmult_lt_compat_r. 
  lra. apply lt_INR. apply Nat.lt_succ_diag_r. auto. auto. 
  split.  
  apply f_x. auto. rewrite H. 
  apply AxiomII. exists 0%nat, a. auto.
  rewrite H. apply f_x. rewrite <- H. auto.
  apply AxiomII. exists (S n), b. auto.
Qed.




Lemma a_b_c : ∀ T a b n k, seg T a b (S n) ->
  (0 <= k <= n)%nat -> \[ T [k], T [S k] \] ⊂ \[ a, b \].
Proof. 
  intros. red in H. destruct H as [H[H1[H2[H3 H4]]]].
  assert ((IsSeq T /\ (∀ (n1 n2 : nat), (n1 < n2)%nat ->
           T[n1] <= T [n2]))).
  apply EqualIncrease. red. split; auto. left. auto.
  destruct H5 as [H5 H6].
  pose proof (Nat.eq_0_gt_0_cases k).
  destruct H7.
  - rewrite H7. rewrite H3. red. intros.
    applyAxiomII H8. apply AxiomII. split. tauto.
    rewrite <- H4. rewrite H7 in H0. destruct H0.
    destruct H9. tauto. 
    assert ((1 < S(S m))%nat). apply lt_n_S.
    apply Nat.lt_0_succ. apply H6 in H10. lra.
  - apply H6 in H7 as H8. rewrite H3 in H8.
    red. intros. applyAxiomII H9. apply AxiomII. split.
    lra. rewrite <- H4. destruct H9.
    destruct H0. destruct H11. auto.
    assert ((S k < S (S m))%nat).
    apply lt_n_S. apply le_lt_n_Sm. auto.
    apply H6 in H12. lra.
Qed.
  


Lemma exists_n : ∀ a b δ, b > a -> δ > 0 -> ∃ n, (b-a)/INR(S n) < δ.
Proof.
  intros. 
  assert ((b-a) > 0). lra. pose proof H0 as H0'.
  apply (Archimedes δ (b-a)) in H0; auto.
  destruct H0. exists x.
  pose proof (gt_0_eq x). destruct H2.
  - assert ((b - a) / INR x < δ). 
    { assert (INR x > 0).
      apply lt_0_INR; auto.
      apply (Rmult_lt_reg_r (INR x) ((b - a) / INR x) δ); auto.
      unfold Rdiv. rewrite Rmult_assoc. rewrite Rinv_l; lra. }
    assert ((b - a) < δ * INR x). lra.
    assert ((b - a) < δ * INR (S x)). rewrite S_INR.
    rewrite Rmult_plus_distr_l. lra.
    apply (Rmult_lt_reg_r (INR (S x)) ((b - a) / INR (S x)) δ);
    auto. rewrite S_INR. apply lt_0_INR in H2. 
    unfold Rdiv. rewrite Rmult_assoc.
    rewrite Rinv_l. lra. lra.
  - rewrite <- H2. simpl. rewrite <- H2 in H0.
    simpl in H0. lra.
Qed.

  

Lemma Lemmasum_minus':∀(ξ ξ':Seq)(n :nat)(x:R),(n > 0)%nat ->
(∀k,(k < n)%nat -> ξ'[k] = ξ[k])
-> Σ ξ' ((n-1)%nat) = Σ ξ (n-1)%nat.
Proof. 
  intros. 
  induction n. inversion H.
  destruct (Nat.eq_dec n 0%nat).
  subst n. simpl. apply H0; auto.
  assert((n > 0)%nat). { apply Nat.neq_0_lt_0. auto. }
  simpl. assert(Σ ξ' (n - 1) = Σ ξ (n - 1)).
  apply IHn; auto. 
  assert((n < S n)%nat). 
  apply Nat.lt_succ_diag_r.
  pose proof (Lemma_6_3_7 n ξ H1).
  repeat rewrite Nat.sub_0_r.
  rewrite H4. 
  pose proof (Lemma_6_3_7 n ξ' H1).
  rewrite H5. 
  apply H0 in H3. lra.
Qed.
  

   
Lemma Lemmasum_minus:∀(ξ ξ':Seq)(k n:nat)(x:R),(0 <= k <= n)%nat ->
Function ξ -> ξ = \{\λ m v,m = k /\ v = x \/ m<>k /\v = ξ'[m] \}\
-> Σ ξ' n - ξ'[k] = Σ ξ n - ξ[k].
Proof.
  intros. generalize dependent k. induction n.
  - intros. destruct (Nat.eq_dec k 0%nat).
    subst k. simpl. lra. inversion H. 
    apply Nat.le_antisymm in H2; auto. rewrite H2 in n.
    contradiction.
  - intros. destruct (Nat.eq_dec k (S n)).
    subst k. simpl. cut(Σ ξ' n = Σ ξ n); intros.
    lra. assert((S n > 0)%nat). apply gt_Sn_O.
    assert(∀k : nat,(k < S n)%nat -> ξ' [k] = ξ [k]).
    { intros.
      symmetry. apply f_x; auto. rewrite H1.
      apply AxiomII'. right. split; auto. 
      apply Nat.lt_neq in H3. auto. }
    pose proof (Lemmasum_minus' ξ ξ' (S n) x H2 H3).
    simpl in H4. repeat rewrite Nat.sub_0_r in H4; auto.
    assert((0 <= k <= n)%nat).
    { destruct H. split; auto.   
      assert ((k < S n)%nat).
      { apply not_eq in n0. destruct n0; auto. inversion H2.
        rewrite H4 in H3. apply Nat.lt_irrefl in H3. lra.
        apply le_lt_n_Sm. auto.  }
      apply lt_n_Sm_le. auto. } 
    apply IHn in H2; auto. simpl. 
    assert(ξ' [S n] = ξ [S n]).
    { symmetry. apply f_x; auto. rewrite H1.
      apply AxiomII'. right. split; auto. } lra.
Qed.
   
(* 定理9.2 可积的必要条件 *)
Theorem Theorem9_2 : forall (f :Fun) (a b J:R),Function f -> 
a < b-> defIntegral f a b J-> IntervalBoundedFun f (\[ a, b \]).
Proof. 
  intros. red in H1.
  destruct H1 as [_ [_ [H1 H2]]].
  assert(∃M,M > 0 /\ M > Abs[J]).
  { exists  (2 * Abs[J] + 1). 
    pose proof(Abs_Rge0 J); lra.  }
  destruct H3 as [M[H3 H3']].
  assert(M - Abs[J] > 0). lra.
  apply H2 in H4 as H4'. destruct H4' as [δ [H6 H5]].
  assert (∃ n, (b-a)/INR(S n) < δ).
  { apply exists_n. lra. auto. } clear H2.
  destruct H7 as [n]. 
  pose proof (Exists_seg a b n H0). 
  destruct H7 as [T [H8 H9]].
  assert(L1:∀n', T[S n'] - T[n'] = (b - a) / INR (S n)).
  { intros. red in H9. destruct H9 as [_[H9 _]].
    red in H9. assert(T [0%nat] = a). 
    apply f_x. tauto. rewrite H8. apply AxiomII'.
    left; auto. assert(T [S n] = b). 
    apply f_x. tauto. rewrite H8. apply AxiomII';
    right; left; auto. 
    assert(∀n0,n0 <> 0%nat /\ n0 <> (S n) -> T [n0] = INR n0 * (b - a) 
    / INR (S n) + a). 
    { intros. apply f_x. tauto. rewrite H8. apply AxiomII'.
      right. right. split; auto. }
    destruct (Nat.eq_dec n' 0%nat). 
    rewrite e. rewrite H7.  
    destruct (Nat.eq_dec n 0%nat). subst n.
    rewrite H10. 
    unfold Rdiv; rewrite RMicromega.Rinv_1; auto.
    assert(1%nat <> 0%nat /\ 1%nat <> S n).
    { split. apply Nat.neq_succ_diag_l. 
      apply not_eq_S; auto. }
    apply H11 in H12. rewrite H12. 
    rewrite Rmult_1_l. unfold Rminus.
    rewrite Rplus_assoc. rewrite Rplus_opp_r. lra.
    destruct (Nat.eq_dec n' (S n)). subst n'.
    rewrite H10. 
    assert((S (S n)) <> 0%nat /\ (S (S n)) <> S n).
    { split. apply Nat.neq_succ_0. 
      apply Nat.neq_succ_diag_l. }
    apply H11 in H12. rewrite H12.  
    cut(INR (S (S n))= INR (S n) +1); intros.
    rewrite H13. unfold Rdiv;
    repeat rewrite Rmult_plus_distr_r. 
    rewrite Rinv_r_simpl_m. lra. 
    apply not_0_INR. apply Nat.neq_succ_0.
    rewrite (S_INR (S n)). auto.
    pose proof(H11 n'). 
    rewrite H12; [|split; auto].
    destruct (Nat.eq_dec n' n).
    subst n'. rewrite H10. unfold Rminus.
    rewrite Ropp_plus_distr.
    rewrite <- Rplus_comm.
    rewrite (Rmult_eq_reg_r (INR(S n)) 
    (- (INR n * (b + - a) / INR (S n)) + - a + b)
    ((b + - a) / INR (S n))). auto.
    assert ((- (INR n * (b + - a) / INR (S n)) + - a + b) =
    - (INR n * (b + - a) / INR (S n)) + (- a + b)).
    lra. rewrite H13. clear H13.
    rewrite Rmult_plus_distr_r. unfold Rdiv.
    replace ((b + - a) * / INR (S n) * INR (S n)) with
    ((b + - a) * INR (S n) * / INR (S n)).
    rewrite Rinv_r_simpl_l.  
    replace (- (INR n * (b + - a) * / INR (S n)) * INR (S n))
    with (- (INR n * (b + - a))).
    replace (- a + b) with (b + - a). 
    rewrite Ropp_mult_distr_l.
    replace ((b + - a) * INR (S n)) with (INR (S n) *(b + - a)).
    rewrite <- Rmult_plus_distr_r.
    replace (- INR n + INR (S n)) with (INR 1). simpl. lra. 
    replace (INR (S n)) with (INR (1 + n)).
    replace (INR (1 + n)) with (INR 1 + INR n).
    lra. rewrite <- S_O_plus_INR. auto.  
    replace (1 + n)%nat with (S n). auto.
    simpl. auto. lra. lra. rewrite Ropp_mult_distr_l_reverse.
    apply Ropp_eq_compat. 
    replace (INR n * (b + - a) * / INR (S n) * INR (S n)) 
    with (INR n * (b + - a) * (/ INR (S n) * INR (S n))).
    rewrite Rinv_l. lra. apply not_0_INR. auto. lra.
    apply not_0_INR. auto. rewrite Rmult_assoc.
    rewrite Rmult_assoc. apply Rmult_eq_compat_l. 
    apply Rmult_comm. apply not_0_INR. auto. 
    apply not_eq_S in n2. rewrite (H11 (S n')).
    apply (Rmult_eq_reg_r (INR (S n))
    (INR (S n') * (b - a) / INR (S n) + a - (INR n' * (b - a) /
     INR (S n) + a) )
    ((b - a) / INR (S n))).
    replace (INR (S n') * (b - a) / INR (S n) + a - 
    (INR n' * (b - a) / INR (S n) + a)) with 
    (INR (S n') * (b - a) / INR (S n) + 
    (a - (INR n' * (b - a) / INR (S n) + a))). 
    rewrite Rmult_plus_distr_r. 
    rewrite Rmult_minus_distr_r.
    rewrite Rmult_plus_distr_r. 
    replace (INR (S n') * (b - a) / INR (S n) * INR (S n) ) 
    with (INR (S n') * (b - a)).
    replace (INR n' * (b - a) / INR (S n) * INR (S n)) 
    with (INR n' * (b - a)).
    replace ((b - a) / INR (S n) * INR (S n)) with ((b - a)).
    replace ((a * INR (S n) - (INR n' * (b - a) + 
    a * INR (S n)))) with (- INR n' * (b - a)).
    rewrite <- Rmult_plus_distr_r.
    replace ((INR (S n') + - INR n')) with (INR 1).
    simpl. lra. replace (S n') with (1 + n')%nat.
    rewrite (S_O_plus_INR n'). lra. simpl. auto.
    lra. unfold Rdiv. rewrite Rmult_assoc. 
    rewrite Rinv_l. lra. apply not_0_INR. auto.
    unfold Rdiv. rewrite Rmult_assoc. 
    rewrite Rinv_l. lra. apply not_0_INR. auto.
    unfold Rdiv. rewrite Rmult_assoc. 
    rewrite Rinv_l. lra. apply not_0_INR. auto.
    lra. apply not_0_INR. auto. split.
    apply Nat.neq_succ_0. auto.  }
  apply NNPP. intro I1.  
  assert(∃k,(0<= k <= n)%nat /\ ~ (IntervalBoundedFun f (\[ T[k], T[S k] \]))). 
  { apply (Lemma9_3 f T n a b); auto. }
  destruct H7 as [k[H10 H11]].   
  assert(∀M : R,∃x : R,x ∈ \[ T [k], T [S k] \] /\ Abs [f [x]] > M).
  { intros. red in H11.
    apply NNPP. intro. apply H11.
    red. split; auto. split. 
    assert (\[ T [k], T [S k] \] ⊂ \[ a, b \]).
    apply (a_b_c T a b n k); auto. 
    red. intros. apply H1. apply H12. auto. exists M0.
    intros. apply NNPP. intro.
    apply H7. exists x. split; auto.
    apply Rnot_le_gt in H13. auto. }
  assert(∃ξ:Seq, ξ = \{\λ m v,v = T[m] \}\).
  { exists(\{\λ m v,v = T[m] \}\). split; auto.  }   
  destruct H12 as [ξ' H13]. 
  assert(∃G' :R, G' = Σ \{\λ(i : nat)(s : R),s = f [ξ'[i]]* (T[S i] - T[i]) \}\ n
   - f [ξ'[k]]* (T[S k] - T[k])).
   { exists (Σ \{\ λ(i : nat)(s : R),s = f [ξ' [i]] * (T [S i] - T [i]) \}\ n
    - f [ξ' [k]] * (T [S k] - T [k])); auto. } 
  destruct H12 as [G']. 
  assert((M + Abs[G'])/ (T[S k] - T[k])> 0).
  { unfold Rdiv. apply Rmult_gt_0_compat.
    pose proof (Abs_Rge0 G'). lra. 
    apply Rinv_0_lt_compat. red in H9. 
    destruct H9 as [_[_[H9 _]]]. 
    pose proof (H9 k). lra. } 
  pose proof (H7 ((M + Abs[G']) / (T [S k] - T [k]))).
  destruct H15 as [x[H16 H17]]. 
  assert(∃ξ:Seq, ξ = \{\λ m v,m = k /\ v = x \/ m<>k /\v = T[m] \}\ 
  /\ segPoint T ξ).
  { exists \{\λ m v,m = k /\ v = x \/ m<>k /\ v = T[m] \}\. split; auto.
    assert(Function \{\ λ(m : nat)(v : R),m = k /\ v = x \/ m <> k
    /\ v = T [m] \}\). 
   { unfold Function.
   intros. applyAxiomII' H15. applyAxiomII' H18.
   destruct H15; destruct H18. lra. 
   destruct H15; destruct H18; contradiction.
   destruct H15; destruct H18; contradiction.
   lra. } unfold segPoint. 
   split. red. split.
   auto. apply AxiomI. split; intros.
   apply AxiomII; auto. apply AxiomII.
   destruct (Nat.eq_dec z k). 
   exists x. apply AxiomII'; auto.
   exists T[z]. apply AxiomII'; auto.
   intros. destruct (Nat.eq_dec n0 k).
   assert(\{\ λ(m : nat)(v : R),m = k /\ v = x \/ m <> k /\ v = T [m] \}\
    [k] = x). { apply f_x; auto. apply AxiomII'. left; auto.  }
    rewrite e. rewrite H18. applyAxiomII H16. lra.
   assert(\{\ λ(m : nat)(v : R),m = k /\ v = x \/ m <> k /\ v = T [m] \}\
    [n0] = T[n0]). { apply f_x; auto. apply AxiomII'. right; auto.  }
   rewrite H18. destruct H9 as [_[_[H9 _]]]. 
    pose proof (H9 n0). split; lra. } 
  destruct H15 as [ξ [H15 H15']]. 
  assert(mold T (S n) < δ).
  { apply Lemma9_1_1 in H9 as H9'.
    destruct H9' as [x' H9']. 
    assert (NotEmpty \{ λ x, segMold T (S n) x \}).
    { exists x'. apply AxiomII. assumption. }
    apply AxiomcR in H18. applyAxiomII H18.
    destruct H18 as [H19' H20]. 
    unfold mold. destruct H19' as [k'[H22 H21]].
    rewrite <- H21. pose proof (L1 k'); lra. }
  pose proof (H5 T ξ n H9 H15' H18). 
  assert(∃G :R, G = Σ \{\ λ(i : nat)(s : R),s = f [ξ [i]] * (T [S i] - T [i])
   \}\ n - f [ξ[k]] * (T [S k] - T [k])).
  {  exists (Σ \{\ λ(i : nat)(s : R),s = f [ξ [i]] * (T [S i] - T [i]) \}\ 
     n - f [ξ [k]] * (T [S k] - T [k])); auto. }
  destruct H20 as [G].
  assert(Σ \{\ λ(i : nat)(s : R),s = f [ξ [i]] * (T [S i] - T [i]) \}\ n = 
  f [ξ [k]] * (T [S k] - T [k]) + G). 
  { rewrite H20; lra.  }
  assert(G = G'). 
  rewrite H20. rewrite H12. 
  assert(∃x', x' = f [ξ [k]] * (T [S k] - T [k])).
  { exists (f [ξ [k]] * (T [S k] - T [k])); auto. }
  destruct H22. 
  assert(∃F, F = \{\ λ(i : nat)(s : R),s = f [ξ' [i]] * (T [S i] - T [i]) \}\).
  { exists (\{\ λ(i : nat)(s : R),s = f [ξ' [i]] * (T [S i] - T [i]) \}\);
    auto. } 
  destruct H23 as [F']. 
  destruct H15' as [[K1 K2] _].
  assert(K3:∀x', x' <> k -> ξ'[x'] = ξ [x']).
  {  intros. rewrite H13; rewrite FunValueR. symmetry.
     apply f_x; auto. rewrite H15. apply AxiomII'.
     right; auto. }
  assert(\{\ λ(i : nat)(s : R),s = f [ξ [i]] * (T [S i] - T [i]) \}\= 
    \{\ λ(i : nat)(s : R),i = k /\ s =x0 \/ i<>k /\ s = F'[i] \}\ ).
  { apply AxiomI. split; intros. applyAxiomII H24.
   destruct H24 as [x'[y'[H24 H25]]].
   apply AxiomII. exists x', y'. split; auto.
   destruct(classic (x' = k)). subst k.
   left; split; auto. rewrite H22; auto.
   right; split; auto. rewrite H23. rewrite FunValueR; auto.
   apply K3 in H26 as H27.
   rewrite H27; auto. applyAxiomII H24.
   destruct H24 as [x'[y'[H24 [H25 |H25]]]].
   apply AxiomII. exists x', y'. split; auto.
   destruct H25; subst x'. rewrite H26; auto.
   apply AxiomII. exists x', y'. split; auto.
   destruct H25. rewrite H23 in H26. 
   rewrite FunValueR in H26. auto. 
   apply K3 in H25. rewrite <- H25. auto. }
   rewrite H24. symmetry. rewrite <- H23.
   assert(F'[k] = f [ξ' [k]] * (T [S k] - T [k]) ).
   rewrite H23. rewrite FunValueR; auto.
   rewrite <- H25.
   assert(∃F, F = \{\ λ(i : nat)(s : R),i = k /\ s = x0 \/ i <> k /\ 
   s = F' [i] \}\).
   { exists (\{\ λ(i : nat)(s : R),i = k /\ s = x0 \/ i <> k /\ 
     s = F' [i] \}\); auto. }
   destruct H26 as [F]. rewrite <- H26.
   assert(Function F). 
   { rewrite H26. unfold Function.
     intros. applyAxiomII' H27. applyAxiomII' H28.
     destruct H27; destruct H28. lra. 
     destruct H27; destruct H28; contradiction.
     destruct H27; destruct H28; contradiction. lra. } 
   assert(F[k] = f [ξ [k]] * (T [S k] - T [k])).
   { apply f_x; auto. rewrite H26. apply AxiomII'.
     left; split; auto. }
   rewrite <- H28. 
   apply (Lemmasum_minus _ _ _ _ x0); auto.
  rewrite H21 in H19. 
  pose proof (plus_min' (f [ξ [k]] * (T [S k] - T [k])) G).
  assert(ξ [k] = x).
  { destruct H15'. destruct H24. apply f_x; auto. 
    rewrite H15; apply AxiomII'; left; auto.  } 
  subst x.
  assert(Abs [f [ξ [k]] * (T [S k] - T [k])] - Abs [G] > (M + Abs[G']) / 
  (T [S k] - T [k]) * (T [S k] - T [k]) - Abs [G]).
  { cut(T [S k] - T [k] > 0). intros L4.
    apply (Rplus_gt_reg_l (Abs [G]) 
    (Abs [f [ξ [k]] * (T [S k] - T [k])] - Abs [G])
    ((M + Abs [G']) / (T [S k] - T [k]) * (T [S k] - T [k]) - Abs [G])).
    replace (Abs [G] + (Abs [f [ξ [k]] * (T [S k] - T [k])]
    - Abs [G])) with (Abs [f [ξ [k]] * (T [S k] - T [k])]).
    replace (Abs [G] + ((M + Abs [G']) / (T [S k] - T [k]) * 
    (T [S k] - T [k]) - Abs [G])) with 
    ((M + Abs [G']) / (T [S k] - T [k]) * (T [S k] - T [k])).
    replace ((M + Abs [G']) / (T [S k] - T [k]) * 
    (T [S k] - T [k])) with ((M + Abs [G'])).
    apply (Rmult_gt_compat_r (T [S k] - T [k])
    Abs [f [ξ [k]]] ((M + Abs [G']) / (T [S k] - T [k]))) in H17; auto.
    unfold Rdiv in H17. 
    replace ((M + Abs [G']) * / (T [S k] - T [k]) * 
    (T [S k] - T [k])) with (M + Abs [G']) in H17.
    replace (Abs [f [ξ [k]]] * (T [S k] - T [k])) with 
    (Abs [f [ξ [k]] * (T [S k] - T [k])]) in H17. auto.
    rewrite Abs_mult. replace (Abs [T [S k] - T [k]]) 
    with ( (T [S k] - T [k])); auto.
    rewrite Abs_gt; auto.
    rewrite Rmult_assoc; rewrite Rinv_l; lra.
    unfold Rdiv. rewrite Rmult_assoc; rewrite Rinv_l; lra.
    lra. lra. red in H9. destruct H9 as [_[_[H9 _]]]. 
    pose proof (H9 k). lra. }
  pose proof (Abs_abs_minus' (f [ξ [k]] * (T [S k] - T [k]) + G) J).
  assert(Abs [f [ξ [k]] * (T [S k] - T [k]) + G] < M). lra. 
  assert((M + Abs[G']) / (T [S k] - T [k]) * (T [S k] - T [k]) - Abs [G] = M).
  rewrite <- H22. unfold Rdiv. 
  rewrite Rmult_assoc; rewrite Rinv_l. lra.
  red in H9. destruct H9 as [_[_[H9 _]]]. 
  pose proof (H9 k). lra. lra.
Qed.
   
End A9_3.

Export A9_3.
