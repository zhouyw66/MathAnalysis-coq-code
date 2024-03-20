Require Export A_9_3.
Require Import Lia.

Module A9_6.

(* 函数值域的上下确界 *)
Definition sup_f' (D : sR)(f : Fun)(M : R):= 
∃U l,(MinValue f D l) /\ (MaxValue f D U)
/\ (sup (\[ l , U \]) M).

(* 函数值域的上下确界 *)
Definition sup_f (D : sR)(f : Fun)(Mi : R):= 
(sup \{λ s, ∃x, s = f[x] /\ x ∈ D\}  Mi).

Definition inf_f (D : sR)(f : Fun)(m : R):= 
∃U l,(MinValue f D l) /\ (MaxValue f D U)
/\ (inf (\[ l , U \]) m).


(* f关于分割T的上和 *)
Definition Up_sum (f : Fun)(T : Seq) (a b :R) (ST: R)(n : nat) := 
seg T a b (S n) /\ (∃M: Seq,∀ i, (i <= n)%nat ->  sup_f (\[T[i] , T[S i] \]) f M[i] /\ ST = (Σ \{\λ i s, s = M[i] * (T[S i]- T[i]) \}\ n)).

(* f关于分割T的下和 *)
Definition Low_sum (f : Fun)(T : Seq) (a b :R) (sT: R)(n : nat) := 
seg T a b (S n) /\ (∃m: Seq,∀ i, (i <= n)%nat ->  inf_f (\[T[i] , T[S i] \]) f m[i] /\ sT = (Σ \{\λ i s, s = m[i] * (T[S i]- T[i]) \}\ n)).



Lemma Lemma9_1: ∀(n : nat)(f g: Seq), (∀ i, (i <= n)%nat -> f[i] >= g [i]) ->
Σ f n  >= Σ g n.
Proof.
  intros. induction n.
  - simpl. pose proof (H 0%nat). apply H0. lia.
  - simpl. apply Rplus_ge_compat. apply IHn.
    intros. apply H. lia. apply H. lia.
Qed.
 

Lemma Lemma9_1': ∀(n : nat)(f g: Seq), (∀ i, (i <= n)%nat -> f[i] > g [i]) ->
Σ f n  > Σ g n.
Proof.
  intros. induction n.
  - simpl. pose proof (H 0%nat). apply H0. lia.
  - simpl. apply Rplus_gt_compat. apply IHn.
    intros. apply H. lia. apply H. lia.
Qed.

Lemma Lemma9_1'': ∀(n : nat)(A B: Seq),
 (∀ x,(x < S n)%nat -> A [x] = B [x]) -> Σ A n = Σ B n.
Proof.
  intros. induction n. 
  simpl. rewrite H. auto. lia.
  simpl. rewrite IHn.
  pose proof (H (S n)).
  rewrite H0. auto. auto.
  intros.
  rewrite H. auto. lia.
Qed.

(* 上和是全体积分和的上界 *) 
Lemma Lemma9_6_1: ∀ (f : Fun)(T ξ: Seq) (a b :R) (n : nat)(ST: R), Up_sum f T a b ST n -> segPoint T ξ -> 
ST >= (Σ \{\λ i s, s = f[ξ[i]%nat] * (T[S i]- T[i]) \}\ n).
Proof.
  intros. unfold Up_sum in H.
  destruct H. unfold segPoint in H0.
  destruct H0 as [H0 H2].
  destruct H1 as [M].
  assert (L3:∀i : nat,(i <= n)%nat -> f [ξ [i]] <= M[i]).
  { intros. apply H1 in H3. destruct H3.
    unfold sup_f in H3. destruct H3. 
    unfold Upper in H3. apply H3. apply AxiomII.
    exists(ξ [i]). split; auto. apply AxiomII. 
    pose proof (H2 i); lra. }
  assert (L5:∀i : nat,(i <= n)%nat -> \{\ λ(i : nat)(s : R),s = f [ξ [i]] * (T [S i] - T [i]) \}\[i] <= \{\ λ(i0 : nat)(s : R),s = M [i]%nat * (T [S i0] - T [i0]%nat) \}\[i]).
  { intros. repeat rewrite FunValueR. 
    apply L3 in H3. 
    apply Rmult_le_compat_r; auto. 
    pose proof (H2 i). lra. }
  assert ((n <= n)%nat). apply Nat.le_refl.
  apply H1 in H3 as H3'. 
  destruct H3' as [H3' H4]. 
  rewrite H4. apply Lemma9_1.  
  intros. apply L5 in H5 as H5'.
  repeat rewrite FunValueR. 
  apply L3 in H5 as L3'. pose proof (H2 i). 
  apply Rmult_ge_compat_r; lra.
Qed.




Lemma Lemma1_1:∀(a b :R),a <= b -> sup (\[a,b\]) b.
Proof.
  intros. unfold sup. split. unfold Upper.
  intros. applyAxiomII H0. lra.
  intros. exists b. split; auto. 
  apply AxiomII; lra.
Qed. 

Lemma Lemma1_2:∀(a b :R),a <= b -> inf (\[a,b\]) a.
Proof.
  intros. unfold inf. split. unfold Lower.
  intros. applyAxiomII H0. lra.
  intros. exists a. split; auto. 
  apply AxiomII; lra.
Qed.

Lemma a_b : ∀ T a b n , seg T a b n -> a <= b.
Proof. 
  intros. red in H. destruct H as [H[H1[H2[H3 H4]]]].  
  rewrite <- H3. rewrite <- H4.
  apply EqualIncrease. red. split. auto.
  intros. pose proof (H2 n0). left. auto. auto.
Qed.

Lemma a_b' : ∀ T a b n , seg T a b (S n) -> a < b.
Proof.
  intros. pose proof (a_b).
  pose proof H as H'. 
  destruct H as [H[H1[H2[H3 H4]]]].
  pose proof (H0 T a b (S n)). apply H5 in H'. destruct H'.
  - auto.
  - rewrite <- H3 in H6. rewrite <- H4 in H6.
    assert  (∀m, T [O] < T [S m]).
    induction m. pose proof (H2 O). auto.
    pose proof (H2 (S m)). lra.
    pose proof (H7 n). rewrite H6 in H8. lra.
Qed. 


Lemma Lemma9_6_1_1 : ∀ M T A n, 
 Σ \{\ λ i m, m = M[i] * (T[S i] - T[i]) - 
 A * (T[S i] - T[i])\}\ n = 
 Σ \{\ λ i m, m = M[i] * (T[S i] - T[i]) \}\ n 
 - A * Σ \{\ λ i m, m = (T[S i] - T[i]) \}\ n.
Proof.
  intros. 
  induction n. simpl.
  - repeat rewrite FunValueR. auto.
  - simpl. rewrite IHn.
  assert  (\{\ λ i m, m = M [i] * (T [S i] - T [i]) - 
             A * (T [S i] - T [i]) \}\ [S n] = 
             \{\ λ i m, m = M [i] * (T [S i] - T [i]) \}\[S n] 
             - A * \{\ λ i m, m = (T [S i] - T [i]) \}\ [S n]).
  { repeat rewrite FunValueR. auto. }
  rewrite H. lra.
Qed.

 Lemma Lemma9_6_1_2 : ∀ T n a b, seg T a b (S n) ->
 Σ \{\ λ i m, m = T [S i] - T [i] \}\ n = b - a .
Proof.
  intros. red in H. destruct H as [H[H1[H2[H3 H4]]]].
  assert  ( ∀ u k, u[S k] - u[O] =
    Σ \{\ λ i v, v = u[S i] - u[i] \}\ k). 
  { intros u m. induction m as [|m IHm].
    - simpl. rewrite FunValueR. reflexivity.
    - simpl. rewrite FunValueR. rewrite <- IHm. field. }
   generalize (H0 T n); intros H5.
   rewrite H3, H4 in H5. auto.
Qed.

(* 全体积分和 *)
Definition All_integralsum (f : Fun)(T : Seq) (a b :R)(n : nat)(Sum :sR) :Prop := seg T a b (S n) /\ (∀(ξ:Seq), segPoint T ξ  /\ Sum = \{λ sum :R, sum = (Σ \{\λ i s, s = f[ξ[i]] * (T[S i]- T[i]) \}\ n) \}).

(* 性质1 上和是全体积分和的最小上界 *)
Fact Fact9_6_1 : ∀ (f : Fun)(T : Seq) (ST a b :R) (n : nat)(Sum : sR),
Up_sum f T a b ST n -> All_integralsum f T a b n Sum -> sup Sum ST.
Proof.  
  intros. pose proof H0 as H0'. red in H0.
  destruct H0 as [H0 H2].
  unfold seg in H0. destruct H0 as [H0[H3[H4[H5 H6]]]].
  pose proof H as H'.
  unfold Up_sum in H. destruct H as [H[M H7]].
  assert (∃ξ : Seq,ξ = \{\ λ n v, ( n = O /\ v = a)\}\ ).
  { exists \{\ λ n v, ( n = O /\ v = a)\}\. auto. }
  destruct H1 as [ξ]. pose proof (H2 ξ). clear H2.
  destruct H8 as [H8 H9].
  red. split.
  - red. intros. rewrite H9 in H2.
  applyAxiomII H2. rewrite H2. 
  apply Rge_le. apply (Lemma9_6_1 f _ _ a b); auto.
  - intros s H2.
    assert (∃ε : R, ε = ST - s /\ε > 0). 
    { exists (ST - s). split; lra. }
    destruct H10 as [ε[H12 H13]]. 
    clear H1 H8 H9.
    assert (∀i : nat,(i <= n)%nat ->∃x : Seq,  f[x[i]] > M[i] - ε / (b -a)).
    { intros. apply H7 in H1 as H7'. destruct H7' as [H7' H11].
      red in H7'. unfold sup in H7'. destruct H7' as [H14 H15].
      assert (M [i] - ε / (b - a) < M[i]).
      { assert  ((ε / (b - a)) > 0).
      { apply Rdiv_lt_0_compat. auto. 
        apply a_b' in H. lra. }
        lra. }
      apply H15 in H8. destruct H8 as [u [H8 H9]]. 
      applyAxiomII H8. destruct H8 as [x[H8 H10]]. 
      exists \{\λ i v, v = x \}\. rewrite FunValueR. 
      rewrite <- H8. auto. }
    assert (∃ξ : Seq, ξ = \{\ λ n v,∃ x:Seq, f[x[n]] > M [n] - ε / (b - a) /\ v = x[n] \}\ ). 
    { exists(\{\ λ n v,∃ x:Seq, f[x[n]] > M [n] - ε / (b - a) /\ v = x[n] \}\).
      auto. }
    destruct H8 as [ξ'].
    red in H0'. destruct H0' as [_ H0'].
    pose proof (H0' ξ'). destruct H9. 
    assert (∀i : nat,(i <= n)%nat -> f[ξ'[i]] > M [i] - ε / (b - a)). 
    { intros. apply H1 in H11. destruct H11 as [x]. 
      assert (ξ' [i] = x[i]). rewrite H8. 
      apply f_x. rewrite <- H8. 
      red in H9. destruct H9 as [[H9 H9'] H10']. 
      auto. apply AxiomII'. exists x. split; auto.
      rewrite H14. auto. } 
    exists (Σ \{\ λ i m, m =f [ξ' [i]] * (T [S i] - T [i])\}\ n).
    split.
    + rewrite H10. apply AxiomII. auto.
    + assert  (∀i : nat,(i <= n)%nat ->  
      f [ξ' [i]] * (T [S i] - T [i]) > 
      (M [i] - ε / (b - a)) * (T [S i] - T [i])).
      { intros. 
        apply H11 in H14.
        red in H. destruct H as [_[_[H[_ _]]]]. 
        pose proof (H  i). 
        apply Rmult_gt_compat_r. lra. auto. }
      assert  (Σ \{\ λ i m, 
              m = f[ξ' [i]] * (T [S i] - T [i])\}\ n >
              Σ \{\ λ i m,  m = 
              (M [i] - ε / (b - a)) * (T [S i] - T [i])\}\ n ).
      { apply Lemma9_1'. intros. repeat rewrite FunValueR. 
        apply H14 in H15. auto. } 
      assert  (Σ \{\ λ i m,  m = 
              (M [i] - ε / (b - a)) * (T [S i] - T [i])\}\ n
              = Σ \{\ λ i m,  m = (M [i])*(T [S i] - T [i])\}\ n
                - ( ε / (b - a)) *
                Σ \{\ λ i m,  m = (T [S i] - T [i])\}\ n).
      { assert  ( \{\ λ i m, m = (M [i] - ε / (b - a)) * 
                     (T [S i] - T [i]) \}\  =
                 \{\ λ i m, m = (M [i]) * (T [S i] - T [i]) 
                - ε / (b - a) * (T [S i] - T [i]) \}\ ).
        { apply AxiomI. split; intros.
          - applyAxiomII H16. destruct H16 as [x[y[H16 H17]]].
            apply AxiomII. exists x, y. split; auto.
            rewrite H17. lra.
          - applyAxiomII H16. destruct H16 as [x[y[H16 H17]]].
            apply AxiomII. exists x, y. split; auto.
            rewrite H17. lra. }
        rewrite H16. 
        rewrite Lemma9_6_1_1. auto. }
      assert  (Σ \{\ λ i m, m = T [S i] - T [i] \}\ n = b - a).
      { apply Lemma9_6_1_2. auto. }
      rewrite H17 in H16. clear H17. 
      pose proof (H7 n).
      assert  ((n <= n)%nat). left. apply H17 in H18.
      destruct H18. rewrite <- H19 in H16.
      assert  (ST - ε / (b - a) * (b - a) = ST - ε).
      unfold Rdiv. rewrite Rmult_assoc.
      rewrite (Rinv_l (b - a)). lra. apply a_b' in H. lra.
      rewrite H20 in H16.
      assert  (s = ST - ε). lra.
      rewrite <- H21 in H16. rewrite <- H16. auto.
Qed.
  
  (* 下和是全体积分和的最小下界 *)
Fact Fact9_6_1' : ∀ (f : Fun)(T : Seq) (St a b :R) (n : nat)(Sum : sR),
Low_sum f T a b St n -> All_integralsum f T a b n Sum -> inf Sum St.
Proof.
Admitted. 


  
(* T'是T增加p个分割点后的分割, 就是说T'和T都是[a,b]上分割,
   T分割n份, T'分割n+p份, 并且T是T'的子列 *)
Definition sum_seg1 (T T':Seq) (a b :R) (n p : nat) := seg T a b (S n)
  /\ seg T' a b ((S n) + p)%nat /\ SubSeq T' T.


(* 增加一个分割点k *)
Lemma Fact9_6_2'_Lemma1 : ∀ (f : Fun) (T T': Seq) (a b :R) (n : nat),
  sum_seg1 T T' a b n 1%nat -> (∃ k : nat, (0 <= k < (S n))%nat
    /\ (∀ x, x <= k -> T[x] = T'[x])%nat
    /\ (∀ x, k < x <= (S n) -> T[x] = T'[S x])%nat
    /\ T[S k] - T[k] = T'[S (S k)] - T'[k]).
Proof.
  intros. generalize dependent b. generalize dependent a.
  generalize dependent T. generalize dependent T'.
  generalize dependent f. induction n.
  - intros. destruct H as [H[]]. exists 0%nat.
    split. lia. destruct H as [_[_[_[]]]]. 
    destruct H0 as [_[_[_[]]]].
    assert ((1 + 1)%nat = 2%nat). lia.
    rewrite H4 in H3.
    repeat split; intros. 
    assert  (x = 0)%nat. lia. rewrite H6. lra.
    assert (x = 1)%nat. lia.
    rewrite H6; lra. lra. 
  - intros. destruct H as [H[]]. destruct H1 as [H1[H2[h[H3[]]]]].
    set (A := \{ λ u, h\[u\] = u /\ (u <= S (S n))%nat \}).
    assert  (∃ Aa, maxN A Aa) as [Aa[]].
    { assert (h \[ 0%nat \] = 0%nat).
    { red in H. destruct H as [_[_ [_ [H _]]]].
      assert  (T[0] = T'[h\[0\]])%nat; auto.
      rewrite H in H6. red in H0. 
      destruct (gt_0_eq (h \[ 0%nat \])).
      destruct H0 as [_[_ [H0 []]]].
        assert  (∀m, T' [O] < T' [S m]).
        { induction m. pose proof (H0 O). auto.
          pose proof (H0 (S m)). lra. }
        pose proof(H10 ((h \[ 0%nat \])-1))%nat.
        assert (S (h \[ 0%nat \] - 1) = h \[ 0%nat \]).
        lia. rewrite H12 in H11; lra. auto. }
      assert  (0%nat ∈ A). (* A非空 *)
      { apply AxiomII. split; auto. lia. }
      assert  (∃ a, (∀ x, x ∈ A -> x <= a)%nat).
      { exists (S (S n)). intros.
        apply AxiomII in H8 as []. auto. }
      apply finite_maxN.  destruct H8 as [a'].
      pose proof (NatFinite a'). 
      assert (Finite \{ λ u,(u <= a')%nat \}).
      { red. left; auto. } 
      assert (A ⊂ \{ λ u : nat,(u <= a')%nat \}).
      {  red. intros. apply AxiomII.
         apply H8; auto. } 
      pose proof (SubSetFinite_N H10 H11). 
      destruct H12 as [H12|H12]. auto.
      rewrite H12 in H7. applyAxiomII H7.
      destruct H7. auto. }  
    assert  (∀ x, x <= h\[x\])%nat.
    { intros. induction x. lia.
      assert  (h\[x\] < h\[S x\])%nat.
      { destruct H3. apply (H8 x _ (S x)); auto.
      apply x_fx_N; auto; rewrite H4; 
      apply AxiomII;auto. apply x_fx_N; auto; rewrite H4; 
      apply AxiomII;auto. }
      assert  (S (h\[x\]) <= h\[S x\])%nat. lia. 
      assert  ((S x) <= S (h\[x\]))%nat. lia. lia. }
    assert  (∀ x, x < h\[x\] -> (∀ y, x < y -> y < h\[y\]))%nat.
    { intros. induction y.  lia. assert  (x <= y)%nat. lia. 
      destruct (classic (x = y)). rewrite <-H12.
      assert  (S x <= h\[x\])%nat. lia.  
      assert  (h\[x\] < h\[S x\])%nat.
      { destruct H3. apply (H14 x _ (S x)); auto.
        apply x_fx_N; auto; rewrite H4; 
       apply AxiomII;auto. 
       apply x_fx_N; auto; rewrite H4; 
       apply AxiomII;auto. } lia.
      assert  (x < y)%nat. lia. 
      apply IHy in H13. assert  (S y <= h\[y\])%nat. lia. 
      assert  (h\[y\] < h\[S y\])%nat. destruct H3 as [H3 H3'].
      apply (H3' y _ (S y)); auto. apply x_fx_N; auto; rewrite H4; 
      apply AxiomII;auto. apply x_fx_N; auto; rewrite H4; 
      apply AxiomII;auto. lia. }
    (* 下面讨论T'增加的那个分割点加到T的哪个区间了 *)
    (* Aa是加入的点的前一个点, 如果Aa = S n, 加入的点就在最后一个区间里,
       即[S n, S S n]里 *)
    destruct (classic (Aa = S n)).
    + (* 加入的点在最后一个区间里 *) exists Aa.
      assert  (0 <= Aa < (S (S n)))%nat. lia. 
      assert  (∀ x,(x <= Aa)%nat -> T[x] = T'[x]).
      { intros. rewrite H5. pose proof H8 x.
        destruct (classic (h\[x\] = x)). rewrite H14; auto.
        assert  (x < h\[x\])%nat. lia.
        assert  (Aa < h\[Aa\])%nat.
        { apply le_lt_or_eq in H12. destruct H12.
        apply (H9 x); auto. rewrite <- H12; auto. }
        applyAxiomII H6. destruct H6. rewrite H6 in H16. lia. }
      assert  (∀ x, (Aa < x <= S (S n))%nat -> T[x] = T'[S x])%nat.
      { intros. destruct H as [_[_[_[]]]]. destruct H0 as [_[_[_[]]]].
        assert  (x = S (S n)). lia. simpl in H15.
        rewrite plus_comm in H15. simpl in H15.
        rewrite H16,H14,H15; auto. }
      split; auto. repeat split; auto. rewrite H13,H12; auto.
      rewrite H10; auto.
    + assert  (Aa <> S (S n)).
      { intro. pose proof(Increase_seg T' a b _ H0) as H12'.
      pose proof H0 as H0'.
      destruct H as [_[_[_[]]]]. destruct H0 as [_[_[H0''[]]]].
        rewrite <-H11 in H12,H13. rewrite H5,<-H13 in H12.
        assert  (h\[Aa\] = Aa + 1)%nat. 
        { rewrite H13 in H12. rewrite <- H13 in H12.
          apply (equal_seg T' a b _ H0') in H12; auto. } 
        applyAxiomII H6. destruct H6. rewrite H6 in H14. lia. }
      (* 加入的点在之前的区间里, 构造之前区间的分割以应用归纳假设 *)
      assert  (sum_seg1 T T' a b (S n) 1).
      { split; auto. split; auto. split; auto. split; eauto. }
      assert  (seg T a T[S n] (S n)).
      { split. lia. split; auto. destruct H as [_[_[H[]]]]; auto. }
      assert  (T[S n] = T'[(S n) + 1])%nat.
      { pose proof H0 as H0'.
       destruct H0 as [H0[H14[H15[]]]].
       destruct H as [H[H18[H19[]]]].
        rewrite H5,<-H17 in H21.
        assert  (h\[S (S n)\] = (S (S n) + 1))%nat.
        { apply (equal_seg T' a b _ H0') in H21; auto. }  
        assert  (h\[S n\] < h\[S (S n)\])%nat. 
        { destruct H3 as []. apply (H23 (S n) _ (S (S n))); auto.
          apply x_fx_N; auto; rewrite H4; 
          apply AxiomII;auto. apply x_fx_N; auto; rewrite H4; 
          apply AxiomII;auto. }
        rewrite H22 in H23.
        assert  (h\[S n\] <= S (S n))%nat. lia. 
        destruct (classic (h\[S n\] = S (S n))%nat).
        rewrite H5,H25. simpl. cut(S (S n) = S (n + 1)).
        intros. rewrite H26; auto. lia. 
        assert  (h\[S n\] < S (S n))%nat. lia. 
        assert  (h\[S n\] <= (S n))%nat. lia. 
        pose proof H8 (S n). assert  (h\[S n\] = (S n))%nat. lia. 
        assert  ((S n) ∈ A). apply AxiomII; split; auto. 
        apply H7 in H30. applyAxiomII H6. destruct H6.
        assert  (Aa < S n)%nat; lia. }
      assert  (seg T' a T[S n] ((S n) + 1)%nat).
      { split. lia. split; auto. destruct H0 as [_[_[H0[]]]]; auto. }
      assert  (sum_seg1 T T' a T[S n] n 1).
      { split; auto. split; auto. split; auto. split; eauto. }
      apply IHn in H16 as [k[H16[H17[]]]]; auto. exists k.
      split. lia. split; auto. split; auto. intros. destruct H20.
      destruct H as [_[_[_[_]]]]. destruct H0 as [_[_[_[_]]]].
      destruct (classic (x = S (S n))). rewrite H22.
      rewrite H. cut(S (S (S n)) = (S (S n) + 1)%nat);intros;[|lia].
      rewrite H23. auto.
      apply H18. split; auto. lia. 
Qed.


Lemma Fact9_6_2'_Lemma2 : ∀ (A B : Seq) (k n : nat), (0 <= k <= n)%nat
  -> (∀ x, x < k -> A[x] = B[x])%nat
  -> (∀ x, k < x <= n -> A[x] = B[x])%nat
  -> Σ A n - Σ B n = A[k] - B[k].
Proof.
(*   intros. induction k.
  - simpl. induction n. simpl; lra.
    simpl. *) 
Admitted.

(* 函数值域的确界唯一 *) 
Lemma Lemma6_2:∀(f : Fun)(D :sR)(M M1 : R),sup_f D f M -> sup_f D f M1 
-> M = M1.
Proof. 
  intros. unfold sup_f in *. destruct H, H0. 
  red in H, H0. destruct (classic (M = M1)); auto. 
  apply Rdichotomy in H3 as [H3|H3].
  apply H2 in H3 as H3'. destruct H3' as [x0[H4 H5]].
  apply H in H4. lra.
  apply H1 in H3 as H3'. destruct H3' as [x0[H4 H5]].
  apply H0 in H4. lra.
Qed.  



Lemma subsup_inf :forall (f : Fun)(a b c d m M:R),\[c, d \] ⊂ \[ a, b \]
-> inf_f (\[ a, b \]) f m -> sup_f (\[c, d \]) f M -> m <= M.
Proof. 
Admitted.

Lemma sup_inf :forall (f : Fun)(a b m M:R),
inf_f (\[ a, b \]) f m -> sup_f (\[a, b \]) f M -> m <= M.
Proof. 
Admitted.
 
Lemma sup_subsup :forall (f : Fun)(a b c d m M:R),\[c, d \] ⊂ \[ a, b \]
-> sup_f (\[ a, b \]) f M -> sup_f (\[c, d \]) f m -> m <= M.
Proof. 
Admitted.

Lemma exists_sup:forall (f : Fun)(a b c d M:R),\[c, d \] ⊂ \[ a, b \]
-> sup_f (\[ a, b \]) f M -> ∃m, sup_f (\[c, d \]) f m.
Proof.
Admitted.




Fact Fact9_6_2_1:∀(T T': Seq) (n k: nat)(M2 : Seq), 
(0 <= k < S n)%nat ->
Σ \{\ λ i s, s = M2 [i] * (T' [S i] - T' [i]) \}\ (S n) = 
Σ \{\ λ(i : nat)(s : R), (0 <= i < k)%nat /\ s = 
M2 [i] * (T' [S i] - T' [i]) \/ 
i = k /\ s = M2 [k] * (T' [S k] - T' [k]) + M2 [S k] * 
(T' [S (S k)] - T' [S k]) \/ 
(k < i)%nat /\ s = M2 [S i] * (T' [S (S i)] - T' [S i]) \}\ n.
Proof. 
  intros T T' n k M2 L. 
  induction n. 
  - simpl.   
    assert  (\{\ λ i s, 
     s = M2 [i] * (T' [S i] - T' [i]) \}\ [0%nat] = 
     M2 [0%nat] * (T' [1%nat] - T' [0%nat])). 
     { apply FunValue. } rewrite H. clear H.
     assert  (\{\ λ i s, 
     s = M2 [i] * (T' [S i] - T' [i]) \}\ [1%nat] =
     M2 [1%nat] * (T' [2%nat] - T' [1%nat])).
     { apply FunValue. } rewrite H. clear H.  
     assert  (\{\ λ i s,
     (0 <= i < k)%nat /\ s = M2 [i] * (T' [S i] - T' [i]) \/
     i = k /\ s = M2 [k] * (T' [S k] - T' [k]) +
     M2 [S k] * (T' [S (S k)] - T' [S k]) \/(k < i)%nat
     /\ s = M2 [S i] * (T' [S (S i)] - T' [S i]) \}\[0%nat] =
     M2 [0%nat] * (T' [1%nat] - T' [0%nat]) +
     M2 [1%nat] * (T' [2%nat] - T' [1%nat])). 
     apply f_x. red. intros. applyAxiomII H.
     applyAxiomII H0. destruct H as [x'[y'[H H']]].
     destruct H0 as [x''[y''[H0 H0']]].
     apply ProdEqual in H. apply ProdEqual in H0.
     destruct H. destruct H0. rewrite H1, H2. 
     destruct H', H0'; destruct H3, H4;
     subst y'; subst y''. subst y. subst z.
     subst x'; subst x''; auto.
     destruct H4. subst y; subst z. subst k.
     subst x'; subst x''. destruct H3.
     apply Nat.lt_irrefl in H0. lra.
     destruct H4. rewrite H2. rewrite H5. 
     subst x'. subst x''.
     destruct H3. lia. 
     destruct H3. rewrite <- H0 in H4. rewrite H in H4.
     rewrite H1 in H4. destruct H4. 
     apply Nat.lt_irrefl in H4. lra.
     destruct H3. rewrite <- H0 in H4. rewrite <- H in H1.
     destruct H4. lia.
     destruct H3,H4. rewrite H2,H4. auto.
     destruct H3,H4. rewrite <- H0 in H3. rewrite H in H3.
     rewrite H1 in H3. apply Nat.lt_irrefl in H3. lra.
     destruct H3,H4. rewrite <- H in H1. rewrite H0 in H1.
     rewrite H3 in H1. apply Nat.lt_irrefl in H1. lra.
     destruct H3,H4. rewrite H2,H4. rewrite <- H,H0. auto. 
     apply AxiomII. exists 0%nat. 
     exists (M2 [0%nat] * (T' [1%nat] - T' [0%nat]) +
     M2 [1%nat] * (T' [2%nat] - T' [1%nat])). split. auto.
     right. left. assert  (k = 0%nat). lia. split.
     auto. rewrite H. auto. 
     rewrite H. clear H. auto. 
  - simpl. destruct L as [L L0]. apply lt_n_Sm_le in L0.
    apply le_lt_or_eq in L0. destruct L0 as [L0|L0'].  
    + rewrite <- IHn. simpl. 
      assert  (\{\ λ i s, 
      s = M2 [i] * (T' [S i] - T' [i]) \}\ [S (S n)]
      = \{\ λ i s, (0 <= i < k)%nat /\ 
      s = M2 [i] * (T' [S i] - T' [i]) \/
      i = k /\ s = M2 [k] * (T' [S k] - T' [k]) +
      M2 [S k] * (T' [S (S k)] - T' [S k]) \/
      (k < i)%nat /\ 
      s = M2 [S i] * (T' [S (S i)] - T' [S i]) \}\[S n]).
      { assert  (\{\ λ i s, 
        s = M2 [i] * (T' [S i] - T' [i]) \}\ [S (S n)] = 
        M2 [S (S n)] * (T' [S (S (S n))] - T' [S (S n)])).
        { apply FunValue. }
        rewrite H. clear H.
        apply eq_sym. apply f_x. red. intros. applyAxiomII H.
        applyAxiomII H0. destruct H as [x'[y'[H H']]].
        destruct H0 as [x''[y''[H0 H0']]].
        apply ProdEqual in H. apply ProdEqual in H0.
        destruct H. destruct H0. destruct H',H0';
        destruct H3,H4. subst y. subst z. rewrite H5,H6.
        rewrite <- H,H0. auto. destruct H4.
        rewrite <- H4 in H3. rewrite <- H0 in H3.
        rewrite <- H in H3. destruct H3.  
        apply Nat.lt_irrefl in H7. lra.
        destruct H4. rewrite <- H0 in H4. rewrite <- H in H3.
        destruct H3. lia. 
        destruct H3. rewrite <- H0 in H4. rewrite <- H3 in H4.
        rewrite <- H in H4. destruct H4.
        apply Nat.lt_irrefl in H7. lra.
        destruct H3. rewrite <- H0 in H4. rewrite H in H4.
        destruct H4. lia.
        destruct H3, H4. rewrite H1,H2. rewrite H5,H6. auto.
        destruct H3, H4. rewrite <- H0 in H4. rewrite H in H4.
        rewrite <- H3 in H4. apply Nat.lt_irrefl in H4. lra.
        destruct H3,H4. rewrite <- H in H3. rewrite H0 in H3.
        rewrite H4 in H3. apply Nat.lt_irrefl in H3. lra.
        destruct H3,H4. rewrite H1,H2. rewrite H5,H6.
        rewrite <- H,H0. auto.
        apply AxiomII. exists (S n),
        (M2 [S (S n)] * (T' [S (S (S n))] - T' [S (S n)])).
        split. auto. right. right. auto. }
      rewrite H. auto. auto. 
    + assert  (\{\ λ i s, 
        s = M2 [i] * (T' [S i] - T' [i]) \}\ [S n] = 
        (M2 [(S n)] * (T' [S (S n)] - T' [(S n)]))).
      { apply FunValue. }
      rewrite H. clear H. 
      assert  (\{\ λ i s, 
        s = M2 [i] * (T' [S i] - T' [i]) \}\ [S (S n)] =
        (M2 [(S (S n))] * (T' [S (S (S n))] - T' [(S (S n))]))).
      { apply FunValue. }
      rewrite H. clear H.
      assert  (\{\ λ i s, 
        (0 <= i < k)%nat /\ s = M2 [i] * (T' [S i] - T' [i]) 
        \/ i = k /\ s = M2 [k] * (T' [S k] - T' [k]) +
        M2 [S k] * (T' [S (S k)] - T' [S k]) \/ (k < i)%nat 
        /\ s = M2 [S i] * (T' [S (S i)] - T' [S i]) \}\[S n] =
        M2 [(S n)] * (T' [S (S n)] - T' [(S n)]) +
        M2 [S (S n)] * (T' [S (S (S n))] - T' [S (S n)])).
      { apply f_x. red. intros. applyAxiomII H.
        applyAxiomII H0. destruct H as [x'[y'[H H']]].
        destruct H0 as [x''[y''[H0 H0']]].
        apply ProdEqual in H. apply ProdEqual in H0.
        destruct H. destruct H0. destruct H',H0';
        destruct H3,H4. subst y. subst z. rewrite H5,H6.
        rewrite <- H,H0. auto. destruct H4.
        rewrite <- H4 in H3. rewrite <- H0 in H3.
        rewrite <- H in H3. destruct H3.  
        apply Nat.lt_irrefl in H7. lra.
        destruct H4. rewrite <- H0 in H4. rewrite <- H in H3.
        destruct H3. lia. 
        destruct H3. rewrite <- H0 in H4. rewrite <- H3 in H4.
        rewrite <- H in H4. destruct H4.
        apply Nat.lt_irrefl in H7. lra.
        destruct H3. rewrite <- H0 in H4. rewrite H in H4.
        destruct H4. lia.
        destruct H3, H4. rewrite H1,H2. rewrite H5,H6. auto.
        destruct H3, H4. rewrite <- H0 in H4. rewrite H in H4.
        rewrite <- H3 in H4. apply Nat.lt_irrefl in H4. lra.
        destruct H3,H4. rewrite <- H in H3. rewrite H0 in H3.
        rewrite H4 in H3. apply Nat.lt_irrefl in H3. lra.
        destruct H3,H4. rewrite H1,H2. rewrite H5,H6.
        rewrite <- H,H0. auto. 
        apply AxiomII. exists (S n),
        (M2 [(S n)] * (T' [S (S n)] - T' [(S n)]) +
        M2 [S (S n)] * (T' [S (S (S n))] - T' [S (S n)])).
        split. auto. right. left. split. auto.
        rewrite L0'. auto. }
      rewrite H. 
      assert  (Σ \{\ λ i s, 
        s = M2 [i] * (T' [S i] - T' [i]) \}\ n =
        Σ \{\ λ i s, (0 <= i < k)%nat /\ 
        s = M2 [i] * (T' [S i] - T' [i]) \/ i = k /\
        s = M2 [k] * (T' [S k] - T' [k]) + M2 [S k] * 
        (T' [S (S k)] - T' [S k]) \/ (k < i)%nat /\ 
        s = M2 [S i] * (T' [S (S i)] - T' [S i]) \}\ n).
      { apply Lemma9_1''. intros. subst k. 
        assert  (\{\ λ i s, 
          s = M2 [i] * (T' [S i] - T' [i]) \}\ [x] =
          (M2 [x] * (T' [S x] - T' [x]))). 
        apply FunValue. rewrite H1. clear H1.
        apply eq_sym. apply f_x. 
        red. intros. applyAxiomII H1.
        applyAxiomII H2. destruct H1 as [x'[y'[H1 H1']]].
        destruct H2 as [x''[y''[H2 H2']]].
        apply ProdEqual in H1. apply ProdEqual in H2.
        destruct H1. destruct H2. destruct H1',H2'; 
        destruct H5,H6. subst y. subst z. rewrite H7,H8.
        rewrite <- H1,H2. auto. destruct H6.
        rewrite <- H1 in H5. rewrite H2 in H5.
        rewrite H6 in H5. destruct H5.
        apply Nat.lt_irrefl in H9. lra.
        destruct H6. rewrite <- H2 in H6. rewrite <- H1 in H5.
        destruct H5. lia. 
        destruct H5. rewrite <- H2 in H6. rewrite <- H5 in H6.
        rewrite <- H1 in H6. destruct H6.
        apply Nat.lt_irrefl in H9. lra.
        destruct H5. rewrite <- H2 in H6. rewrite <- H1 in H5.
        destruct H6. lia.
        destruct H5, H6. rewrite H3,H4. rewrite H7,H8. auto.
        destruct H5, H6. rewrite <- H2 in H6. rewrite H1 in H6.
        rewrite H5 in H6. apply Nat.lt_irrefl in H6. lra. 
        destruct H5,H6. rewrite <- H1 in H5. rewrite H2 in H5.
        rewrite H6 in H5. apply Nat.lt_irrefl in H5. lra.
        destruct H5,H6. rewrite H3,H4. rewrite H7,H8.
        rewrite <- H1,H2. auto. 
        apply AxiomII. exists x,
        (M2 [x] * (T' [S x] - T' [x])).
        split. auto. left. split. lia. auto. }
      rewrite H0. lra.
Qed.


Lemma hanshu:∀ (T' M2: Seq)(k : nat)(ST ST1 M m: R), 
  \{\ λ i s, 
  (0 <= i < k)%nat /\ s = M2 [i] * (T' [S i] - T' [i]) \/
  i = k /\ s = M2 [k] * (T' [S k] - T' [k]) +
  M2 [S k] * (T' [S (S k)] - T' [S k]) \/ (k < i)%nat 
  /\ s = M2 [S i] * (T' [S (S i)] - T' [S i]) \}\[k] = 
  M2 [k] * (T' [S k] - T' [k]) + M2 [S k] * (T' [S (S k)] 
  - T' [S k]).
Proof.
  intros.
  apply f_x. red. intros. 
  applyAxiomII H. applyAxiomII H0.
  destruct H as [x'[y'[H H']]]. 
  destruct H0 as [x''[y''[H0 H0']]].
  apply ProdEqual in H. apply ProdEqual in H0.
  destruct H. destruct H0. rewrite H1, H2. 
  destruct H', H0'; destruct H3, H4;
  subst y'; subst y''. subst y. subst z.
  subst x'; subst x''; auto.
  destruct H4. subst y; subst z. subst k.
  subst x'; subst x''. destruct H3.
  apply Nat.lt_irrefl in H0. lra.
  destruct H4. rewrite H2. rewrite H5. 
  subst x'. subst x''.
  destruct H3. lia.
  destruct H3. rewrite <- H0 in H4. rewrite H in H4.
  rewrite H1 in H4. destruct H4. 
  apply Nat.lt_irrefl in H4. lra.
  destruct H3. rewrite <- H0 in H4. rewrite <- H in H1.
  destruct H4. lia.
  destruct H3,H4. rewrite H2,H4. auto.
  destruct H3,H4. rewrite <- H0 in H3. rewrite H in H3.
  rewrite H1 in H3. apply Nat.lt_irrefl in H3. lra.
  destruct H3,H4. rewrite <- H in H1. rewrite H0 in H1.
  rewrite H3 in H1. apply Nat.lt_irrefl in H1. lra.
  destruct H3,H4. rewrite H2,H4. rewrite <- H,H0. auto. 
  apply AxiomII. exists k.  
  exists (M2 [k] * (T' [S k] - T' [k]) +
          M2 [S k] * (T' [S (S k)] - T' [S k])). split. auto. 
  right. left. auto. 
Qed.

Lemma function:∀ (T' M2: Seq)(k : nat)(ST ST1 M m: R), 
Function \{\ λ i s,
  (0 <= i < k)%nat /\ s = M2 [i] * (T' [S i] - T' [i]) \/
  i = k /\ s = M2 [k] * (T' [S k] - T' [k]) +
  M2 [S k] * (T' [S (S k)] - T' [S k]) \/
  (k < i)%nat /\ s = M2 [S i] * (T' [S (S i)] - T' [S i]) \}\.
Proof.
  intros. red. intros. 
  applyAxiomII H. applyAxiomII H0.
  destruct H as [x'[y'[H H']]]. 
  destruct H0 as [x''[y''[H0 H0']]].
  apply ProdEqual in H. apply ProdEqual in H0.
  destruct H. destruct H0. rewrite H1, H2. 
  destruct H', H0'; destruct H3, H4;
  subst y'; subst y''. subst y. subst z.
  subst x'; subst x''; auto.
  destruct H4. subst y; subst z. subst k.
  subst x'; subst x''. destruct H3.
  apply Nat.lt_irrefl in H0. lra.
  destruct H4. rewrite H2. rewrite H5. 
  subst x'. subst x''.
  destruct H3. lia.
  destruct H3. rewrite <- H0 in H4. rewrite H in H4.
  rewrite H1 in H4. destruct H4. 
  apply Nat.lt_irrefl in H4. lra.
  destruct H3. rewrite <- H0 in H4. rewrite <- H in H1.
  destruct H4. lia.
  destruct H3,H4. rewrite H2,H4. auto.
  destruct H3,H4. rewrite <- H0 in H3. rewrite H in H3.
  rewrite H1 in H3. apply Nat.lt_irrefl in H3. lra.
  destruct H3,H4. rewrite <- H in H1. rewrite H0 in H1.
  rewrite H3 in H1. apply Nat.lt_irrefl in H1. lra.
  destruct H3,H4. rewrite H2,H4. rewrite <- H,H0. auto.
Qed.




(* 性质2' 对分割T增加一个分割点得到T' *)
Fact Fact9_6_2':∀ (f : Fun)(T T': Seq) (a b :R) (n : nat)(ST ST1 M m: R),
Up_sum f T a b ST n -> Up_sum f T' a b ST1 (S n)
  -> sum_seg1 T T' a b n 1%nat -> sup_f (\[a,b\]) f M
    /\ inf_f (\[a,b\]) f m -> 0 <= ST - ST1 <= (M - m) *(mold T (S n)).
Proof.
  intros. destruct H as [H[M1]]. destruct H0 as [H0[M2]].
  pose proof H1 as H1a. destruct H1 as [_[_]].
  assert  (∃ k : nat, (0 <= k < (S n))%nat
    /\ T[k] = T'[k] /\ T[S k] = T'[S (S k)]
    /\ T[S k] - T[k] = T'[S (S k)] - T'[k]
    /\ ST - ST1 = M1[k] * (T[S k] - T[k])
      - (M2[k] * (T'[S k] - T'[k]) + M2[S k] * (T'[S (S k)] - T'[S k]))).
  { pose proof H1a.  
    apply Fact9_6_2'_Lemma1 in H5 as [k[H5[H6[]]]]; auto.
    exists k. split; auto. split. rewrite H6; auto. split.
    rewrite H7; auto. lia. split; auto.
    assert  (ST = Σ \{\ λ (i : nat)(s : R),
      s = M1[i] * (T[S i] - T[i]) \}\ n).
    { apply (H3 0%nat). lia. }
    assert  (ST1 = Σ \{\ λ (i : nat)(s : R),
      s = M2[i] * (T'[S i] - T'[i]) \}\ (S n)).
    { apply (H4 0%nat). lia. }
    set (A := \{\ λ (i : nat)(s : R), s = M1[i] * (T[S i] - T[i]) \}\).
    set (A1 := \{\ λ (i : nat)(s : R),
      ((0 <= i < k)%nat /\ s = M2[i] * (T'[S i] - T'[i]))
      \/ (i = k /\ s = M2[k] * (T'[S k] - T'[k])
        + M2[S k] * (T'[S (S k)] - T'[S k]))
      \/ ((k < i)%nat /\ s = M2[S i] * (T'[S (S i)] - T'[S i])) \}\).
    assert  (ST1 = Σ A1 n).
    { (* 该断言旨在改变ST1的求和上限为n, 使之与ST一致,
         可能需要用到分部求和证明 A_000 *)  
     rewrite H10. subst A1. apply Fact9_6_2_1. auto. auto. }
    assert  (A[k] = M1[k] * (T[S k] - T[k])). 
    subst A. rewrite FunValueR; auto. 
    assert  (A1[k] = M2[k] * (T'[S k] - T'[k])
      + M2[S k] * (T'[S (S k)] - T'[S k])). 
      { subst A1. apply hanshu; auto. }
    assert  (ST = Σ A n); auto. rewrite <-H12,<-H13,H11,H14.
    (* Lemmasum_minus不好用在这里, 这里n之后的项无法确保相等,
       可以用Fact9_6_2'_Lemma2 *) 
    apply Fact9_6_2'_Lemma2. lia. intros.
    subst A. rewrite FunValueR. symmetry.
    subst A1. apply f_x. apply function; auto.
    apply AxiomII'. left. split. lia.
    repeat rewrite H6; [ |lia|lia].
    assert (∀i : nat,(i < k)%nat -> M1 [i] = M2 [i]).
    { intros. cut((i <= n)%nat); intros;[|lia].
      pose proof (H3 i H17). 
      cut((i <= S n)%nat); intros;[|lia].
      pose proof (H4 i H19). destruct H18 as [H18 _].
      destruct H20 as [H20 _]. 
      rewrite <- H6 in H20.  rewrite <- H6 in H20.
      apply (Lemma6_2 f (\[ T [i], T [S i] \])); auto.
      lia. lia. }
     rewrite H16;[auto| lia]. intros.
     subst A. rewrite FunValueR. symmetry.
     subst A1. apply f_x. apply function; auto. apply AxiomII'.
     right; right. split. lia.
     repeat rewrite H7; [|lia|lia].
     assert (∀i : nat,(k < i <= n)%nat -> M1 [i] =M2 [S i]). 
     { intros. cut((i <= n)%nat); intros;[|lia].
      pose proof (H3 i H17).
      cut((S i <= S n)%nat); intros;[|lia].
      pose proof (H4 (S i) H19). destruct H18 as [H18 _].
      destruct H20 as [H20 _]. 
      rewrite <- H7 in H20.  rewrite <- H7 in H20.
      apply (Lemma6_2 f (\[ T [i], T [S i] \])); auto.
      lia. lia.  }  rewrite H16; auto. }
  destruct H5 as [k[H5[H6[H7[]]]]].
  assert  (T'[S (S k)] - T'[k]
    = (T'[S k] - T'[k]) + (T'[S (S k)] - T'[S k])).
  { lra. }
  rewrite H8,H10 in H9.
  assert  (ST - ST1 = (M1[k] - M2[k]) * (T'[S k] - T'[k])
    + (M1[k] - M2[S k]) * (T'[S (S k)] - T'[S k])).
  { lra. (* H9的等式变形过来 *) }
  assert  (m <= M2[k] /\ m <= M2[S k]) as [].
  { assert  (k <= S n)%nat. { lia. (* 用H5 *) }
    apply H4 in H12 as [H12 _].
    assert  (S k <= S n)%nat. { lia. (* 用H5 *) }
    apply H4 in H13 as [H13 _]. destruct H2. split. 
    apply (subsup_inf f a b T'[k] T'[S k]); auto.
    apply (a_b_c T' _ _ (S n) ); auto. lia.
    apply (subsup_inf f a b T'[S k] T'[S(S k)]); auto.
     apply (a_b_c T' _ _ (S n) ); auto. lia.
    (* 用H12和H13, m是函数f的下确界, 应该小于等于任何一个小区间的下确界 *) }
  assert  (M2[k] <= M1[k] /\ M2[S k] <= M1[k]) as [].
  { assert  (k <= n)%nat. { lia. (* 用H5 *) }
    apply H3 in H14 as [H14 _].
    assert  (k <= S n)%nat. { lia. (* 用H5 *) }
    apply H4 in H15 as [H15 _].
    assert  (S k <= S n)%nat. { lia. (* 用H5 *) }
    apply H4 in H16 as [H16 _].
    rewrite <-H6 in H15. rewrite <-H7 in H16. 
    split. apply (sup_subsup f T[k] T[S k] T[k] T'[S k]); auto.
    intros z H17. applyAxiomII H17. apply AxiomII.
    split. lra. red in H0. destruct H0 as [_[_ [H0 _]]].
    pose proof (H0 (S k)). lra.
    apply (sup_subsup f T[k] T[S k] T'[S k] T[S k]); auto.
    intros z H17. applyAxiomII H17. apply AxiomII.
    split. red in H0. destruct H0 as [_[_ [H0 _]]].
    pose proof (H0 (k)). lra. lra.
    (* 根据H14 H15 H16证明.
       M1[k]是整个区间上的上确界, 但M2[k]和M2[S k]是分成两段的上确界. *) }
  assert  (M1[k] <= M).
  { destruct H2. pose proof (H3 k). cut((k <= n)%nat); 
    intros;[|lia].
    apply H17 in H18. destruct H18 as [H18 _].
    apply (sup_subsup f a b T[k] T[S k]); auto.
    apply (a_b_c T a b n k ); auto. lia. } 
  split.
  - rewrite H11. 
    red in H0. destruct H0 as [_[_ [H0 _]]].
    pose proof (H0 (S k)).  pose proof (H0 k). 
    apply Rplus_le_le_0_compat; apply Rmult_le_pos; lra.
  - assert  (ST -ST1 <= (M - m) * (T'[S k] - T'[k])
      + (M - m) * (T'[S (S k)] - T'[S k])).
    { rewrite H11. red in H0. destruct H0 as [_[_ [H0 _]]].
      pose proof (H0 (S k)).  pose proof (H0 k). 
      apply Rplus_le_compat; apply Rmult_le_compat_r; lra.  }
    assert  ((M - m) * (T'[S k] - T'[k])
      + (M - m) * (T'[S (S k)] - T'[S k])
      = (M - m) * (T'[S (S k)] - T'[k])). { (* 分配律 *) lra. }
    rewrite H18,<-H8 in H17.
    (* (T[S k] - T[k])小于T的模 *) 
    destruct H5.
    pose proof (Lemma9_1_2 T a b (S n) k H19 H).
   assert ((M - m) * (T [S k] - T [k]) <= (M - m) * mold T (S n)).
   apply Rmult_le_compat_l. assert (m <= M). destruct H2.
   apply (sup_inf f a b); auto. lra. auto. lra.
Qed.


Lemma Lemma9_6_3:∀(f : set (prod nat nat))(n:nat),
  StrictlyIncreaseFun_nat f -> dom[f] = Full nat -> (f\[n\] >= n)%nat.
Proof. 
  intros. red in H. induction n. lia. 
  assert ([n,f\[n\]] ∈ f).
  { apply x_fx_N; auto. tauto. rewrite H0.
    apply AxiomII; auto. }
  assert ([S n,f\[S n\]] ∈ f).
  { apply x_fx_N; auto. tauto. rewrite H0.
    apply AxiomII; auto. }
  destruct H.
  pose proof (H3 n (f \[ n \]) (S n) (f \[ S n \]) H1 H2). 
  cut ((n < S n)%nat); [|lia]. intros.
  apply H4 in H5; lia.
Qed.

Lemma Lemma9_6_4:∀(T T': Seq),SubSeq T' T -> 
(∀(k m:nat),(k < m)%nat -> T'[k] < T'[m])
-> (∀n, T[S n] = T'[S n]->  T[n] = T'[n]).
Proof. 
  intros. red in H. destruct H as [H[H' [f [H2 [H3 H4]]]]].
  pose proof (H4 (S n)). rewrite H5 in H1.
  pose proof (H4 (n)).  
  assert (f \[(S n)\]> f \[ n \])%nat.
  { red in H2. destruct H2 as [H2 H2'].
    assert ([n, f\[n\]] ∈ f).
    apply x_fx_N; auto. rewrite H3. apply AxiomII; auto.  
    assert ([S n, f \[S n \]] ∈ f).
    apply x_fx_N; auto. rewrite H3. apply AxiomII; auto. 
    pose proof (H2' n (f \[ n \]) (S n) (f \[ S n \]) H7 H8).
    apply H9;lia. }
  pose proof (H0 (f \[ n \]) (f \[(S n)\]) H7).  
  rewrite H1 in H8. 
  assert (f \[ n \] < S n)%nat. 
  { destruct(classic((f \[ n \] < S n)%nat)).
    auto. apply not_lt in H9.
    apply le_lt_or_eq in H9. destruct H9.
    apply H0 in H9. lra. rewrite H9 in H8.
    lra. }
  assert ((f \[ n \] <= n)%nat). lia.
  assert ((∀n,f\[n\] >= n)%nat). intros.  
  apply Lemma9_6_3; auto. 
  pose proof (H11 n). 
  assert ((f \[ n \] = n)%nat). lia.
  rewrite H13 in H6. auto.
Qed.
  
 
Lemma Lemma9_6_5 : ∀(T T': Seq)(n: nat)(a b:R),SubSeq T' T ->
(∀(k m:nat),(k < m)%nat -> T'[k] < T'[m]) -> T[n] = T'[n]  ->
(∀m,(m < n)%nat ->  T[m] = T'[m]).
Proof.
  intros. induction n. lia.  
  assert (T [n] = T' [n]). 
  apply (Lemma9_6_4 T T' H H0); auto.
  assert ((m <= n)%nat). lia. 
  apply le_lt_or_eq in H4. destruct H4.
  auto. rewrite H4. auto.
Qed.  
  
  
Definition minN (A : set nat) (n : nat) :=
    n ∈ A /\ (∀ x, x ∈ A -> x >= n)%nat.
Theorem finite_minN : ∀ (A : set nat),
    NotEmptyFinite A -> (∃ n : nat, minN A n).
Proof.
Admitted.


Lemma Lemma_9_6_6 : ∀ (f : set (prod nat nat)), dom[f] = Full nat
  -> StrictlyIncreaseFun_nat f -> StrictlyIncreaseFun_nat (f﹣¹).
Proof.
  intros. destruct H0. split; intros.
  - Locate Function. unfold Function. intros.
    applyAxiomII' H2. applyAxiomII' H3. admit.
  - applyAxiomII' H2. applyAxiomII' H3. admit.
Admitted.

Theorem Lemma_inver_N : ∀(f : set (prod nat nat)),
  dom[f ﹣¹] = ran[f] /\ ran[f ﹣¹] = dom[f]. 
Proof. 
   intros. split.
   - apply AxiomI. split; intros. 
      + apply AxiomII. applyAxiomII H. destruct H as [y].
        applyAxiomII' H. exists y; auto.
      + apply AxiomII. applyAxiomII H. destruct H as [y].
        exists y.  apply AxiomII'. auto.
   - apply AxiomI. split; intros. 
      + apply AxiomII. applyAxiomII H. destruct H as [y].
        applyAxiomII' H. exists y; auto.
      + apply AxiomII. applyAxiomII H. destruct H as [y].
        exists y.  apply AxiomII'. auto.
Qed.

Lemma Lemma_Inverse_N: ∀(f : set (prod nat nat)) (x: nat),
 Function f -> Function f﹣¹ -> x ∈ dom[f] -> f ﹣¹\[f \[x\]\] = x.
Proof.
  intros. 
  apply f_x_N; auto. apply AxiomII'.
  apply x_fx_N; auto.
Qed.

Lemma Lemma_Inverse_N': ∀(f : set (prod nat nat)) (y: nat),
 Function f -> Function f﹣¹ ->  y ∈ dom[f ﹣¹] 
 -> (f\[f ﹣¹\[y\]\] = y)%nat.
Proof. 
  intros f y H H' H0. 
  apply f_x_N; auto. assert((f ﹣¹)\[y\] ∈ ran[f ﹣¹]).
  { apply fx_ran_N; auto.  }
  assert (∃x , x = (f ﹣¹) \[y\]).
  { exists (f ﹣¹) \[y\]. auto. }
  destruct H2 as [x H2].
  rewrite <- H2.
  pose proof Lemma_Inverse_N.
  rewrite <- H2 in H1.
  pose proof Lemma_inver_N f. 
  destruct H4. rewrite H5 in H1. 
  pose proof H' as I1.
  apply (H3 f x) in H'; auto.
  red in H. red in I1.
  assert ([f \[x\], x] ∈ f ﹣¹).
  { apply AxiomII'. apply x_fx_N; auto. }
  assert ([y , x] ∈ f ﹣¹).
  { rewrite H2. apply x_fx_N; auto. }
  applyAxiomII' H7; auto. 
Qed.


Lemma Lemma9_6_7 : ∀(T T': Seq) (a b :R) (n p: nat), sum_seg1 T T' a b n p
  -> (p > 0)%nat -> ∃ k : nat, ∀ i ,T[i] <> T'[k] /\ (k < S n + p)%nat.
Proof.
  intros. 
  assert (\{ λ u : nat, T[u] <> T'[u] /\ (u <=S n)%nat \} ⊂ 
  \{ λ u : nat,(u <= S n + p)%nat \}).
  { red. intros. applyAxiomII H1. apply AxiomII. lia. }
  assert (NotEmptyFinite \{ λ u : nat, T[u] <> T'[u] /\ (u <=S n)%nat\}).
  { apply SubSetFinite_N in H1. destruct H1; auto.
    cut (NotEmpty \{ λ u,T [u] <> T' [u] /\ (u <= S n)%nat \}); intros.
    apply not_empty in H1; auto. contradiction. exists (S n). 
    destruct H as [H[H4 H5]]. destruct H.
    pose proof H4 as [H1' H5']. destruct H5' as [H5'[_ [_ H5'']]].
    cut(T' [S n] < b); intros. apply AxiomII; split; try lra; lia.
    rewrite <- H5''. apply (Increase_seg _ a b (S n + p)); auto.
    lia. left; apply NatFinite. }
  apply finite_minN in H2. destruct H2 as [k].
  exists k. destruct H2 as [H8' H9]. 
  intros. applyAxiomII H8'. split; [|try lia].
  destruct (Nat.eq_dec i k). rewrite e. lra.
  apply (not_eq i k) in n0. destruct n0.
  assert (T'[i] < T'[k]). destruct H as [H[H3 H4]].
  apply (Increase_seg _ a b (S n + p)); auto.
  - assert (T[i] = T'[i]). 
    { destruct (Req_dec T[i] T'[i]); auto. 
      cut(i ∈ \{ λ u,T [u] <> T' [u] /\ (u <= S n)%nat \});intros. 
      apply H9 in H5. lia. apply AxiomII; split; auto. lia. }
      rewrite H4. lra.
  - destruct H as [H4[H4' H10]]. destruct H10 as [H10[H3 [f [H5 [H6 H7]]]]]. 
    pose proof (H7 k). apply (Lemma9_6_3 f k) in H5; auto.
    apply le_lt_or_eq in H5. destruct H5.
    apply (Increase_seg _ a b (S n) H4) in H2. 
    apply (Increase_seg _ a b (S n + p) H4') in H5; auto.
    lra. rewrite H5. rewrite <- H. 
    apply (Increase_seg _ a b (S n) H4) in H2. lra.
Qed.

Lemma Lemma9_6_8: ∀(f : Fun)(T : Seq)(i:nat)(M m : R), T[i] < T[S i] 
  -> T[S i] < T[S (S i)] -> sup_f (\[T[i], T[S i] \]) f M 
  -> sup_f (\[T[S i], T[S (S i)] \]) f m 
  -> sup_f (\[T[i], T[S (S i)] \]) f (Rbasic_fun.Rmax M m).
Proof.
  intros. 
Admitted.

Lemma Lemma9_6_9: ∀(T T': Seq)(n p:nat)(a b :R), 
  sum_seg1 T T' a b n p -> (mold T n) >= (mold T' (S n + p)).
Proof.
  intros. red in H. 
  
Admitted.
  
  

(* 性质2 对分割T增加p个分割点得到T' *)
Fact Fact9_6_2:∀ (f : Fun)(T T': Seq) (a b :R) (n p: nat)(ST ST1 M m: R),
Up_sum f T a b ST n -> Up_sum f T' a b ST1 (n + p)%nat
-> sum_seg1 T T' a b n p  -> sup_f (\[a,b\]) f M  /\ inf_f (\[a,b\]) f m 
-> 0 <= ST - ST1 <= (M - m) *(mold T n)*INR(p).
Proof.
  intros. generalize dependent f. generalize dependent T.
  generalize dependent T'. generalize dependent a.
  generalize dependent b. generalize dependent n.
  generalize dependent ST. generalize dependent ST1.
  generalize dependent M. generalize dependent m.
  induction p.
  - intros. destruct H1 as [H1[]]. simpl in *.
    rewrite Nat.add_0_r in H3,H0. rewrite Rmult_0_r.
    pose proof (Increase_seg T' a b (S n)).
    assert (∀(k m:nat),(k < m)%nat -> T'[k] < T'[m]).
    { apply H5; auto. }
    assert (T'[S n] = T[S n]).
    { admit. }
    assert (∀m,(m <= S n)%nat ->  T[m] = T'[m]).
    { admit. (*apply Lemma9_6_5; auto. *) }
    red in H. red in H0.
    destruct H as [_ [M1]].
    destruct H0 as [_ [M2]].
    assert (∀m : nat,(m < S n)%nat -> M1[m] = M2[m]).
    { intros. cut (m0<=n)%nat. intros.
      apply H in H10 as H'. apply H0 in H10 as H0'.
      destruct H0' as [H0' H11]. destruct H' as [H' Hh12].
      rewrite H8 in H'; auto. rewrite H8 in H'; auto.
      apply (Lemma6_2 f (\[ T' [m0], T' [S m0] \])); auto.
      lia. }
    assert (ST1 = ST).
    { assert (n<=n)%nat. lia.
      apply H in H10 as H10'. apply H0 in H10 as H11'.
      destruct H11'. destruct H10'.
      rewrite H12.  rewrite H14. apply Lemma9_1''.
      intros. repeat rewrite FunValueR. 
      rewrite H9; auto. repeat rewrite H8; auto.
      lia. } lra.
  - intros. pose proof H1 as H1'.
    destruct H1 as [H1[H5[H6[]]]].
    destruct H4 as [f'].
    assert (H9: ∃ k, ∀ i ,T[i] <> T'[k] /\ (k < S n + S p)%nat).
    { apply (Lemma9_6_7 _ _ a b _ _); auto. lia. }
    destruct H9 as [k].
    
    assert (H10 : ∃ h,h= \{\ λ i h':nat,  (i < k)%nat /\ h' = i 
      \/ (i >= k)%nat /\ h' = S i \}\ /\ StrictlyIncreaseFun_nat h 
      /\dom[ h] = Full nat).
      { exists \{\  λ i f : nat,  (i < k)%nat /\ f = i 
      \/ (i >= k)%nat /\ f = S i \}\; split; auto.
       admit. }
    destruct H10 as [h']. 
     
    assert(∃ X, X = \{\ λ i f, (i < k)%nat /\ f = T'[i] 
      \/ (i >= k)%nat /\ f = T'[S i] \}\).
    { exists \{\ λ i f, (i < k)%nat /\ f = T'[i] 
      \/ (i >= k)%nat /\ f = T'[S i] \}\; auto.  }
    destruct H9 as [X].
    
    assert (H11: sum_seg1 X T' a b (n + p) 1%nat).
    { red. split.  
    
     admit.
      cut (S (n + p) + 1 = S n + S p)%nat. intros. 
      rewrite H10. split; auto. destruct H6.
      repeat split; auto. admit. admit.
      exists h'. split. tauto. split. tauto. 
      intros. admit. lia.  }
    assert (sum_seg1 T X a b n p).
    { split; auto. pose proof H11 as H11'. 
      assert(∀i : nat,X [i] <> T' [k] /\ (k < S (n + p) + 1)%nat).
      { intros. pose proof (H7 i). split;[|lia].
      destruct H11' as [_[_[_ [[H11' H12'] _]]]].
        destruct (classic ((i < k)%nat)).
        cut(X[i] = T'[i]);intros. 
        apply (Increase_seg T' a b (S n + S p)) in H12; auto.
        lra.  apply f_x; auto.
        rewrite H9. apply AxiomII'. left. split;[lia|auto].  
        cut(S i > k)%nat; intros; [|lia].
        apply (Increase_seg T' a b (S n + S p)) in H13; auto.
        cut(X[i] = T'[S i]); intros. lra. apply f_x; auto.
        rewrite H9. apply AxiomII'. right. split; [lia|auto]. }
      destruct H11 as [H11 [I1 [_ [[I2 I2'] I3]]]].
      destruct I3 as [h[I3 [I4 I5]]].
      split; auto. split; auto. split; auto.
      assert(∀i : nat,(i < k)%nat -> h\[i\] = i).
      { intros. cut(X[i] = T'[i]);intros.
        pose proof (I5 i). rewrite H13 in H14.
        apply (equal_seg T' a b (S (n + p) + 1)); auto.
        apply f_x; auto. rewrite H9. apply AxiomII'. left; split; [lia|auto]. }
      assert(∀i : nat,(i >= k)%nat -> h\[i\] =S i).
      { intros. cut(X[i] = T'[S i]);intros.
        pose proof (I5 i).
        rewrite H14 in H15.
        apply (equal_seg T' a b (S (n + p) + 1)); auto.
        apply f_x; auto. rewrite H9.
        apply AxiomII'. right; split; [lia|auto]. }
      split; auto. 
      exists\{\ λ i h':nat, h' = (h﹣¹)\[f'\[i\]\]%nat \}\.
      assert (dom[h﹣¹] = Full nat \~ [k]).
      { destruct (Lemma_inver_N h). rewrite H14.
        apply AxiomI. destruct I3 as [I6 I7]. 
        split; intros.
        - apply AxiomII. split. apply AxiomII; auto.
          apply AxiomII. intro. applyAxiomII H17.
          applyAxiomII H16. destruct H16 as [x].
          rewrite H17 in H16. assert(h\[x\] = k).
          apply f_x_N; auto. pose proof (I5 x).
          pose proof (H10 x). rewrite H18 in H19. lra. 
        - applyAxiomII H16. apply AxiomII.
          destruct (classic ((z < k)%nat)). exists z.
          assert(h\[z\] = z). apply H12; lia.
          cut([z, h\[z\]] ∈ h); intros. 
          rewrite H18 in H19; auto. apply x_fx_N; auto.
          rewrite I4; apply AxiomII; auto. 
          exists (pred z). destruct H16. cut(z <> k); intros. 
          assert((Init.Nat.pred z >= k)%nat). apply not_lt in H17.
          lia. apply (H13 (pred z)) in H20. 
          replace (S (Init.Nat.pred z)) with z in H20; [|lia].
          cut([pred z, h \[pred z \] ] ∈ h); intros.  
          rewrite H20 in H21; auto. apply x_fx_N; auto.
          rewrite I4; apply AxiomII; auto. applyAxiomII H18. 
          intro. apply H18. apply AxiomII; auto. }
       assert(I7:Function \{\ λ i h'0,h'0 = (h ﹣¹) \[ f' \[ i \] \] \}\).
       { red; intros. applyAxiomII' H15.
        applyAxiomII' H16. rewrite H16. auto. }
       repeat split; auto. 
      - assert (H12' :∀i : nat, f'\[i\] <> k).
        { intros. intro.  destruct H4 as [_ [_ H4']].
        pose proof (H4' i). rewrite H15 in H4.
        pose proof (H7 i). lra. } 
        intros. applyAxiomII' H15. applyAxiomII' H16.  
        pose proof I3 as I3'.
        apply Lemma_9_6_6 in I3 as []; auto.
        apply (H19 (f'\[ x1 \]) y1 (f'\[ x2 \]) y2); auto.
        rewrite H15; apply x_fx_N; auto. rewrite H14;
        apply AxiomII; split; apply AxiomII; auto.
        intro; applyAxiomII H20; pose proof (H12' x1); lia.
        rewrite H16; apply x_fx_N; auto; rewrite H14;
        apply AxiomII; split; apply AxiomII; auto;
        intro; applyAxiomII H20; pose proof (H12' x2); lia.
        destruct H4 as [[H4 H5'] [H4' _]]. 
        apply (H5' x1 (f' \[ x1 \]) x2 (f' \[ x2 \])); auto;
        apply x_fx_N; auto; rewrite H4'; apply AxiomII; auto.
      - apply AxiomI. 
        split; intros. apply AxiomII; auto.
        apply AxiomII. exists (h ﹣¹) \[ f' \[ z \] \] .
        apply AxiomII'. auto.
      - intros. 
        cut(\{\ λ i h'0,h'0 = (h ﹣¹) \[ f' \[ i \] \] \}\ \[ n0 \] 
        = (h ﹣¹) \[ f' \[ n0 \] \]); intros. 
        rewrite H15. pose proof (I5 (h ﹣¹) \[ f' \[ n0 \] \]).
        assert(h \[ (h ﹣¹) \[ f' \[ n0 \] \] \] = f' \[ n0 \] ).
        pose proof I3 as I3'. apply Lemma_9_6_6 in I3.
        destruct I3 as [I3 I6]. destruct I3' as [I3' I6'].  
        apply Lemma_Inverse_N'; auto.  
        rewrite H14. apply AxiomII. split.
        apply AxiomII; auto. apply AxiomII. intro.
        applyAxiomII H17. pose proof (H7 n0).
        rewrite <- H17 in H18. destruct H4 as [_[_ H4]].
        pose proof (H4 n0). lra. auto. rewrite H17 in H16.
        rewrite H16. destruct H4 as [_[_ H4]]. pose proof (H4 n0); auto.
        apply f_x_N; auto. apply AxiomII'; auto. }
      pose proof H0 as H0''. 
      destruct H0 as [L1 [M' L2]]. 
      pose proof H11 as H11'. destruct H11 as [[_[[L4 L4'] H11]]L3]. 
      assert(∃M:Seq, ∀ i, (i <= n + p)%nat ->
       ∃t,M[i] = t /\ sup_f (\[X[i] , X[S i] \]) f t).
      { exists (\{\ λ(i : nat)(f : R), (i < pred k)%nat /\ f = M' [i] 
        \/ (i > pred k)%nat /\ f = M' [S i] \/ (i = pred k)%nat 
        /\ f = Rbasic_fun.Rmax M'[i] M'[S i] \}\).
      cut(Function \{\ λ(i : nat)(f : R), (i < pred k)%nat /\ f = M' [i] 
        \/ (i > pred k)%nat /\ f = M' [S i] \/ (i = pred k)%nat 
        /\ f = Rbasic_fun.Rmax M'[i] M'[S i] \}\); intros.
      cut(∀i : nat,(i < k)%nat -> X[i] = T'[i]); intros.
      cut(∀i : nat,(i >= k)%nat -> X[i] = T'[S i]); intros.
      pose proof (H7 i) as [_ H7']. 
      destruct (classic ((i < pred k)%nat)).
      exists M'[i]. split. apply f_x; auto. apply AxiomII'.
      left. split; [lia|auto].   
      rewrite (H13 i);[|lia]. rewrite (H13 (S i));[|lia].
      apply (L2 i). lia. apply not_lt in H15. 
      destruct (classic ((i = pred k)%nat)).
      exists (Rbasic_fun.Rmax M'[i] M'[S i]). 
      split. apply f_x; auto. apply AxiomII'. right. right.
      split;[lia|auto]. rewrite (H13 (i)). rewrite (H14 (S i)).
      apply Lemma9_6_8. apply (Increase_seg T' a b (S n + S p)); auto.
      apply (Increase_seg T' a b (S n + S p)); auto. 
      apply (L2 i); lia. apply (L2 (S i)); lia. lia.
      assert(k > 0)%nat. admit. lia. 
      exists (M'[S i]). split. apply f_x; auto.
      apply AxiomII'. right; left; split; [lia|auto].  
      rewrite (H14 i); [|lia]. rewrite (H14 (S i));[|lia].
      apply (L2 (S i)). lia. 
      apply f_x; auto. rewrite H9; apply AxiomII'. right; split; [lia|auto].
      apply f_x; auto. rewrite H9; apply AxiomII'. left; split; [lia|auto].
      red; intros. applyAxiomII' H0. applyAxiomII' H12.
      destruct H0, H12;[lra|lia|lia|].  
      destruct H0, H12;[lra|lia|lia|]. lra. }
      assert(∃ST2, Up_sum f X a b ST2 (n + p)).
      { destruct H0 as [Mx]. 
        exists (Σ \{\ λ(i0 : nat)(s : R),s = Mx [i0] * (X [S i0] - X [i0]) \}\ 
       (n + p)%nat). 
       destruct H10 as [H10[H13 H14]]. split; auto. 
       exists Mx. intros. apply H0 in H12. destruct H12 as [t[H12 H15]].
       rewrite H12. split; auto. }
      destruct H12 as [ST2]. 
      apply (IHp m M ST2 ST n b a X T H10 f) in H; auto. 
      replace (n + S p)%nat with (S (n + p)) in H0'';[|lia].
      apply (Fact9_6_2' f X T' a b (n+p) ST2 ST1 M m) in H11'; auto.
      apply (Lemma9_6_9 T X n p a b) in H10. destruct H2.
      apply (sup_inf f a b m M) in H13; auto. 
      assert(ST2 - ST1 <= (M - m) * mold T n).
      { 
        apply (Rle_trans _ ((M - m) * mold X (S (n + p)))_); auto.
        lra. replace ((S n) + p)%nat with ((S (n + p))) in H10.
        apply Rmult_le_compat_l; lra. lia. }
      split. lra. 
      destruct H. apply (Rplus_le_compat (ST - ST2) 
      ((M - m) * mold T n * INR p) _ _ ) in H14; auto.
      replace (ST - ST2 + (ST2 - ST1)) with (ST - ST1) in H14.
      replace ((M - m) * mold T n * INR p + (M - m) * mold T n) with 
      ((M - m) * mold T n * INR (S p)) in H14. lra.

   Admitted.
   
   
Fact Fact9_6_3:∀ (f : Fun)(T' T'' T: Seq) (a b :R) (n p: nat)
  (ST' ST'' ST M m: R),Up_sum f T' a b ST' n -> Up_sum f T'' a b ST'' p 
  -> sup_f (\[a,b\]) f M  /\ inf_f (\[a,b\]) f m 
  -> sum_seg1 T' T a b n p -> Up_sum f T a b ST (n + p)%nat
  -> ST' >= ST.
Proof.
  intros. 
  apply (Fact9_6_2 f T' T a b n p ST' ST M m) in H; auto.
  lra.
Qed.


(* 一个分割的下和总不大于另一个分割的上和 *)
Fact Fact9_6_4:∀ (f : Fun)(T' T'': Seq) (a b :R) (n p: nat)
  (ST'' St' M m: R), Low_sum f T' a b St' n -> Up_sum f T'' a b ST'' p 
  -> sup_f (\[a,b\]) f M  /\ inf_f (\[a,b\]) f m 
  -> ST'' >= St'.
Proof. 
  intros. 
  (* 先证明T是T'和T''两个分割合并的分割 *)
Admitted.
   
(* 所有分割的上和有下界 *)
Definition Upsum_Lower_Bound(a b S : R)(f : Fun) := 
  inf \{λ ST :R,∀ n T, Up_sum f T a b ST n \} S.


(* 所有分割的下和有上界 *)
Definition Lowsum_Upper_Bound(a b s : R)(f : Fun) := 
  sup \{λ ST :R,∀ n T, Low_sum f T a b ST n \} s.  


Fact Fact9_6_5:∀ (f : Fun)(a b m M Sum sum:R), a < b 
  -> Upsum_Lower_Bound a b Sum f -> Lowsum_Upper_Bound a b sum f 
  -> sup_f (\[a,b\]) f M  /\ inf_f (\[a,b\]) f m
  -> m <= sum /\ sum <= Sum /\ Sum <= M.
Proof.
  intros. destruct H1, H0. assert(∃n1 n2,n2 > 0 /\  n1 > 0)%nat.
  { exists 1%nat, 2%nat. lia. }
  destruct H5 as [n1 [n2 [H6 H7]]].
  apply (Exists_seg a b n1) in H as H8.
  apply (Exists_seg a b n2) in H as H9.
  destruct H8 as [T[H8' H8]]. destruct H9 as [T'[H9' H9]].
  destruct H2 as [[H2 H10][H11 H12]].
  assert(∀i,(i <= n1)%nat -> ∃t, sup_f (\[ T [i], T [S i] \]) f t).
  { intros. 
  assert(∃η, sup \{ λ s,∃x : R,s = f [x] /\ x ∈ \[ T [i], T [S i] \] \} η).
  { apply Sup_principle. exists(f[T[i]]).
    apply AxiomII. exists T[i]. split; auto.
    apply AxiomII. split. lra.
    left. apply (Increase_seg _ a b (S n1)); auto. 
    exists M. red. intros. applyAxiomII H13. destruct H13 as [x0[]].
    apply H2. apply AxiomII. exists x0. split; auto.
    apply AxiomII. applyAxiomII H14. 
    pose proof (Nat.le_0_l i). destruct H15. 
    Search(_<=_)%nat. apply le_lt_or_eq in H5 as [H5 H5'].
    
    pose proof H8 as H1'. destruct H1' as [I1[I2[I3 [I4 I5]]]].
    rewrite I4 in H14. 
     red in H1'.
    
    
    
    
    Search(0<=_)%nat.
    
    
    pose proof (H1 x). 
      }
  
  
  exists m. red.   }
  
  
  assert(∃ST,Up_sum f T a b ST n1).
  
  { assert(∃M0 : Seq,∀i : nat,(i <= n1)%nat ->
          ∃t,M0[i] = t /\sup_f (\[ T [i], T [S i] \]) f t).
    { exists \{\ λ i m', sup_f (\[ T [i], T [S i] \]) f m' \}\.
      intros.     } 
  

  { intros. destruct H2. destruct H2.
    assert(NotEmpty \{ λ s,∃x : R,s = f [x] /\ x ∈ D \}).
    {  }
    exists M. red.  
    assert(∀x,x ∈ D -> f[x] <= M).
    { admit. }
    
  
  
  
  exists M.
    split. red. intros. applyAxiomII H12. destruct H12 as [x0[H12 H12']].
    admit. intros. red in H2. 
    }
  
  
   destruct  H1, H0.
    




   
Theorem Theorem9_15:∀(f:Fun)(a b J:R), defIntegral f a b J <->
  (∀ε : R,ε > 0 -> ∃(T:Seq)(n : nat), seg T a b (S n) 
  -> (∃(ST sT :R),Up_sum f T a b ST n /\ Low_sum f T a b sT n 
  -> ST - sT < ε)).
Proof. 
  intros.
Admitted.




End A9_6.
Export A9_6.






    

