Require Export A_9_6.
Require Import Lia.

Module A9_3_2.

(* 可积函数类-----可积的充分条件 *)

Lemma Lemma9_4_1:∀ M m T n, Σ \{\ λ i m, m = M[i] * (T[S i] - T[i]) \}\ n
  - Σ \{\ λ i f, f = m[i] * (T[S i] - T[i]) \}\ n 
  = Σ \{\ λ i f, f = (M[i]-m[i]) * (T[S i] - T[i]) \}\ n.
Proof.
  intros. 
  induction n. simpl.
  - repeat rewrite FunValueR. lra. 
  - simpl. rewrite <- IHn.
    repeat rewrite FunValueR. lra.
Qed.


(* 可积的充分条件   连续--->可积 *)
Theorem Theorem9_4:∀(f:Fun)(a b J:R),ContinuousClose f a b 
 -> a < b -> defIntegral f a b J.
Proof.
  intros. apply Theorem4_9 in H. red in H.
  destruct H as [H[H2 H3]]. 
  apply Theorem9_15. intros.
  assert(ε /(b - a) > 0).
  { admit. } 
  apply H3 in H4. destruct H4 as [δ[H4 H5]].
  assert(∃(n:nat), INR n> ((b-a)/δ)). 
  { admit. }
  destruct H6 as [n].
  Locate Exists_seg.
  pose proof (Exists_seg a b n H0).
  destruct H7 as [T[H7 _]].
  exists T, n. intros.
  assert(∀ i, ∃t, sup_f (\[T[i] , T[S i] \]) f t).
  { intros. assert(ContinuousClose f T[i] T[S i]).
    admit. apply (Theorem4_6 f T[i] T[S i]) in H9.
    destruct H9 as [[max H9][min H10]]. 
    exists max. repeat red. red in H9. 
    destruct H9 as [H9[H9'[x0' H13]]].
    split. red. intros. applyAxiomII H11. 
    destruct H11 as [x0[H11 H12]].  rewrite H11.
    apply H9'; auto. intros. exists max.
    split;[|auto]. apply AxiomII. destruct H13. 
    exists x0'; split; try auto.  
    red in H8. destruct H8 as [_[_[H8 _]]].
    apply H8. }
  assert(∃M:Seq, ∀ i, ∃t,M[i] = t /\ sup_f (\[T[i] , T[S i] \]) f t).
  { exists (\{\ λ(i : nat)(s : R), sup_f (\[T[i] , T[S i] \]) f s \}\).
    intros. pose proof (H9 i). destruct H10 as [t].
    exists t. split;[|auto]. apply f_x.
    red. intros. applyAxiomII' H11.
    applyAxiomII' H12. admit.
    apply AxiomII'; auto. }
  destruct H10 as [M].
  exists (Σ \{\ λ(i0 : nat)(s : R),s = M [i0] * (T [S i0] - T [i0]) \}\ n).
  assert(∃m:Seq, m = \{\ λ(i : nat)(v : R), inf (\[T[i] , T[S i] \]) v \}\). 
  { exists \{\ λ(i : nat)(v : R), inf (\[T[i] , T[S i] \]) v \}\; auto. } 
  destruct H11 as [m].
  exists (Σ \{\ λ(i0 : nat)(s : R),s = m [i0] * (T [S i0] - T [i0]) \}\ n).
  intros. 
  assert(∀i:nat,M[i]-m[i] < ε / (b - a)) .
  { intros. 
    assert(sup_f' (\[ T [i], T [S i] \]) f M[i]). admit.
    red in H13. destruct H13 as [U[L[H13[H14 H15]]]]. 
    assert(L <= U).
    { red in H13. red in H14. admit.  }
    apply (Lemma1_1 L U) in H16 as H16'. 
    assert(M[i] = U). admit.
    apply (Lemma1_2 L U) in H16 as H16''. 
    assert(m[i] = L). admit.
    assert(∃t1,t1 ∈ (\[ T [i], T [S i] \]) /\ M[i] = f[t1]).
    { rewrite <- H17 in H14.
      red in H14. destruct H14 as [H14[H19[x0[H21 H20]]]].
      exists x0. split; auto. } 
    destruct H19 as [t1[H19' H20]]. 
    assert(∃t2,t2 ∈ (\[ T [i], T [S i] \]) /\ m[i] = f[t2]).
    { rewrite <- H18 in H13.
      red in H13. destruct H13 as [H13[H19[x0[H21 H22]]]].
      exists x0. split; auto. } 
    destruct H19 as [t2[H19'' H19]]. 
   rewrite H19. rewrite H20. 
   assert(Abs [f [t1] - f [t2]] < ε / (b - a)).
   { apply H5. admit. admit. admit.  }
   admit. }
   assert(Σ \{\ λ(i0 : nat)(s : R),s = M [i0] * (T [S i0] - T [i0]) \}\ n 
   - Σ \{\ λ(i0 : nat)(s : R),s = m [i0] * (T [S i0] - T [i0]) \}\ n = 
   Σ \{\ λ(i0 : nat)(s : R),s = (M [i0]-m [i0]) * (T [S i0] - T [i0]) \}\ n).
   apply Lemma9_4_1; auto.
   rewrite H14. 
   assert(∀i : nat, \{\ λ(i : nat)(s : R),s = ε / (b - a) * (T [S i] - T [i]) \}\[i]
   > \{\ λ(i0 : nat)(s : R),s = (M [i0] - m [i0]) * (T [S i0] - T [i0]) \}\[i]).
   { admit. }
   
   pose proof (Lemma9_1' n (\{\ λ(i : nat)(s : R),s = ε / (b - a) * (T [S i] - T [i]) \}\)
   (\{\ λ(i0 : nat)(s : R),s = (M [i0] - m [i0]) * (T [S i0] - T [i0]) \}\)).
   assert(Σ \{\ λ(i : nat)(s : R),s = ε / (b - a) * (T [S i] - T [i]) \}\ n 
   = ε / (b - a) * Σ \{\ λ(i : nat)(s : R),s = (T [S i] - T [i]) \}\ n).
   admit.
   apply (Lemma9_6_1_2 T n a b) in H8. 
   rewrite H8 in H17.
   assert((n <= n)%nat). lia.
   assert(Σ \{\ λ(i : nat)(s : R),s = ε / (b - a) * (T [S i] - T [i]) \}\ n >
      Σ \{\ λ(i0 : nat)(s : R),s = (M [i0] - m [i0]) * (T [S i0] - T [i0]) \}\
        n).
   apply H16. intros. 
   repeat rewrite FunValueR. admit.
   rewrite H17 in H19.
   admit.
Admitted.
   
(* Theorem Theorem9_5:∀(f:Fun)(a b J:R), IntervalBoundedFun f \[a, b\] 
  -> . *)
  
(* 区间单调 --> 可积 *) 
Theorem Theorem9_6:∀(f:Fun)(a b J:R),IntervalMonotonicFun f (\[a, b\]) 
  -> a < b -> defIntegral f a b J.
Proof.
  intros. red in H. apply Theorem9_15. destruct H.
  - red in H. destruct H as [H[H1 H2]].
    intros. assert(f[a] <= f[b]).
    { apply H2; auto; apply AxiomII; lra. }
    cut(f[a]<f[b] \/ f[a] = f[b]); intros;[|lra].
    destruct H5. 
    + assert(∃(n:nat), INR n> ((b-a)* (f[b]-f[a]) / ε)). 
      { admit. }    
      destruct H6 as [n].
      apply (Exists_seg a b n) in H0. destruct H0 as [T].
      exists T,n. intros.
      assert(∃M:Seq, ∀ i, M[i] = f[T[S i]]).
      { admit. } 
      assert(∃m:Seq, ∀ i, m[i] = f[T[i]]).
      { admit. }
      destruct H8 as [M]. destruct H9 as [m].
      exists(Σ \{\ λ(i0 : nat)(s : R),s = M [i0] * (T [S i0] - T [i0]) \}\ n).
      exists(Σ \{\ λ(i0 : nat)(s : R),s = m [i0] * (T [S i0] - T [i0]) \}\ n).
      intros. 
      assert(Σ \{\ λ(i0 : nat)(s : R),s = M [i0] * (T [S i0] - T [i0]) \}\ n 
   - Σ \{\ λ(i0 : nat)(s : R),s = m [i0] * (T [S i0] - T [i0]) \}\ n = 
   Σ \{\ λ(i0 : nat)(s : R),s = (M [i0]-m [i0]) * (T [S i0] - T [i0]) \}\ n).
   apply Lemma9_4_1.
   rewrite H11. 
   assert(∀i, (i <= n)%nat -> T[S i] - T[i] < ε / (f [b] - f [a])).
   { admit.  }
   assert(Σ \{\ λ(i0 : nat)(s : R),s = (M [i0] - m [i0]) * (T [S i0] - T [i0])
    \}\ n < Σ \{\ λ(i0 : nat)(s : R),s = (M [i0] - m [i0]) \}\ n 
    * ε / (f [b] - f [a])).
    admit.
    assert(Σ \{\ λ(i0 : nat)(s : R),s = (M [i0] - m [i0]) \}\ n  = f[b] - f[a]).
    admit.
    rewrite H14 in H13.
Admitted.

   
   
   
   
   
   
   
   
   
   
   
   
   
   

   