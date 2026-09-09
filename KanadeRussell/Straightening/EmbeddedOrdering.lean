import KanadeRussell.Straightening.EmbeddedAction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace KanadeRussell.Straightening.PolynomialAction
open Tsuchioka Tsuchioka.Fock PowerSeries
variable {K : Type*} [Field K] [CharZero K]
theorem pair_convolutions_eq_symmetricSum (w : K) (B : PolynomialAction w) (h : PowerSeries K)
    (a b : ℤ) (t : Word) (N : ℕ)
    (htail : ∀ p : ℕ, N ≤ p →
      B.action.wordValue ([a - p, b + p] ++ t) = 0 ∧
      B.action.wordValue ([b - p, a + p] ++ t) = 0) :
    quadraticConvolution w h (B.action.wordValue t) a b +
      quadraticConvolution w h (B.action.wordValue t) b a =
      symmetricSum (fun v => B.action.wordValue (v ++ t))
        (fun p => PowerSeries.coeff p h) a b N := by
  have hf : ∀ p : ℕ, N ≤ p →
      mode w (a - p) (mode w (b + p) (B.action.wordValue t)) = 0 :=
    fun p hp => (htail p hp).1
  have hr : ∀ p : ℕ, N ≤ p →
      mode w (b - p) (mode w (a + p) (B.action.wordValue t)) = 0 :=
    fun p hp => (htail p hp).2
  rw [quadraticConvolution_eq_sum_of_tail w h _ a b N hf,
    quadraticConvolution_eq_sum_of_tail w h _ b a N hr]
  simp only [symmetricSum, smul_add, Finset.sum_add_distrib]
  rfl

/-- A common finite cutoff works for every later truncation of the G2 relation
on each word suffix. Thus its use in algebraic straightening needs no infinite sum. -/
theorem G2_anticommutator_word_finite (w : K) (B : PolynomialAction w) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (a b : ℤ) (t : Word) :
    ∃ N : ℕ, ∀ M : ℕ, N ≤ M →
      symmetricSum (fun v => B.action.wordValue (v ++ t))
        (fun p => PowerSeries.coeff p (Scalar.G w 1)) a b (M + 1) =
        (Scalar.aPrime w * (w ^ (-2 * a + 2 * b) + w ^ (2 * a - 2 * b)) / 12) •
          mode w (a + b) (B.action.wordValue t) +
        (Coefficients.tCoeff w * (w ^ (4 * a + 9 * b) + w ^ (9 * a + 4 * b)) / 12) •
          secondRootMode w (a + b) (B.action.wordValue t) +
        (if a + b = 0 then (Scalar.cPrime w * (-1 : K) ^ a / 48) •
          B.action.wordValue t else 0) +
        ((-1 : K) ^ (a + b) / 3) • mode w (a + b) (B.action.wordValue t) := by
  obtain ⟨N, hN⟩ := pair_tails_zero B.action a b t
  refine ⟨N, ?_⟩
  intro M hM
  rw [← pair_convolutions_eq_symmetricSum w B (Scalar.G w 1) a b t (M + 1)
    (fun p hp => hN p (by omega))]
  exact G2_anticommutator w hw _ a b

theorem pair_convolutions_eq_skewSum (w : K) (B : PolynomialAction w) (h : PowerSeries K)
    (a b : ℤ) (t : Word) (N : ℕ)
    (htail : ∀ p : ℕ, N ≤ p →
      B.action.wordValue ([a - p, b + p] ++ t) = 0 ∧
      B.action.wordValue ([b - p, a + p] ++ t) = 0) :
    quadraticConvolution w h (B.action.wordValue t) a b -
      quadraticConvolution w h (B.action.wordValue t) b a =
      skewSum (fun v => B.action.wordValue (v ++ t))
        (fun p => PowerSeries.coeff p h) a b N := by
  have hf : ∀ p : ℕ, N ≤ p →
      mode w (a - p) (mode w (b + p) (B.action.wordValue t)) = 0 :=
    fun p hp => (htail p hp).1
  have hr : ∀ p : ℕ, N ≤ p →
      mode w (b - p) (mode w (a + p) (B.action.wordValue t)) = 0 :=
    fun p hp => (htail p hp).2
  rw [quadraticConvolution_eq_sum_of_tail w h _ a b N hf,
    quadraticConvolution_eq_sum_of_tail w h _ b a N hr]
  simp only [skewSum, smul_sub, Finset.sum_sub_distrib]
  rfl

theorem G1_commutator_word_finite (w : K) (B : PolynomialAction w) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (a b : ℤ) (t : Word) :
    ∃ N : ℕ, ∀ M : ℕ, N ≤ M →
      skewSum (fun v => B.action.wordValue (v ++ t))
        (fun p => PowerSeries.coeff p (Scalar.G w 0)) a b (M + 1) =
        (Coefficients.pCoeff w * (w ^ (-2 * a + 2 * b) - w ^ (2 * a - 2 * b)) / 12) •
          mode w (a + b) (B.action.wordValue t) +
        (Scalar.rootSecondResidue w * (w ^ (4 * a + 9 * b) - w ^ (9 * a + 4 * b)) / 12) •
          secondRootMode w (a + b) (B.action.wordValue t) +
        (if a + b = 0 then (Scalar.cPrime w * (a : K) * (-1 : K) ^ a / 24) •
          B.action.wordValue t else 0) := by
  obtain ⟨N, hN⟩ := pair_tails_zero B.action a b t
  refine ⟨N, ?_⟩
  intro M hM
  rw [← pair_convolutions_eq_skewSum w B (Scalar.G w 0) a b t (M + 1)
    (fun p hp => hN p (by omega))]
  exact G1_commutator w hw _ a b

theorem mode_pair_sum_mem (w : K) (B : PolynomialAction w) (a b : ℤ) (t : Word) :
    mode w (a + b) (B.action.wordValue t) ∈
      higherSpan (K := K) (fun v => B.action.wordValue (v ++ t)) [a, b] := by
  change B.action.wordValue ([a + b] ++ t) ∈ _
  exact mem_higherSpan _ (Or.inl (by simp)) (by simp)

theorem central_pair_mem (w : K) (B : PolynomialAction w) (a b : ℤ) (t : Word) (c : K) :
    (if a + b = 0 then c • B.action.wordValue t else 0) ∈
      higherSpan (K := K) (fun v => B.action.wordValue (v ++ t)) [a, b] := by
  by_cases hab : a + b = 0
  · rw [if_pos hab]
    apply Submodule.smul_mem
    change B.action.wordValue ([] ++ t) ∈ _
    exact mem_higherSpan _ (Or.inl (by simp)) (by simpa using hab.symm)
  · rw [if_neg hab]
    exact Submodule.zero_mem _

/-- The first commutator leaves only shorter words after its second-root term
is removed, also when applied at shifted indices of the same total. -/
theorem G1_relation_higher_remainder (w : K) (B : PolynomialAction w) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (a b c d : ℤ) (hcd : c + d = a + b) (t : Word) :
    ∃ N : ℕ, ∀ M : ℕ, N ≤ M →
      skewSum (fun v => B.action.wordValue (v ++ t))
          (fun p => PowerSeries.coeff p (Scalar.G w 0)) c d (M + 1) -
        (skewPhase w c d / 12) • secondRootMode w (a + b) (B.action.wordValue t) ∈
        higherSpan (K := K) (fun v => B.action.wordValue (v ++ t)) [a, b] := by
  obtain ⟨N, hN⟩ := G1_commutator_word_finite w B hw c d t
  refine ⟨N, ?_⟩
  intro M hM
  rw [hN M hM, hcd]
  let S := higherSpan (K := K) (fun v => B.action.wordValue (v ++ t)) [a, b]
  have hf := S.smul_mem
    (Coefficients.pCoeff w * (w ^ (-2 * c + 2 * d) - w ^ (2 * c - 2 * d)) / 12)
    (mode_pair_sum_mem w B a b t)
  have hz := central_pair_mem w B a b t (Scalar.cPrime w * (c : K) * (-1 : K) ^ c / 24)
  convert S.add_mem hf hz using 1
  simp only [skewPhase, Scalar.rootSecondResidue]
  module

theorem G2_relation_higher_remainder (w : K) (B : PolynomialAction w) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (a b : ℤ) (t : Word) :
    ∃ N : ℕ, ∀ M : ℕ, N ≤ M →
      symmetricSum (fun v => B.action.wordValue (v ++ t))
          (fun p => PowerSeries.coeff p (Scalar.G w 1)) a b (M + 1) -
        (symmetricPhase w a b / 12) •
          secondRootMode w (a + b) (B.action.wordValue t) ∈
        higherSpan (K := K) (fun v => B.action.wordValue (v ++ t)) [a, b] := by
  obtain ⟨N, hN⟩ := G2_anticommutator_word_finite w B hw a b t
  refine ⟨N, ?_⟩
  intro M hM
  rw [hN M hM]
  let S := higherSpan (K := K) (fun v => B.action.wordValue (v ++ t)) [a, b]
  have hm := mode_pair_sum_mem w B a b t
  have hf := S.smul_mem
    (Scalar.aPrime w * (w ^ (-2 * a + 2 * b) + w ^ (2 * a - 2 * b)) / 12) hm
  have hz := central_pair_mem w B a b t (Scalar.cPrime w * (-1 : K) ^ a / 48)
  have ht := S.smul_mem ((-1 : K) ^ (a + b) / 3) hm
  convert S.add_mem (S.add_mem hf hz) ht using 1
  simp only [symmetricPhase, Coefficients.tCoeff]
  module

/-- F1 for the constructed modes on every suffix vector. Both source relations
and the shifted exceptional relation have concrete finite proofs. -/
theorem local_ordering_reduction (w : K) (B : PolynomialAction w) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (a b : ℤ) (hab : b < a) :
    B.action.LocalReduction [a, b] := by
  intro t
  obtain ⟨N, hN⟩ := G1_relation_higher_remainder w B hw a b a b rfl t
  obtain ⟨M, hM⟩ := G2_relation_higher_remainder w B hw a b t
  obtain ⟨L, hL⟩ := G1_relation_higher_remainder w B hw a b (a - 1) (b + 1) (by ring) t
  exact ordering_reduction_of_relations w hw
    (fun v => B.action.wordValue (v ++ t)) _ _
    (Scalar.coeff_zero_G w 0) (Scalar.coeff_zero_G w 1) a b hab N M (L + 1)
    (secondRootMode w (a + b) (B.action.wordValue t))
    (hN N le_rfl) (hM M le_rfl) (hL L le_rfl)

theorem fock_pairSum_eq_convolution (w : K) (B : PolynomialAction w) (h : PowerSeries K) (a b : ℤ) (t : Word) :
    pairSum B.action (fun p => coeff p h) a b t =
      Fock.quadraticConvolution w h (B.action.wordValue t) a b := by
  obtain ⟨N,hN⟩ := pair_tails_zero B.action a b t
  rw [pairSum_eq_sum _ _ a b t N (fun p hp => (hN p hp).1),
    Fock.quadraticConvolution_eq_sum_of_tail w h (B.action.wordValue t) a b N (fun p hp => (hN p hp).1)]
  rfl

theorem fock_mode_shorter (w : K) (B : PolynomialAction w) (a b : ℤ) (t : Word) :
    Fock.mode w (a+b) (B.action.wordValue t) ∈
      shorterSpan (K := K) (fun u => B.action.wordValue (u ++ t)) [a,b] := by
  apply Submodule.subset_span
  refine ⟨[a+b], ⟨by simp, by simp⟩, ?_⟩
  rfl

theorem fock_central_shorter (w : K) (B : PolynomialAction w) (a b : ℤ) (t : Word) (c : K) :
    (if a+b=0 then c • B.action.wordValue t else 0) ∈
      shorterSpan (K := K) (fun u => B.action.wordValue (u ++ t)) [a,b] := by
  by_cases hab : a+b=0
  · rw [if_pos hab]
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact ⟨[], ⟨by simp, by simpa using hab.symm⟩, rfl⟩
  · rw [if_neg hab]
    exact Submodule.zero_mem _

theorem fock_G1_shorter_remainder (w : K) (B : PolynomialAction w) (hw : w^4-w^2+1=0)
    (a b : ℤ) (t : Word) :
    pairSum B.action (fun p => coeff p (Scalar.G w 0)) a b t -
      pairSum B.action (fun p => coeff p (Scalar.G w 0)) b a t -
      (skewPhase w a b/12) • Fock.secondRootMode w (a+b) (B.action.wordValue t) ∈
      shorterSpan (K := K) (fun u => B.action.wordValue (u ++ t)) [a,b] := by
  rw [fock_pairSum_eq_convolution, fock_pairSum_eq_convolution, Fock.G1_commutator w hw]
  let S := shorterSpan (K := K) (fun u => B.action.wordValue (u ++ t)) [a,b]
  have hf := S.smul_mem
    (Coefficients.pCoeff w * (w^(-2*a+2*b)-w^(2*a-2*b))/12) (fock_mode_shorter w B a b t)
  have hz := fock_central_shorter w B a b t (Scalar.cPrime w*(a:K)*(-1:K)^a/24)
  convert S.add_mem hf hz using 1
  simp only [skewPhase, Scalar.rootSecondResidue]
  module

theorem fock_G2_shorter_remainder (w : K) (B : PolynomialAction w) (hw : w^4-w^2+1=0)
    (a b : ℤ) (t : Word) :
    pairSum B.action (fun p => coeff p (Scalar.G w 1)) a b t +
      pairSum B.action (fun p => coeff p (Scalar.G w 1)) b a t -
      (symmetricPhase w a b/12) • Fock.secondRootMode w (a+b) (B.action.wordValue t) ∈
      shorterSpan (K := K) (fun u => B.action.wordValue (u ++ t)) [a,b] := by
  rw [fock_pairSum_eq_convolution, fock_pairSum_eq_convolution, Fock.G2_anticommutator w hw]
  let S := shorterSpan (K := K) (fun u => B.action.wordValue (u ++ t)) [a,b]
  have hm := fock_mode_shorter w B a b t
  have hf := S.smul_mem (Scalar.aPrime w*(w^(-2*a+2*b)+w^(2*a-2*b))/12) hm
  have hz := fock_central_shorter w B a b t (Scalar.cPrime w*(-1:K)^a/48)
  have ht := S.smul_mem ((-1:K)^(a+b)/3) hm
  convert S.add_mem (S.add_mem hf hz) ht using 1
  simp only [symmetricPhase, Coefficients.tCoeff]
  module

/-- The exact ordering coefficients are now obtained from concrete G1/G2 identities. -/
theorem fock_ordering_expansion (w : K) (B : PolynomialAction w) (hw : w^4-w^2+1=0)
    (a b : ℤ) (hab : b<a) (hne : (a-b)%12 ≠ 7) :
    PairExpansion B.action a b (orderingCoeff w a b) := by
  apply ordering_expansion_of_combined_relation _ w hw a b hab hne
  intro t
  let S := shorterSpan (K := K) (fun u => B.action.wordValue (u ++ t)) [a,b]
  have h1 := S.smul_mem (symmetricPhase w a b) (fock_G1_shorter_remainder w B hw a b t)
  have h2 := S.smul_mem (skewPhase w a b) (fock_G2_shorter_remainder w B hw a b t)
  convert S.sub_mem h1 h2 using 1
  module

/-- In particular, the gap-two expansion used by F4 has no operator-relation hypothesis. -/
theorem fock_gapTwo_expansion (w : K) (B : PolynomialAction w) (hw : w^4-w^2+1=0) (a : ℤ) :
    PairExpansion B.action (a+1) (a-1) (orderingCoeff w (a+1) (a-1)) :=
  fock_ordering_expansion w B hw (a+1) (a-1) (by omega) (by omega)


end KanadeRussell.Straightening.PolynomialAction
