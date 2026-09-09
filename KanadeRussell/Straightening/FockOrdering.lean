import KanadeRussell.Straightening.NormalizeOrdering
import KanadeRussell.Tsuchioka.ConcreteOrdering
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-! The normalized ordering expansion on the constructed Fock representation. -/
namespace KanadeRussell.Straightening
open Tsuchioka PowerSeries
variable {K : Type*} [Field K] [CharZero K]

theorem fock_pairSum_eq_convolution (w : K) (h : PowerSeries K) (a b : ℤ) (t : Word) :
    pairSum (Fock.highestWeightAction w) (fun p => coeff p h) a b t =
      Fock.quadraticConvolution w h ((Fock.highestWeightAction w).wordValue t) a b := by
  obtain ⟨N,hN⟩ := pair_tails_zero (Fock.highestWeightAction w) a b t
  rw [pairSum_eq_sum _ _ a b t N (fun p hp => (hN p hp).1),
    Fock.quadraticConvolution_eq_sum_of_tail w h ((Fock.highestWeightAction w).wordValue t) a b N (fun p hp => (hN p hp).1)]
  rfl

theorem fock_mode_shorter (w : K) (a b : ℤ) (t : Word) :
    Fock.mode w (a+b) ((Fock.highestWeightAction w).wordValue t) ∈
      shorterSpan (K := K) (fun u => (Fock.highestWeightAction w).wordValue (u ++ t)) [a,b] := by
  apply Submodule.subset_span
  refine ⟨[a+b], ⟨by simp, by simp⟩, ?_⟩
  rfl

theorem fock_central_shorter (w : K) (a b : ℤ) (t : Word) (c : K) :
    (if a+b=0 then c • (Fock.highestWeightAction w).wordValue t else 0) ∈
      shorterSpan (K := K) (fun u => (Fock.highestWeightAction w).wordValue (u ++ t)) [a,b] := by
  by_cases hab : a+b=0
  · rw [if_pos hab]
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact ⟨[], ⟨by simp, by simpa using hab.symm⟩, rfl⟩
  · rw [if_neg hab]
    exact Submodule.zero_mem _

theorem fock_G1_shorter_remainder (w : K) (hw : w^4-w^2+1=0)
    (a b : ℤ) (t : Word) :
    pairSum (Fock.highestWeightAction w) (fun p => coeff p (Scalar.G w 0)) a b t -
      pairSum (Fock.highestWeightAction w) (fun p => coeff p (Scalar.G w 0)) b a t -
      (skewPhase w a b/12) • Fock.secondRootMode w (a+b) ((Fock.highestWeightAction w).wordValue t) ∈
      shorterSpan (K := K) (fun u => (Fock.highestWeightAction w).wordValue (u ++ t)) [a,b] := by
  rw [fock_pairSum_eq_convolution, fock_pairSum_eq_convolution, Fock.G1_commutator w hw]
  let S := shorterSpan (K := K) (fun u => (Fock.highestWeightAction w).wordValue (u ++ t)) [a,b]
  have hf := S.smul_mem
    (Coefficients.pCoeff w * (w^(-2*a+2*b)-w^(2*a-2*b))/12) (fock_mode_shorter w a b t)
  have hz := fock_central_shorter w a b t (Scalar.cPrime w*(a:K)*(-1:K)^a/24)
  convert S.add_mem hf hz using 1
  simp only [skewPhase, Scalar.rootSecondResidue]
  module

theorem fock_G2_shorter_remainder (w : K) (hw : w^4-w^2+1=0)
    (a b : ℤ) (t : Word) :
    pairSum (Fock.highestWeightAction w) (fun p => coeff p (Scalar.G w 1)) a b t +
      pairSum (Fock.highestWeightAction w) (fun p => coeff p (Scalar.G w 1)) b a t -
      (symmetricPhase w a b/12) • Fock.secondRootMode w (a+b) ((Fock.highestWeightAction w).wordValue t) ∈
      shorterSpan (K := K) (fun u => (Fock.highestWeightAction w).wordValue (u ++ t)) [a,b] := by
  rw [fock_pairSum_eq_convolution, fock_pairSum_eq_convolution, Fock.G2_anticommutator w hw]
  let S := shorterSpan (K := K) (fun u => (Fock.highestWeightAction w).wordValue (u ++ t)) [a,b]
  have hm := fock_mode_shorter w a b t
  have hf := S.smul_mem (Scalar.aPrime w*(w^(-2*a+2*b)+w^(2*a-2*b))/12) hm
  have hz := fock_central_shorter w a b t (Scalar.cPrime w*(-1:K)^a/48)
  have ht := S.smul_mem ((-1:K)^(a+b)/3) hm
  convert S.add_mem (S.add_mem hf hz) ht using 1
  simp only [symmetricPhase, Coefficients.tCoeff]
  module

/-- The exact ordering coefficients are now obtained from concrete G1/G2 identities. -/
theorem fock_ordering_expansion (w : K) (hw : w^4-w^2+1=0)
    (a b : ℤ) (hab : b<a) (hne : (a-b)%12 ≠ 7) :
    PairExpansion (Fock.highestWeightAction w) a b (orderingCoeff w a b) := by
  apply ordering_expansion_of_combined_relation _ w hw a b hab hne
  intro t
  let S := shorterSpan (K := K) (fun u => (Fock.highestWeightAction w).wordValue (u ++ t)) [a,b]
  have h1 := S.smul_mem (symmetricPhase w a b) (fock_G1_shorter_remainder w hw a b t)
  have h2 := S.smul_mem (skewPhase w a b) (fock_G2_shorter_remainder w hw a b t)
  convert S.sub_mem h1 h2 using 1
  module

/-- In particular, the gap-two expansion used by F4 has no operator-relation hypothesis. -/
theorem fock_gapTwo_expansion (w : K) (hw : w^4-w^2+1=0) (a : ℤ) :
    PairExpansion (Fock.highestWeightAction w) (a+1) (a-1) (orderingCoeff w (a+1) (a-1)) :=
  fock_ordering_expansion w hw (a+1) (a-1) (by omega) (by omega)

end KanadeRussell.Straightening
