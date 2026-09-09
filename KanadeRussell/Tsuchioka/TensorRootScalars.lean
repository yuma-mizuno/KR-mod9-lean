import KanadeRussell.Tsuchioka.TensorScalarFactors
import KanadeRussell.Tsuchioka.SourceEmbedding

/-! Ordinary rational scalar series for every pair of tensor roots.
Their binomial exponents are derived from the lattice and all polynomial
denominators have constant coefficient one. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.RootData

def rootPairingExponents (beta gamma : Lattice) (p : Fin 12) : ℤ :=
  pairing ((coxeter^[p.val]) beta) gamma

theorem rootPairingExponents_first_second :
    rootPairingExponents (simpleRoot 0) (simpleRoot 1) =
      ![-1, 0, -1, 1, 0, 1, 1, 0, 1, -1, 0, -1] := by
  decide

theorem rootPairingExponents_second_first :
    rootPairingExponents (simpleRoot 1) (simpleRoot 0) =
      ![-1, -1, 0, -1, 1, 0, 1, 1, 0, 1, -1, 0] := by
  decide

theorem rootPairingExponents_second_second :
    rootPairingExponents (simpleRoot 1) (simpleRoot 1) =
      ![2, -1, 1, 0, -1, 1, -2, 1, -1, 0, 1, -1] := by
  decide

end KanadeRussell.Tsuchioka.RootData

namespace KanadeRussell.Tsuchioka.Scalar

open PowerSeries FormalSeries
open RootData (Lattice rootPairingExponents)

variable {K : Type*} [Field K] [CharZero K]

noncomputable def rootScalar (w : K) (beta gamma : Lattice) : PowerSeries K :=
  ∏ p : Fin 12, binomialFactor (rootPairingExponents beta gamma p : ℚ)
    (w ^ (-(p.val : ℤ)))

noncomputable def orbitNumerator (w : K) (e : Fin 12 → ℤ) : Polynomial K :=
  ∏ p : Fin 12,
    (1 - Polynomial.C (w ^ (-(p.val : ℤ))) * Polynomial.X) ^ (e p).toNat

@[simp] theorem constantCoeff_rootScalar (w : K) (beta gamma : Lattice) :
    constantCoeff (rootScalar w beta gamma) = 1 := by
  simp [rootScalar, map_prod]

theorem coe_orbitNumerator (w : K) (e : Fin 12 → ℤ) :
    (orbitNumerator w e : PowerSeries K) =
      ∏ p : Fin 12, (1 - PowerSeries.C (w ^ (-(p.val : ℤ))) * X) ^ (e p).toNat := by
  change Polynomial.coeToPowerSeries.ringHom (orbitNumerator w e) = _
  simp [orbitNumerator, map_prod]

@[simp] theorem orbitNumerator_constantCoeff (w : K) (e : Fin 12 → ℤ) :
    (orbitNumerator w e).coeff 0 = 1 := by
  rw [← Polynomial.constantCoeff_apply]
  unfold orbitNumerator
  simp only [map_prod, map_pow]
  simp [Polynomial.constantCoeff_apply]

theorem orbitNumerator_isUnit (w : K) (e : Fin 12 → ℤ) :
    IsUnit (orbitNumerator w e : PowerSeries K) := by
  apply PowerSeries.isUnit_iff_constantCoeff.mpr
  simp

theorem rootScalar_cross (w : K) (beta gamma : Lattice) :
    rootScalar w beta gamma *
      (orbitNumerator w (-rootPairingExponents beta gamma) : PowerSeries K) =
        (orbitNumerator w (rootPairingExponents beta gamma) : PowerSeries K) := by
  simp only [rootScalar, coe_orbitNumerator, ← Finset.prod_mul_distrib, Pi.neg_apply]
  apply Finset.prod_congr rfl
  intro p hp
  exact binomialFactor_int_cross _ _

end KanadeRussell.Tsuchioka.Scalar

namespace KanadeRussell.Tsuchioka.Fock

open RootData (Lattice rootPairingExponents)

variable {K : Type*} [Field K] [CharZero K]

theorem ratioEmbedding_rootScalar (w : K) (beta gamma : Lattice) :
    ratioEmbedding (Scalar.rootScalar w beta gamma) = tensorOrbitProduct w beta gamma := by
  simp only [Scalar.rootScalar, tensorOrbitProduct, map_prod,
    ratioEmbedding_binomialFactor, ratioMonomial, rootPairingExponents]

theorem tensorTwoSummands_same_rootScalar (w : K)
    (hw : w ^ 4 - w ^ 2 + 1 = 0) (beta gamma : Lattice) (s : Fin 3) (f : Space K) :
    tensorTwoSummands w beta gamma s s f =
      tensorNormalProduct w beta gamma s s f *
        (ratioEmbedding (Scalar.rootScalar w beta gamma) :
          LaurentSeries (LaurentSeries (Space K))) := by
  rw [tensorTwoSummands_same_orbitProduct w hw, ratioEmbedding_rootScalar]

end KanadeRussell.Tsuchioka.Fock
