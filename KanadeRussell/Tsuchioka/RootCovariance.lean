import KanadeRussell.Tsuchioka.RootFock
import KanadeRussell.Tsuchioka.PrimitivePhases

/-! Coxeter covariance and root fusion for the concrete creation operators. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.FormalSeries

open PowerSeries

variable {A : Type*} [CommRing A] [Algebra ℚ A]

theorem rescale_exponential (d : A) (f : PowerSeries A) (hf : constantCoeff f = 0) :
    rescale d (exponential f) = exponential (rescale d f) := by
  have hr : constantCoeff (rescale d f) = 0 := by
    rw [← coeff_zero_eq_constantCoeff, coeff_rescale, pow_zero, one_mul,
      coeff_zero_eq_constantCoeff, hf]
  apply PowerSeries.ext
  intro n
  rw [coeff_rescale, coeff_exponential hf, coeff_exponential hr, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← map_pow, coeff_rescale]
  ring

end KanadeRussell.Tsuchioka.FormalSeries

namespace KanadeRussell.Tsuchioka.Fock

open PowerSeries
open RootData (Lattice simpleRoot coxeter rootWeight)

variable {K : Type*} [Field K] [CharZero K]

theorem mode_coprime_twelve (n : Mode) : n.val.Coprime 12 := by
  apply (ZMod.coprime_mod_iff_coprime n.val 12).mp
  rcases n.property with h | h | h | h
  all_goals rw [h]; decide

theorem mode_primitive_root (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) (n : Mode) :
    IsPrimitiveRoot (w ^ n.val) 12 :=
  (Coefficients.primitive_root w hw).pow_of_coprime n.val (mode_coprime_twelve n)

theorem mode_cyclotomic (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) (n : Mode) :
    (w ^ n.val) ^ 4 - (w ^ n.val) ^ 2 + 1 = 0 := by
  have h := (Polynomial.isRoot_cyclotomic_iff_charZero (by decide : 0 < 12)).mpr
    (mode_primitive_root w hw n)
  rw [Coefficients.cyclotomic_twelve] at h
  simpa [Polynomial.IsRoot.def] using h

theorem mode_inverse_cyclotomic (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) (n : Mode) :
    (w ^ (-(n.val : ℤ))) ^ 4 - (w ^ (-(n.val : ℤ))) ^ 2 + 1 = 0 := by
  have h := (Polynomial.isRoot_cyclotomic_iff_charZero (by decide : 0 < 12)).mpr
    (mode_primitive_root w hw n).inv
  rw [Coefficients.cyclotomic_twelve] at h
  simpa [Polynomial.IsRoot.def, zpow_neg, zpow_natCast] using h

/-- Every allowed Heisenberg mode has the required eigenvalue, at all orbit indices. -/
theorem rootCreationLog_iterate (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (β : Lattice) (j : Fin 3) (p : ℕ) :
    rootCreationLog w ((coxeter^[p]) β) j =
      rescale (MvPolynomial.C (w ^ (-(p : ℤ)))) (rootCreationLog w β j) := by
  apply PowerSeries.ext
  intro n
  rw [coeff_rescale]
  simp only [rootCreationLog, coeff_mk]
  by_cases hn : IsMode n
  · have ht := mode_inverse_cyclotomic w hw (⟨n, hn⟩ : Mode)
    have hp : (w ^ (-(n : ℤ))) ^ p = (w ^ (-(p : ℤ))) ^ n := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul]
      congr 1
      ring
    rw [RootData.rootWeight_iterate _ ht, hp]
    simp only [map_mul, map_pow, mul_assoc]
  · have hz : coeff n (creationLog (K := K) j) = 0 := by simp [creationLog, hn]
    simp [hz]

theorem rootCreation_iterate (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (β : Lattice) (j : Fin 3) (p : ℕ) :
    rootCreation w ((coxeter^[p]) β) j =
      rescale (MvPolynomial.C (w ^ (-(p : ℤ)))) (rootCreation w β j) := by
  change FormalSeries.exponential (rootCreationLog w ((coxeter^[p]) β) j) =
    rescale _ (FormalSeries.exponential (rootCreationLog w β j))
  rw [rootCreationLog_iterate w hw]
  exact (FormalSeries.rescale_exponential _ _ (constantCoeff_rootCreationLog w β j)).symm

theorem creation_fusion_four (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) (j : Fin 3) :
    rescale (MvPolynomial.C (w ^ (-4 : ℤ))) (creation (K := K) j) * creation j =
      rescale (MvPolynomial.C (w ^ (-2 : ℤ))) (creation j) := by
  have h := rootCreation_add w ((coxeter^[4]) (simpleRoot 0)) (simpleRoot 0) j
  rw [RootData.first_fusion_four, rootCreation_iterate w hw,
    rootCreation_iterate w hw, rootCreation_first] at h
  exact h.symm

theorem creation_fusion_eight (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) (j : Fin 3) :
    rescale (MvPolynomial.C (w ^ (-8 : ℤ))) (creation (K := K) j) * creation j =
      rescale (MvPolynomial.C (w ^ (-10 : ℤ))) (creation j) := by
  have h := rootCreation_add w ((coxeter^[8]) (simpleRoot 0)) (simpleRoot 0) j
  rw [RootData.first_fusion_eight, rootCreation_iterate w hw,
    rootCreation_iterate w hw, rootCreation_first] at h
  exact h.symm

theorem creation_fusion_five (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) (j : Fin 3) :
    rescale (MvPolynomial.C (w ^ (-5 : ℤ))) (creation (K := K) j) * creation j =
      rescale (MvPolynomial.C (w ^ (-9 : ℤ))) (rootCreation w (simpleRoot 1) j) := by
  have h := rootCreation_add w ((coxeter^[5]) (simpleRoot 0)) (simpleRoot 0) j
  rw [RootData.first_fusion_five, rootCreation_iterate w hw,
    rootCreation_iterate w hw, rootCreation_first] at h
  exact h.symm

theorem creation_fusion_seven (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) (j : Fin 3) :
    rescale (MvPolynomial.C (w ^ (-7 : ℤ))) (creation (K := K) j) * creation j =
      rescale (MvPolynomial.C (w ^ (-4 : ℤ))) (rootCreation w (simpleRoot 1) j) := by
  have h := rootCreation_add w ((coxeter^[7]) (simpleRoot 0)) (simpleRoot 0) j
  rw [RootData.first_fusion_seven, rootCreation_iterate w hw,
    rootCreation_iterate w hw, rootCreation_first] at h
  exact h.symm

end KanadeRussell.Tsuchioka.Fock
