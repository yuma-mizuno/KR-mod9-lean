import KanadeRussell.Representation.ScalarLambertTransform
import KanadeRussell.Representation.RootLambertPrincipalSpecialization
import KanadeRussell.Representation.RootLambertMomentTable

/-! Finite coefficient scalar reduction of the actual principal Lambert residual.
The scalar series in this file are defined by exact divisor sums. No vanishing
identity or identification with a separately defined analytic Lambert sum is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KanadeRussell.Representation
open AffineWeightLattice
variable {K : Type*} [Field K]

private def activeMoment : (ℕ → Fin 3 → ℕ → K) →ₗ[K] (ℕ → ℕ → K) where
  toFun f h k := ∑ r : Fin 3, if principalWeightSlotActive (positiveModeResidue h) r then f h r k else 0
  map_add' f g := by
    ext h k
    simp only [Pi.add_apply, ite_add_zero, Finset.sum_add_distrib]
  map_smul' c f := by
    ext h k
    simp only [Pi.smul_apply, smul_eq_mul, mul_ite, mul_zero, Finset.mul_sum, RingHom.id_apply]

private theorem ite_sum_zero {α : Type*} (s : Finset α) (p : Prop) [Decidable p] (f : α → K) :
    (if p then ∑ x ∈ s, f x else 0) = ∑ x ∈ s, if p then f x else 0 := by
  split_ifs <;> simp

private theorem degree_as_moment (i : Fin 3) :
    principalLambertDegree (K := K) i = scalarLambertTransform
      (activeMoment fun h r _ => (positiveModeOccupation h r i : K)) := by
  classical
  ext n
  rw [coeff_principalLambertDegree]
  simp only [scalarLambertTransform, LinearMap.coe_mk, AddHom.coe_mk, PowerSeries.coeff_mk]
  apply Finset.sum_congr rfl
  intro h hh
  simp_rw [ite_sum_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases he : (k+1)*(h+1)=n <;> simp [activeMoment, he]

private theorem derivative_as_moment (i j : Fin 3) :
    principalLambertDerivativeDegree (K := K) i j = scalarLambertTransform
      (activeMoment fun h r k => ((k+1 : ℕ) : K)*
        (positiveModeOccupation h r i : K)*(positiveModeOccupation h r j : K)) := by
  classical
  ext n
  rw [coeff_principalLambertDerivativeDegree]
  simp only [scalarLambertTransform, LinearMap.coe_mk, AddHom.coe_mk, PowerSeries.coeff_mk]
  apply Finset.sum_congr rfl
  intro h hh
  simp_rw [ite_sum_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases he : (k+1)*(h+1)=n <;> simp [activeMoment, he]

/-- The two finite-root projections, counted over all active modes. -/
def principalScalarT : PowerSeries K := scalarLambertTransform fun h _ =>
  (-(principalRootMomentA (positiveModeResidue h)) - principalRootMomentB (positiveModeResidue h) : ℤ)
def principalScalarU : PowerSeries K := scalarLambertTransform fun h _ =>
  (principalRootMomentA (positiveModeResidue h) - principalRootMomentB (positiveModeResidue h) : ℤ)
/-- Repetition-weighted quadratic root moment. -/
def principalScalarNorm : PowerSeries K := scalarLambertTransform fun h k =>
  ((k+1 : ℕ) : K) * (principalRootMomentNorm (positiveModeResidue h) : K)
/-- Height-weighted active-slot count. -/
def principalScalarHeight : PowerSeries K := scalarLambertTransform fun h _ =>
  ((h+1 : ℕ) : K) * (principalRootMomentCount (positiveModeResidue h) : K)

private theorem projectionA :
    principalLambertDegree (K := K) 0 - principalLambertDegree 2 =
      scalarLambertTransform (fun h _ => (principalRootMomentA (positiveModeResidue h) : K)) := by
  rw [degree_as_moment, degree_as_moment, ← map_sub, ← map_sub]
  congr 1
  ext h k
  change (∑ r : Fin 3, if principalWeightSlotActive (positiveModeResidue h) r then
    (positiveModeOccupation h r 0 : K) - (positiveModeOccupation h r 2 : K) else 0) = _
  simpa using congrArg (Int.castRingHom K) (principalRootMomentA_eq h)

private theorem projectionB :
    principalLambertDegree (K := K) 1 - 2 • principalLambertDegree 2 =
      scalarLambertTransform (fun h _ => (principalRootMomentB (positiveModeResidue h) : K)) := by
  rw [degree_as_moment, degree_as_moment, ← map_nsmul, ← map_sub, ← map_nsmul, ← map_sub]
  congr 1
  ext h k
  change (∑ r : Fin 3, if principalWeightSlotActive (positiveModeResidue h) r then
    (positiveModeOccupation h r 1 : K) - 2 • (positiveModeOccupation h r 2 : K) else 0) = _
  simp only [nsmul_eq_mul]
  simpa using congrArg (Int.castRingHom K) (principalRootMomentB_eq h)

 theorem principalScalarT_eq : principalScalarT (K := K) =
    -(principalLambertDegree 0) - principalLambertDegree 1 + 3 • principalLambertDegree 2 := by
  have h : principalScalarT (K := K) =
      -(principalLambertDegree 0-principalLambertDegree 2) -
        (principalLambertDegree 1-2 • principalLambertDegree 2) := by
    unfold principalScalarT
    rw [projectionA, projectionB, ← map_neg, ← map_sub]
    congr 1
    ext h k
    simp
  rw [h]
  simp only [nsmul_eq_mul]
  ring

 theorem principalScalarU_eq : principalScalarU (K := K) =
    principalLambertDegree 0-principalLambertDegree 1+principalLambertDegree 2 := by
  have h : principalScalarU (K := K) =
      (principalLambertDegree 0-principalLambertDegree 2) -
        (principalLambertDegree 1-2 • principalLambertDegree 2) := by
    unfold principalScalarU
    rw [projectionA, projectionB, ← map_sub]
    congr 1
    ext h k
    simp
  rw [h]
  simp only [nsmul_eq_mul]
  ring

theorem principalScalarNorm_eq : principalScalarNorm (K := K) =
    principalLambertDerivativeDegree 0 0 + principalLambertDerivativeDegree 1 1 +
      3 • principalLambertDerivativeDegree 2 2 - principalLambertDerivativeDegree 0 1 -
      3 • principalLambertDerivativeDegree 1 2 := by
  unfold principalScalarNorm
  simp only [derivative_as_moment, ← map_nsmul, ← map_add, ← map_sub]
  congr 1
  ext h k
  simp only [activeMoment, LinearMap.coe_mk, AddHom.coe_mk]
  rw [← principalRootMomentNorm_eq, Int.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  split_ifs <;> simp only [Int.cast_zero, mul_zero, Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.natCast_apply,
    nsmul_eq_mul, rootQuadratic_eq, Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_pow]
  all_goals ring

theorem principalScalarHeight_eq : principalScalarHeight (K := K) =
    principalLambertDegree 0 + principalLambertDegree 1 + principalLambertDegree 2 := by
  unfold principalScalarHeight
  simp only [degree_as_moment, ← map_add]
  congr 1
  ext h k
  simp only [activeMoment, LinearMap.coe_mk, AddHom.coe_mk]
  rw [← principalRootMomentCount_eq, Int.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  split_ifs with ha
  · simp only [Int.cast_one, mul_one, Pi.add_apply]
    have hd := congrArg (Int.castRingHom K) (positiveModeOccupation_degree h r)
    simpa [totalDegree, Fin.sum_univ_three] using hd.symm
  · simp

/-- The actual multivariate residual reduces to four exact scalar moment series. -/
theorem rootPrincipalSpecialization_residual_scalar :
    4 • rootPrincipalSpecialization (principalRootLambertResidual (K := K)) =
      (principalScalarT)^2 + 2 • principalScalarT + 3 • (principalScalarU)^2 -
        4 • principalScalarNorm + 6 • principalScalarHeight := by
  rw [rootPrincipalSpecialization_lambertResidual, principalScalarT_eq,
    principalScalarU_eq, principalScalarNorm_eq, principalScalarHeight_eq]
  simp only [nsmul_eq_mul]
  ring

end KanadeRussell.Representation
