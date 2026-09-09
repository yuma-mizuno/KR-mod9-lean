import KanadeRussell.Representation.PrincipalRootRecurrenceData
import KanadeRussell.Representation.RootMultiplicitySeries

/-! Nonnegative root exponents and coefficientwise finite Lambert series for
the actual counted positive-mode slots. These are explicit combinatorial
series, without any denominator or character assumption. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Representation
open AffineWeightLattice

def rootExponentDegree (e : Fin 3 →₀ ℕ) : ℕ := e.sum (fun _ m => m)

theorem rootExponentDegree_eq_sum (e : Fin 3 →₀ ℕ) : rootExponentDegree e = ∑ i : Fin 3, e i := by
  exact Finsupp.sum_fintype _ _ (fun _ => rfl)

@[simp] theorem rootExponentDegree_zero : rootExponentDegree 0 = 0 := rfl

theorem rootExponentDegree_mono {e f : Fin 3 →₀ ℕ} (h : e ≤ f) :
    rootExponentDegree e ≤ rootExponentDegree f := by
  simp only [rootExponentDegree_eq_sum]
  exact Finset.sum_le_sum (fun i _ => h i)

@[simp] theorem rootExponentDegree_nsmul (k : ℕ) (e : Fin 3 →₀ ℕ) :
    rootExponentDegree (k • e) = k * rootExponentDegree e := by
  simp [rootExponentDegree_eq_sum, Finsupp.smul_apply, Finset.mul_sum]

theorem rootExponentDegree_cast (e : Fin 3 →₀ ℕ) :
    (rootExponentDegree e : ℤ) = totalDegree (rootCoefficientsOfExponent e) := by
  simp [rootExponentDegree_eq_sum, totalDegree, rootCoefficientsOfExponent]

@[simp] theorem rootCoefficientsOfExponent_nsmul (k : ℕ) (e : Fin 3 →₀ ℕ) :
    rootCoefficientsOfExponent (k • e) = (k : ℤ) • rootCoefficientsOfExponent e := by
  ext i
  simp [rootCoefficientsOfExponent]

noncomputable def positiveModeExponent (n : ℕ) (r : Fin 3) : Fin 3 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (positiveModeOccupation n r i).toNat)

@[simp] theorem positiveModeExponent_apply (n : ℕ) (r i : Fin 3) :
    positiveModeExponent n r i = (positiveModeOccupation n r i).toNat := rfl

@[simp] theorem rootCoefficientsOfExponent_positiveModeExponent (n : ℕ) (r : Fin 3) :
    rootCoefficientsOfExponent (positiveModeExponent n r) = positiveModeOccupation n r := by
  ext i
  exact Int.toNat_of_nonneg (positiveModeOccupation_nonneg n r i)

@[simp] theorem positiveModeExponent_degree (n : ℕ) (r : Fin 3) :
    rootExponentDegree (positiveModeExponent n r) = n+1 := by
  have h := rootExponentDegree_cast (positiveModeExponent n r)
  rw [rootCoefficientsOfExponent_positiveModeExponent, positiveModeOccupation_degree] at h
  exact_mod_cast h

theorem positiveModeExponent_ne_zero (n : ℕ) (r : Fin 3) : positiveModeExponent n r ≠ 0 := by
  intro h
  have hd := positiveModeExponent_degree n r
  rw [h, rootExponentDegree_zero] at hd
  omega

theorem positiveModeExponent_multiple_le_bounds (e : Fin 3 →₀ ℕ)
    (n : ℕ) (r : Fin 3) (k : ℕ) (h : (k+1) • positiveModeExponent n r ≤ e) :
    n < rootExponentDegree e ∧ k < rootExponentDegree e+1 := by
  have hd := rootExponentDegree_mono h
  rw [rootExponentDegree_nsmul, positiveModeExponent_degree] at hd
  constructor <;> nlinarith

theorem positiveModeExponent_le_degree (e : Fin 3 →₀ ℕ)
    (n : ℕ) (r : Fin 3) (h : positiveModeExponent n r ≤ e) : n < rootExponentDegree e := by
  have hd := rootExponentDegree_mono h
  rw [positiveModeExponent_degree] at hd
  omega

theorem finite_positiveModeExponent_le (e : Fin 3 →₀ ℕ) :
    Set.Finite {p : ℕ × Fin 3 | positiveModeExponent p.1 p.2 ≤ e} := by
  have hsub : {p : ℕ × Fin 3 | positiveModeExponent p.1 p.2 ≤ e} ⊆
      (↑(Finset.range (rootExponentDegree e) ×ˢ (Finset.univ : Finset (Fin 3))) : Set (ℕ × Fin 3)) := by
    intro p hp
    simpa only [Finset.mem_coe, Finset.mem_product, Finset.mem_range, Finset.mem_univ, and_true] using
      positiveModeExponent_le_degree e p.1 p.2 hp
  exact (Finset.finite_toSet _).subset hsub

variable {K : Type*} [Field K]

noncomputable def principalRootLambertTerm (i : Fin 3) (e : Fin 3 →₀ ℕ)
    (n : ℕ) (r : Fin 3) (k : ℕ) : K :=
  if principalWeightSlotActive (positiveModeResidue n) r then
    if (k+1) • positiveModeExponent n r = e then (positiveModeOccupation n r i : K) else 0
  else 0

noncomputable def principalRootLambert (i : Fin 3) : MvPowerSeries (Fin 3) K :=
  fun e => ∑ n ∈ Finset.range (rootExponentDegree e), ∑ r : Fin 3,
    ∑ k ∈ Finset.range (rootExponentDegree e+1), principalRootLambertTerm i e n r k

@[simp] theorem coeff_principalRootLambert (i : Fin 3) (e : Fin 3 →₀ ℕ) :
    MvPowerSeries.coeff e (principalRootLambert (K := K) i) =
      ∑ n ∈ Finset.range (rootExponentDegree e), ∑ r : Fin 3,
        ∑ k ∈ Finset.range (rootExponentDegree e+1),
          if principalWeightSlotActive (positiveModeResidue n) r then
            if (k+1) • positiveModeExponent n r = e then (positiveModeOccupation n r i : K) else 0
          else 0 := rfl

theorem principalRootLambertTerm_eq_zero_of_large_n (i : Fin 3) (e : Fin 3 →₀ ℕ)
    (n : ℕ) (r : Fin 3) (k : ℕ) (hn : rootExponentDegree e ≤ n) :
    principalRootLambertTerm (K := K) i e n r k = 0 := by
  have hne : (k+1) • positiveModeExponent n r ≠ e := by
    intro heq
    have hb := positiveModeExponent_multiple_le_bounds e n r k heq.le
    omega
  simp [principalRootLambertTerm, hne]

theorem principalRootLambertTerm_eq_zero_of_large_k (i : Fin 3) (e : Fin 3 →₀ ℕ)
    (n : ℕ) (r : Fin 3) (k : ℕ) (hk : rootExponentDegree e+1 ≤ k) :
    principalRootLambertTerm (K := K) i e n r k = 0 := by
  have hne : (k+1) • positiveModeExponent n r ≠ e := by
    intro heq
    have hb := positiveModeExponent_multiple_le_bounds e n r k heq.le
    omega
  simp [principalRootLambertTerm, hne]

theorem coeff_principalRootLambert_cutoff (i : Fin 3) (e : Fin 3 →₀ ℕ)
    (N : ℕ) (hN : rootExponentDegree e ≤ N) :
    MvPowerSeries.coeff e (principalRootLambert (K := K) i) =
      ∑ n ∈ Finset.range N, ∑ r : Fin 3, ∑ k ∈ Finset.range (N+1),
        if principalWeightSlotActive (positiveModeResidue n) r then
          if (k+1) • positiveModeExponent n r = e then (positiveModeOccupation n r i : K) else 0
        else 0 := by
  classical
  change (∑ n ∈ Finset.range (rootExponentDegree e), ∑ r : Fin 3,
      ∑ k ∈ Finset.range (rootExponentDegree e+1), principalRootLambertTerm i e n r k) =
    ∑ n ∈ Finset.range N, ∑ r : Fin 3, ∑ k ∈ Finset.range (N+1), principalRootLambertTerm i e n r k
  calc
    _ = ∑ n ∈ Finset.range (rootExponentDegree e), ∑ r : Fin 3,
        ∑ k ∈ Finset.range (N+1), principalRootLambertTerm i e n r k := by
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_subset (Finset.range_mono (by omega : rootExponentDegree e+1 ≤ N+1))
      intro k hk hkn
      exact principalRootLambertTerm_eq_zero_of_large_k i e n r k (by simpa using hkn)
    _ = _ := by
      apply Finset.sum_subset (Finset.range_mono hN)
      intro n hn hnn
      apply Finset.sum_eq_zero
      intro r hr
      apply Finset.sum_eq_zero
      intro k hk
      exact principalRootLambertTerm_eq_zero_of_large_n i e n r k (by simpa using hnn)

@[simp] theorem constantCoeff_principalRootLambert (i : Fin 3) :
    MvPowerSeries.constantCoeff (principalRootLambert (K := K) i) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_principalRootLambert]
  simp only [rootExponentDegree_zero, Finset.range_zero, Finset.sum_empty]

end KanadeRussell.Representation
