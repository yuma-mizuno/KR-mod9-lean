import KanadeRussell.Representation.RootMultiplicitySeries

/-! Coefficientwise Euler differentiation of multivariate Euler products. -/
set_option autoImplicit false
namespace KanadeRussell.Representation
variable {K : Type*} [Field K]

theorem rootEulerOperator_mul (i : Fin 3) (f g : MvPowerSeries (Fin 3) K) :
    rootEulerOperator i (f*g) = (rootEulerOperator i f)*g + f*(rootEulerOperator i g) := by
  ext e
  simp only [coeff_rootEulerOperator, map_add, MvPowerSeries.coeff_mul,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have he := Finset.mem_antidiagonal.mp hp
  rw [← he]
  simp only [Finsupp.add_apply, Nat.cast_add]
  ring

@[simp] theorem rootEulerOperator_one (i : Fin 3) :
    rootEulerOperator i (1 : MvPowerSeries (Fin 3) K) = 0 := by
  ext e
  by_cases he : e = 0
  · subst e; simp
  · simp [MvPowerSeries.coeff_one, he]

@[simp] theorem rootEulerOperator_monomial (i : Fin 3) (e : Fin 3 →₀ ℕ) (a : K) :
    rootEulerOperator i (MvPowerSeries.monomial e a) =
      (e i : K) • MvPowerSeries.monomial e a := by
  ext f
  by_cases h : e = f
  · subst f; simp
  · simp [MvPowerSeries.coeff_monomial, Ne.symm h]

/-- Finite Leibniz rule, with one factor differentiated at a time. -/
theorem rootEulerOperator_prod {ι : Type*} [DecidableEq ι]
    (i : Fin 3) (s : Finset ι) (f : ι → MvPowerSeries (Fin 3) K) :
    rootEulerOperator i (∏ a ∈ s, f a) =
      ∑ a ∈ s, (rootEulerOperator i (f a)) * ∏ b ∈ s.erase a, f b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, rootEulerOperator_mul, ih, Finset.sum_insert ha]
    simp only [Finset.erase_insert ha]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro b hb
    have hba : b ≠ a := ne_of_mem_of_not_mem hb ha
    rw [Finset.erase_insert_of_ne hba.symm, Finset.prod_insert]
    · ring
    · simp [ha]

/-- Equality of all coefficients in the finite lower box below an exponent. -/
def RootCoeffAgree (e : Fin 3 →₀ ℕ) (f g : MvPowerSeries (Fin 3) K) : Prop :=
  ∀ d ≤ e, MvPowerSeries.coeff d f = MvPowerSeries.coeff d g

namespace RootCoeffAgree
variable {e : Fin 3 →₀ ℕ} {f g h f' g' : MvPowerSeries (Fin 3) K}
theorem refl (f : MvPowerSeries (Fin 3) K) : RootCoeffAgree e f f := fun _ _ => rfl
theorem trans (hfg : RootCoeffAgree e f g) (hgh : RootCoeffAgree e g h) :
    RootCoeffAgree e f h := fun d hd => (hfg d hd).trans (hgh d hd)
theorem symm (hfg : RootCoeffAgree e f g) : RootCoeffAgree e g f :=
  fun d hd => (hfg d hd).symm
theorem add (hf : RootCoeffAgree e f f') (hg : RootCoeffAgree e g g') :
    RootCoeffAgree e (f+g) (f'+g') := by
  intro d hd
  simp only [map_add, hf d hd, hg d hd]
theorem neg (hf : RootCoeffAgree e f f') : RootCoeffAgree e (-f) (-f') := by
  intro d hd
  simp only [map_neg, hf d hd]
theorem smul (hf : RootCoeffAgree e f f') (a : K) :
    RootCoeffAgree e (a • f) (a • f') := by
  intro d hd
  simp only [map_smul, hf d hd]
theorem mul (hf : RootCoeffAgree e f f') (hg : RootCoeffAgree e g g') :
    RootCoeffAgree e (f*g) (f'*g') := by
  intro d hd
  simp only [MvPowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have hp' := Finset.mem_antidiagonal.mp hp
  have h1 : p.1 ≤ e := (le_add_right (le_refl p.1)).trans (le_of_eq hp' |>.trans hd)
  have h2 : p.2 ≤ e := (le_add_left (le_refl p.2)).trans (le_of_eq hp' |>.trans hd)
  rw [hf _ h1, hg _ h2]
theorem euler (hf : RootCoeffAgree e f f') (i : Fin 3) :
    RootCoeffAgree e (rootEulerOperator i f) (rootEulerOperator i f') := by
  intro d hd
  simp only [coeff_rootEulerOperator, hf d hd]
end RootCoeffAgree

/-- A monomial outside the lower box cannot affect any coefficient in that box. -/
theorem rootCoeffAgree_monomial_zero (e a : Fin 3 →₀ ℕ) (h : ¬a ≤ e) (c : K) :
    RootCoeffAgree e (MvPowerSeries.monomial a c) 0 := by
  intro d hd
  have hda : d ≠ a := fun he => h (he ▸ hd)
  simp [MvPowerSeries.coeff_monomial, hda]

/-- The logarithmic derivative identity needs only hold in the box being computed. -/
theorem rootEulerOperator_prod_local {ι : Type*} [DecidableEq ι]
    (i : Fin 3) (e : Fin 3 →₀ ℕ) (s : Finset ι)
    (f L : ι → MvPowerSeries (Fin 3) K)
    (h : ∀ a ∈ s, RootCoeffAgree e (rootEulerOperator i (f a)) (-(f a * L a))) :
    RootCoeffAgree e (rootEulerOperator i (∏ a ∈ s, f a))
      (-(∏ a ∈ s, f a) * ∑ a ∈ s, L a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [RootCoeffAgree]
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, rootEulerOperator_mul, Finset.sum_insert ha]
    have h1 := (h a (Finset.mem_insert_self a s)).mul (RootCoeffAgree.refl (e := e) (∏ b ∈ s, f b))
    have h2 := (RootCoeffAgree.refl (e := e) (f a)).mul
      (ih (fun b hb => h b (Finset.mem_insert_of_mem hb)))
    have hh := h1.add h2
    convert hh using 1; ring

/-- Finite geometric sum in precisely the positive-power convention used by Lambert series. -/
theorem root_positive_geom (x : MvPowerSeries (Fin 3) K) (N : ℕ) :
    (1-x) * (∑ k ∈ Finset.range N, x^(k+1)) = x-x^(N+1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    simp only [pow_succ]
    ring

/-- The finite geometric logarithmic derivative is exact below its remainder monomial. -/
theorem rootEulerOperator_factor_local (i : Fin 3) (e a : Fin 3 →₀ ℕ) (N : ℕ)
    (hN : ¬(N+1) • a ≤ e) :
    RootCoeffAgree e (rootEulerOperator i (1-MvPowerSeries.monomial a (1 : K)))
      (-((1-MvPowerSeries.monomial a (1 : K)) *
        ((a i : K) • ∑ k ∈ Finset.range N, MvPowerSeries.monomial a (1 : K)^(k+1)))) := by
  rw [map_sub, rootEulerOperator_one, zero_sub, rootEulerOperator_monomial,
    mul_smul_comm, root_positive_geom, smul_sub]
  have hz := (rootCoeffAgree_monomial_zero e ((N+1) • a) hN (1 : K)).smul (a i : K)
  have hp : (MvPowerSeries.monomial a (1 : K))^(N+1) =
      MvPowerSeries.monomial ((N+1) • a) (1 : K) := by
    simp [MvPowerSeries.monomial_pow]
  rw [hp]
  intro d hd
  have hh := hz d hd
  simp only [map_smul, map_zero] at hh
  simp only [map_neg, map_sub, map_smul, hh, smul_zero, sub_zero]

theorem RootCoeffAgree.prod {ι : Type*} (s : Finset ι)
    {e : Fin 3 →₀ ℕ} {f g : ι → MvPowerSeries (Fin 3) K}
    (h : ∀ a ∈ s, RootCoeffAgree e (f a) (g a)) :
    RootCoeffAgree e (∏ a ∈ s, f a) (∏ a ∈ s, g a) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact RootCoeffAgree.refl _
  | @insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul
      (ih (fun b hb => h b (Finset.mem_insert_of_mem hb)))
end KanadeRussell.Representation
