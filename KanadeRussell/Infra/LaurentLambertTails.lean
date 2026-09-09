import KanadeRussell.Infra.LambertTailCoefficients
import KanadeRussell.Product.CubicScalarExtension

/-! Actual constant-unit Jacobi tails in the existing Laurent coefficient
extension, with the substitution q=p² made explicit. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open PowerSeries PowerSeries.WithPiTopology MvLaurentSeries
open scoped DiscreteUniformity
namespace KanadeRussell.Infra.LaurentLambertTails
open JacobiJets JacobiFirstJet KanadeRussell.Representation
open Product.CubicScalarExtension (L scalar p)
local instance : UniformSpace ℂ := ⊥

/-- Complex-coefficient extension of the same q=p² evaluation used in A₂-square. -/
noncomputable def eval2 : PowerSeries ℂ →+* L :=
  (LaurentSeries₁.ofPowerSeries ℂ).comp (expand 2 (by decide)).toRingHom

theorem eval2_continuous : Continuous eval2 := by
  have he : Continuous (expand 2 (by decide) (R := ℂ)) := by
    rw [continuous_iff_continuousAt]
    intro f
    rw [ContinuousAt, tendsto_iff_coeff_tendsto]
    intro n
    simp only [coeff_expand]
    split_ifs
    · exact (continuous_coeff ℂ (n/2)).continuousAt
    · exact tendsto_const_nhds
  exact LaurentSeries₁.coe_continuous.comp he

@[simp] theorem eval2_C (u : ℂ) : eval2 (PowerSeries.C u) = scalar u := by
  simp [eval2, Product.CubicScalarExtension.scalar, expand_C]

@[simp] theorem eval2_X : eval2 (X : PowerSeries ℂ) = (p : L)^2 := by
  change LaurentSeries₁.ofPowerSeries ℂ (expand 2 (by decide) X) = _
  rw [expand_X]
  calc
    _ = xPow () 2 := MvLaurentSeries.coe_X_pow () 2
    _ = (p : L)^2 := by
      change xPow () 2 = (xPow () 1 : L)^2
      rw [xPow_pow]
      norm_num

/-- On integral series this is exactly the existing faithful evaluation. -/
theorem eval2_map_int (f : PowerSeries ℤ) :
    eval2 (PowerSeries.map (Int.castRingHom ℂ) f) = Product.CubicScalarExtension.eval f := by
  rw [Product.CubicScalarExtension.eval_eq_expand]
  rfl

/-- The Laurent substitution is injective on the full complex power-series ring. -/
theorem eval2_injective : Function.Injective eval2 := by
  intro f g h
  change LaurentSeries₁.ofPowerSeries ℂ (expand 2 (by decide) f) =
    LaurentSeries₁.ofPowerSeries ℂ (expand 2 (by decide) g) at h
  have hh := LaurentSeries₁.coe_injective h
  apply PowerSeries.ext
  intro n
  simpa only [coeff_expand_mul] using congrArg (PowerSeries.coeff (2*n)) hh

/-- In particular, the original integral power-series object is faithfully embedded. -/
theorem eval2_map_int_injective :
    Function.Injective (fun f : PowerSeries ℤ => eval2 (PowerSeries.map (Int.castRingHom ℂ) f)) := by
  intro f g h
  apply Product.CubicScalarExtension.eval_injective
  simpa only [eval2_map_int] using h

noncomputable def constantUnit (v : ℂˣ) : Lˣ := Units.map scalar.toMonoidHom v

@[simp] theorem constantUnit_val (v : ℂˣ) : (constantUnit v : L) = scalar (v : ℂ) := rfl

@[simp] theorem constantUnit_inv_val (v : ℂˣ) : ((constantUnit v)⁻¹ : Lˣ) = constantUnit v⁻¹ := by
  simp [constantUnit]

theorem eval2_log_tail (u : ℂ) :
    eval2 (scalarLambertTransform (fun h _ => u^(h+1))) =
      logLambertTail (scalar u*(p : L)^2) ((p : L)^2) := by
  simpa using LambertTailCoefficients.map_logLambertTail_transform eval2 eval2_continuous u

theorem eval2_even_tail (u : ℂ) :
    eval2 (scalarLambertTransform (fun h _ => ((h+1 : ℕ) : ℂ)*u^(h+1))) =
      lambertTail (scalar u*(p : L)^2) ((p : L)^2) := by
  simpa using LambertTailCoefficients.map_lambertTail_transform eval2 eval2_continuous u

private theorem scalar_times_p_sq_nilpotent (u : ℂ) :
    IsTopologicallyNilpotent (scalar u*(p : L)^2) := by
  have h : IsTopologicallyNilpotent (PowerSeries.C u*(X : PowerSeries ℂ)) := by simp
  simpa only [map_mul, eval2_C, eval2_X] using h.map eval2_continuous

private theorem complement (v : ℂˣ) :
    ((p^2/constantUnit v : Lˣ) : L) = scalar ((v⁻¹ : ℂˣ) : ℂ)*(p : L)^2 := by
  simp only [div_eq_mul_inv, Units.val_mul, Units.val_pow_eq_pow_val,
    constantUnit_inv_val, constantUnit_val]
  ring

private theorem denominator_unit (v : ℂˣ) (hv : (v : ℂ) ≠ 1) :
    IsUnit (1-(v : ℂ)) := isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm hv))

/-- Exact resummation of the actual logarithmic Jacobi tail at a constant unit. -/
theorem jacobiLogarithmicLambert_constant (v : ℂˣ) (hv : (v : ℂ) ≠ 1) :
    jacobiLogarithmicLambert p (constantUnit v) =
      scalar (-(v : ℂ)*bInv (1-(v : ℂ))) +
        eval2 (scalarLambertTransform (fun h _ =>
          (((v⁻¹ : ℂˣ) : ℂ)^(h+1)-(v : ℂ)^(h+1)))) := by
  have hi := (denominator_unit v hv).map_bInv scalar
  have hf : scalarLambertTransform (fun h _ =>
      (((v⁻¹ : ℂˣ) : ℂ)^(h+1)-(v : ℂ)^(h+1))) =
      scalarLambertTransform (fun h _ => ((v⁻¹ : ℂˣ) : ℂ)^(h+1)) -
        scalarLambertTransform (fun h _ => (v : ℂ)^(h+1)) := map_sub _ _ _
  rw [hf, map_sub, eval2_log_tail, eval2_log_tail]
  simp only [jacobiLogarithmicLambert, constantUnit_val, complement,
    map_mul, map_neg, hi, map_sub, map_one]
  ring

/-- Exact resummation of the actual elliptic Lambert series at a constant unit. -/
theorem ellipticLambert_constant (v : ℂˣ) (hv : (v : ℂ) ≠ 1) :
    ellipticLambert p (constantUnit v) =
      scalar ((v : ℂ)*bInv (1-(v : ℂ))^2) +
        eval2 (scalarLambertTransform (fun h _ => ((h+1 : ℕ) : ℂ)*
          ((v : ℂ)^(h+1)+((v⁻¹ : ℂˣ) : ℂ)^(h+1)))) := by
  have hi := (denominator_unit v hv).map_bInv scalar
  have hs := JacobiParameter.lambertTail_split (scalar (v : ℂ)) ((p : L)^2)
    (Product.CubicScalarExtension.p_nilpotent.pow (by decide))
    (scalar_times_p_sq_nilpotent (v : ℂ))
  have hf : scalarLambertTransform (fun h _ => ((h+1 : ℕ) : ℂ)*
      ((v : ℂ)^(h+1)+((v⁻¹ : ℂˣ) : ℂ)^(h+1))) =
      scalarLambertTransform (fun h _ => ((h+1 : ℕ) : ℂ)*(v : ℂ)^(h+1)) +
        scalarLambertTransform (fun h _ => ((h+1 : ℕ) : ℂ)*((v⁻¹ : ℂˣ) : ℂ)^(h+1)) := by
    rw [← map_add]
    congr 1
    funext h k
    simp only [Pi.add_apply, mul_add]
  rw [hf, map_add, eval2_even_tail, eval2_even_tail]
  simp only [ellipticLambert, constantUnit_val, complement, hs,
    map_mul, map_pow, hi, map_sub, map_one]
  ring

/-- The normalized actual Jacobi first jet, not just its rational-tail definition. -/
theorem jacobi_normalized_first_constant (v : ℂˣ) (hv : (v : ℂ) ≠ 1) :
    coeff 1 (ThetaAddition.jacobi (unitC p) (unitC (constantUnit v)*oneAddX)) *
        bInv (ThetaAddition.jacobi p (constantUnit v)) =
      scalar (-(v : ℂ)*bInv (1-(v : ℂ))) +
        eval2 (scalarLambertTransform (fun h _ =>
          (((v⁻¹ : ℂˣ) : ℂ)^(h+1)-(v : ℂ)^(h+1)))) := by
  have hu : IsUnit (1-(constantUnit v : L)) := by
    simpa only [map_sub, map_one, constantUnit_val] using (denominator_unit v hv).map scalar
  have hnil : IsTopologicallyNilpotent ((constantUnit v : L)*(p : L)^2) :=
    scalar_times_p_sq_nilpotent (v : ℂ)
  have hcomp : IsTopologicallyNilpotent (((p^2/constantUnit v : Lˣ) : L)) := by
    rw [complement]
    exact scalar_times_p_sq_nilpotent ((v⁻¹ : ℂˣ) : ℂ)
  rw [jacobi_normalized_first_of_shift p (constantUnit v)
    Product.CubicScalarExtension.p_nilpotent hnil hu hcomp]
  exact jacobiLogarithmicLambert_constant v hv

/-- The centered first jet has exactly the constant and raw odd Fourier weights. -/
theorem jacobi_centered_first_constant (v : ℂˣ) (hv : (v : ℂ) ≠ 1) :
    coeff 1 (ThetaAddition.jacobi (unitC p) (unitC (constantUnit v)*oneAddX)) *
        bInv (ThetaAddition.jacobi p (constantUnit v)) - scalar (1/2) =
      scalar (-(v : ℂ)*bInv (1-(v : ℂ))-1/2) +
        eval2 (scalarLambertTransform (fun h _ =>
          (((v⁻¹ : ℂˣ) : ℂ)^(h+1)-(v : ℂ)^(h+1)))) := by
  rw [jacobi_normalized_first_constant v hv, map_sub]
  ring

end KanadeRussell.Infra.LaurentLambertTails
