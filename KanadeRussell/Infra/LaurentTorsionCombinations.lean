import KanadeRussell.Infra.LaurentLambertTails
import KanadeRussell.Infra.TwelfthRootJacobiArguments
import KanadeRussell.Representation.RootTorsionMomentBridge

/-! Exact twelfth-root combinations of the actual centered Jacobi first jets
and elliptic Lambert functions in the faithful q=p² Laurent embedding. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open PowerSeries PowerSeries.WithPiTopology
open scoped DiscreteUniformity
namespace KanadeRussell.Infra.LaurentTorsionCombinations
open JacobiJets JacobiFirstJet LaurentLambertTails TwelfthRootTorsionWeights
open KanadeRussell.Representation
open Product.CubicScalarExtension (L scalar p)
local instance : UniformSpace ℂ := ⊥

noncomputable def centeredZ (w : ℂˣ) (j : ℕ) : L :=
  jacobiLogarithmicLambert p (constantUnit (w^j))-scalar (1/2)

noncomputable def ellipticE (w : ℂˣ) (j : ℕ) : L :=
  ellipticLambert p (constantUnit (w^j))

noncomputable def centeredP (w : ℂˣ) (j : ℕ) : L :=
  ellipticE w j+scalar (1/12)-2*lambertTail ((p : L)^2) ((p : L)^2)

private theorem power_ne_one (w : ℂˣ) (hw : (w : ℂ)^4-(w : ℂ)^2+1=0)
    (j : Fin 6) : ((w^(j.val+1) : ℂˣ) : ℂ) ≠ 1 := by
  exact TwelfthRootJacobiArguments.torsion_pow_ne_one (w : ℂ) hw (j.val+1)
    (by omega) (by omega)

/-- The centered rational-tail expression is the normalized actual Jacobi jet. -/
theorem centeredZ_eq_normalized_first (w : ℂˣ) (hw : (w : ℂ)^4-(w : ℂ)^2+1=0)
    (j : Fin 6) :
    centeredZ w (j.val+1) =
      PowerSeries.coeff 1 (ThetaAddition.jacobi (unitC p)
        (unitC (constantUnit (w^(j.val+1)))*oneAddX)) *
          bInv (ThetaAddition.jacobi p (constantUnit (w^(j.val+1))))-scalar (1/2) := by
  rw [centeredZ, LaurentLambertTails.jacobi_normalized_first_constant _ (power_ne_one w hw j),
    LaurentLambertTails.jacobiLogarithmicLambert_constant _ (power_ne_one w hw j)]

private theorem odd_function (w : ℂˣ) (hw : (w : ℂ)^4-(w : ℂ)^2+1=0) (j : Fin 6) :
    (fun h (_ : ℕ) => (((w^(j.val+1))⁻¹ : ℂˣ) : ℂ)^(h+1)-
      ((w^(j.val+1) : ℂˣ) : ℂ)^(h+1)) =
      (fun h (_ : ℕ) => oddFourier (w : ℂ) (j.val+1) (h+1)) := by
  funext h k
  rw [oddFourier_eq_zpow (w : ℂ) hw (j.val+1) (h+1) (by omega)]
  simp only [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, zpow_neg, zpow_natCast, inv_pow]

private theorem even_function (w : ℂˣ) (hw : (w : ℂ)^4-(w : ℂ)^2+1=0) (j : Fin 6) :
    (fun h (_ : ℕ) => ((h+1 : ℕ) : ℂ)*
      (((w^(j.val+1) : ℂˣ) : ℂ)^(h+1)+(((w^(j.val+1))⁻¹ : ℂˣ) : ℂ)^(h+1))) =
      (fun h (_ : ℕ) => ((h+1 : ℕ) : ℂ)*evenFourier (w : ℂ) (j.val+1) (h+1)) := by
  funext h k
  rw [evenFourier_eq_zpow (w : ℂ) hw (j.val+1) (h+1) (by omega)]
  simp only [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, zpow_neg, zpow_natCast, inv_pow]
  ring

theorem centeredZ_fourier (w : ℂˣ) (hw : (w : ℂ)^4-(w : ℂ)^2+1=0) (j : Fin 6) :
    centeredZ w (j.val+1) = scalar (firstConstant (w : ℂ) j) +
      eval2 (scalarLambertTransform (fun h _ => oddFourier (w : ℂ) (j.val+1) (h+1))) := by
  rw [centeredZ, jacobiLogarithmicLambert_constant _ (power_ne_one w hw j), odd_function w hw j]
  simp only [firstConstant, Units.val_pow_eq_pow_val, map_sub]
  ring

theorem ellipticE_fourier (w : ℂˣ) (hw : (w : ℂ)^4-(w : ℂ)^2+1=0) (j : Fin 6) :
    ellipticE w (j.val+1) = scalar (evenConstant (w : ℂ) j) +
      eval2 (scalarLambertTransform (fun h _ => ((h+1 : ℕ) : ℂ)*
        evenFourier (w : ℂ) (j.val+1) (h+1))) := by
  rw [ellipticE, ellipticLambert_constant _ (power_ne_one w hw j), even_function w hw j]
  simp only [evenConstant, Units.val_pow_eq_pow_val]

private theorem eval2_smul (a : ℂ) (f : PowerSeries ℂ) :
    eval2 (a • f) = scalar a*eval2 f := by
  rw [PowerSeries.smul_eq_C_mul, map_mul, eval2_C]

theorem centeredZ_T (w : ℂˣ) (hw : (w : ℂ)^4-(w : ℂ)^2+1=0) :
    centeredZ w 1+centeredZ w 5 = -2*scalar ((w : ℂ)^3)*(1+eval2 principalScalarT) := by
  have h1 := centeredZ_fourier w hw 0
  have h5 := centeredZ_fourier w hw 4
  norm_num at h1 h5
  rw [h1,h5]
  have ht := congrArg eval2 (scalarLambertTransform_torsion_T (w : ℂ) hw)
  have hf : scalarLambertTransform (fun h (_ : ℕ) => oddFourier (w : ℂ) 1 (h+1)+
      oddFourier (w : ℂ) 5 (h+1)) =
      scalarLambertTransform (fun h _ => oddFourier (w : ℂ) 1 (h+1))+
        scalarLambertTransform (fun h _ => oddFourier (w : ℂ) 5 (h+1)) := map_add _ _ _
  rw [hf,map_add,eval2_smul] at ht
  have hc := congrArg scalar (firstConstant_T (w : ℂ) hw)
  simp only [map_add,map_mul,map_neg,map_ofNat] at hc ht
  linear_combination hc+ht

theorem centeredZ_U (w : ℂˣ) (hw : (w : ℂ)^4-(w : ℂ)^2+1=0) :
    -centeredZ w 1+2*centeredZ w 2+centeredZ w 5 =
      -2*scalar (2*(w : ℂ)^2-1)*eval2 principalScalarU := by
  have h1 := centeredZ_fourier w hw 0
  have h2 := centeredZ_fourier w hw 1
  have h5 := centeredZ_fourier w hw 4
  norm_num at h1 h2 h5
  rw [h1,h2,h5]
  have ht := congrArg eval2 (scalarLambertTransform_torsion_U (w : ℂ) hw)
  have hf : scalarLambertTransform (fun h (_ : ℕ) => -oddFourier (w : ℂ) 1 (h+1)+
      2*oddFourier (w : ℂ) 2 (h+1)+oddFourier (w : ℂ) 5 (h+1)) =
      -scalarLambertTransform (fun h _ => oddFourier (w : ℂ) 1 (h+1))+
        2 • scalarLambertTransform (fun h _ => oddFourier (w : ℂ) 2 (h+1))+
          scalarLambertTransform (fun h _ => oddFourier (w : ℂ) 5 (h+1)) := by
    rw [← map_neg, ← map_nsmul, ← map_add, ← map_add]
    congr 1
    funext h k
    simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply]
    simp only [nsmul_eq_mul, Nat.cast_ofNat]
  rw [hf,map_add,map_add,map_neg,map_nsmul,eval2_smul] at ht
  have hc := congrArg scalar (firstConstant_U (w : ℂ) hw)
  simp only [map_add,map_mul,map_neg,map_ofNat,map_zero, nsmul_eq_mul, Nat.cast_ofNat] at hc ht
  linear_combination hc+ht

/-- The central Lambert tail is the evaluation of the original integral L₁ series. -/
theorem central_lambertTail :
    lambertTail ((p : L)^2) ((p : L)^2) =
      eval2 (PowerSeries.map (Int.castRingHom ℂ) (Product.lambert 1)) := by
  have ht := eval2_even_tail (1 : ℂ)
  have hh := scalarLambertTransform_height_divisor (K := ℂ) 1 (by decide)
  simp only [one_dvd, if_true, Nat.cast_one, one_smul] at hh
  simp only [one_pow, mul_one, map_one, one_mul] at ht
  rw [hh] at ht
  exact ht.symm

/-- The weighted actual elliptic Lambert combination, with all initial constants retained. -/
theorem ellipticE_combination (w : ℂˣ) (hw : (w : ℂ)^4-(w : ℂ)^2+1=0) :
    ellipticE w 1+9*ellipticE w 2-2*ellipticE w 3+
      ellipticE w 4+ellipticE w 5+3*ellipticE w 6 =
      scalar (-157/12)+eval2 (PowerSeries.map (Int.castRingHom ℂ)
        (2 • Product.lambert 1-72 • Product.lambert 3-48 • Product.lambert 4+
          288 • Product.lambert 6+144 • Product.lambert 12)) := by
  have h1 := ellipticE_fourier w hw 0
  have h2 := ellipticE_fourier w hw 1
  have h3 := ellipticE_fourier w hw 2
  have h4 := ellipticE_fourier w hw 3
  have h5 := ellipticE_fourier w hw 4
  have h6 := ellipticE_fourier w hw 5
  norm_num at h1 h2 h3 h4 h5 h6
  rw [h1,h2,h3,h4,h5,h6]
  have ht := congrArg eval2 (scalarLambertTransform_torsion_E (w : ℂ) hw)
  have hf : scalarLambertTransform (fun h (_ : ℕ) => ((h+1 : ℕ) : ℂ)*
      (evenFourier (w : ℂ) 1 (h+1)+9*evenFourier (w : ℂ) 2 (h+1)-
        2*evenFourier (w : ℂ) 3 (h+1)+evenFourier (w : ℂ) 4 (h+1)+
          evenFourier (w : ℂ) 5 (h+1)+3*evenFourier (w : ℂ) 6 (h+1))) =
      scalarLambertTransform (fun h _ => ((h+1 : ℕ) : ℂ)*evenFourier (w : ℂ) 1 (h+1))+
        9 • scalarLambertTransform (fun h _ => ((h+1 : ℕ) : ℂ)*evenFourier (w : ℂ) 2 (h+1))-
        2 • scalarLambertTransform (fun h _ => ((h+1 : ℕ) : ℂ)*evenFourier (w : ℂ) 3 (h+1))+
          scalarLambertTransform (fun h _ => ((h+1 : ℕ) : ℂ)*evenFourier (w : ℂ) 4 (h+1))+
          scalarLambertTransform (fun h _ => ((h+1 : ℕ) : ℂ)*evenFourier (w : ℂ) 5 (h+1))+
        3 • scalarLambertTransform (fun h _ => ((h+1 : ℕ) : ℂ)*evenFourier (w : ℂ) 6 (h+1)) := by
    simp only [← map_nsmul, ← map_add, ← map_sub]
    congr 1
    funext h k
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
    simp only [nsmul_eq_mul, Nat.cast_ofNat]
    ring
  rw [hf] at ht
  have hc := congrArg scalar (evenConstant_combination (w : ℂ) hw)
  simp only [map_add,map_sub,map_mul,map_ofNat,nsmul_eq_mul,Nat.cast_ofNat,
    Nat.cast_add,Nat.cast_one] at hc ht ⊢
  linear_combination hc+ht

end KanadeRussell.Infra.LaurentTorsionCombinations
