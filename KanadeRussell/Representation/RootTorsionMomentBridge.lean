import KanadeRussell.Infra.TwelfthRootTorsionWeights
import KanadeRussell.Representation.RootLambertScalarIdentity
import KanadeRussell.Representation.RootLambertDivisorBridge

/-! Exact identification of the torsion Fourier traces with the scalar
moments of the original root denominator. All coefficient indices are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Representation
open Infra.TwelfthRootTorsionWeights

theorem tWeight_rootMoment (n : ℕ) :
    tWeight ⟨(n+1)%12, Nat.mod_lt _ (Nat.zero_lt_succ 11)⟩ =
      -principalRootMomentA (positiveModeResidue n)-principalRootMomentB (positiveModeResidue n) := by
  have hi : (n+1)%12 = (n%12+1)%12 := by omega
  simp only [hi]
  exact (by decide : ∀ s : Fin 12,
    tWeight ⟨(s.val+1)%12, Nat.mod_lt _ (Nat.zero_lt_succ 11)⟩ = -principalRootMomentA s-principalRootMomentB s)
      (positiveModeResidue n)

theorem uWeight_rootMoment (n : ℕ) :
    uWeight ⟨(n+1)%12, Nat.mod_lt _ (Nat.zero_lt_succ 11)⟩ =
      principalRootMomentA (positiveModeResidue n)-principalRootMomentB (positiveModeResidue n) := by
  have hi : (n+1)%12 = (n%12+1)%12 := by omega
  simp only [hi]
  exact (by decide : ∀ s : Fin 12,
    uWeight ⟨(s.val+1)%12, Nat.mod_lt _ (Nat.zero_lt_succ 11)⟩ = principalRootMomentA s-principalRootMomentB s)
      (positiveModeResidue n)

variable {K : Type*} [Field K]

theorem scalarLambertTransform_torsion_T (w : K) (hw : w^4-w^2+1=0) :
    scalarLambertTransform (fun h _ => oddFourier w 1 (h+1)+oddFourier w 5 (h+1)) =
      (-2*w^3) • principalScalarT := by
  unfold principalScalarT
  rw [← map_smul]
  congr 1
  ext h k
  simp only [Pi.smul_apply, smul_eq_mul, Fourier_T w hw, tWeight_rootMoment]

theorem scalarLambertTransform_torsion_U (w : K) (hw : w^4-w^2+1=0) :
    scalarLambertTransform (fun h _ =>
      -oddFourier w 1 (h+1)+2*oddFourier w 2 (h+1)+oddFourier w 5 (h+1)) =
      (-2*(2*w^2-1)) • principalScalarU := by
  unfold principalScalarU
  rw [← map_smul]
  congr 1
  ext h k
  simp only [Pi.smul_apply, smul_eq_mul, Fourier_U w hw, uWeight_rootMoment]

theorem scalarLambertTransform_torsion_evenWeight :
    scalarLambertTransform (fun h _ => ((h+1 : ℕ) : K)*
      (eWeight ⟨(h+1)%12, Nat.mod_lt _ (Nat.zero_lt_succ 11)⟩ : K)) =
      PowerSeries.map (Int.castRingHom K)
        (2 • Product.lambert 1 - 72 • Product.lambert 3 - 48 • Product.lambert 4 +
          288 • Product.lambert 6 + 144 • Product.lambert 12) := by
  have h : scalarLambertTransform (fun h _ => ((h+1 : ℕ) : K)*
      (eWeight ⟨(h+1)%12, Nat.mod_lt _ (Nat.zero_lt_succ 11)⟩ : K)) =
      2 • scalarLambertTransform (fun h _ => if 1 ∣ h+1 then ((h+1 : ℕ) : K) else 0) -
        24 • scalarLambertTransform (fun h _ => if 3 ∣ h+1 then ((h+1 : ℕ) : K) else 0) -
        12 • scalarLambertTransform (fun h _ => if 4 ∣ h+1 then ((h+1 : ℕ) : K) else 0) +
        48 • scalarLambertTransform (fun h _ => if 6 ∣ h+1 then ((h+1 : ℕ) : K) else 0) +
        12 • scalarLambertTransform (fun h _ => if 12 ∣ h+1 then ((h+1 : ℕ) : K) else 0) := by
    simp only [← map_nsmul, ← map_add, ← map_sub]
    congr 1
    ext h k
    simp [eWeight_dvd, mul_sub, mul_add, mul_ite]
    simp only [add_mul, one_mul, mul_comm]
  rw [h, scalarLambertTransform_height_divisor 1 (by decide),
    scalarLambertTransform_height_divisor 3 (by decide),
    scalarLambertTransform_height_divisor 4 (by decide),
    scalarLambertTransform_height_divisor 6 (by decide),
    scalarLambertTransform_height_divisor 12 (by decide)]
  simp only [map_add, map_sub, map_nsmul, Nat.cast_smul_eq_nsmul, smul_smul]
  norm_num

theorem scalarLambertTransform_torsion_E (w : K) (hw : w^4-w^2+1=0) :
    scalarLambertTransform (fun h _ => ((h+1 : ℕ) : K)*
      (evenFourier w 1 (h+1)+9*evenFourier w 2 (h+1)-2*evenFourier w 3 (h+1)+
        evenFourier w 4 (h+1)+evenFourier w 5 (h+1)+3*evenFourier w 6 (h+1))) =
      PowerSeries.map (Int.castRingHom K)
        (2 • Product.lambert 1 - 72 • Product.lambert 3 - 48 • Product.lambert 4 +
          288 • Product.lambert 6 + 144 • Product.lambert 12) := by
  simp only [Fourier_E w hw]
  exact scalarLambertTransform_torsion_evenWeight

end KanadeRussell.Representation
