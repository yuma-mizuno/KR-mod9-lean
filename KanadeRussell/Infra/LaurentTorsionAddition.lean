import KanadeRussell.Infra.LaurentTorsionCombinations
import KanadeRussell.Infra.LaurentLambertTails
import KanadeRussell.Infra.JacobiFiniteOrderArguments
import KanadeRussell.Infra.JacobiFrobeniusStickelberger
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
open PowerSeries PowerSeries.WithPiTopology MvLaurentSeries
open scoped DiscreteUniformity
namespace KanadeRussell.Infra.LaurentTorsionAddition
open LaurentLambertTails JacobiFirstJet JacobiJets JacobiFiniteOrderArguments
open Product.CubicScalarExtension (L scalar p)
local instance : UniformSpace ℂ := ⊥

theorem torsion_argument (w : ℂˣ) (hw : (w:ℂ)^4-(w:ℂ)^2+1=0)
    (j : ℕ) (hj : 1 ≤ j) (hj12 : j < 12) :
    IsTopologicallyNilpotent ((constantUnit (w^j):L)*(p:L)^2) ∧
    IsUnit (1-(constantUnit (w^j):L)) ∧
    IsTopologicallyNilpotent ((p^2/constantUnit (w^j):Lˣ):L) := by
  have hw12 : w^12=1 := by
    apply Units.ext
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using
      TwelfthRootTorsionWeights.pow_twelve (w:ℂ) hw
  have ho : (constantUnit (w^j))^12=1 := by
    have hh : (w^j)^12=1 := by
      rw [← pow_mul, Nat.mul_comm j 12, pow_mul, hw12, one_pow]
    simpa only [constantUnit, map_pow, map_one] using congrArg (Units.map scalar.toMonoidHom) hh
  obtain ⟨hplus,hminus⟩ := shifted_tails_nilpotent p (constantUnit (w^j))
    (by decide : 12 ≠ 0) ho Product.CubicScalarExtension.p_nilpotent
  refine ⟨hplus,?_,hminus⟩
  simpa only [constantUnit_val, Units.val_pow_eq_pow_val, map_pow] using
    TwelfthRootJacobiArguments.mapped_torsion_denominator_isUnit scalar (w:ℂ) hw j hj hj12

theorem frobenius_stickelberger_pair (w a : ℂˣ)
    (hw : (w:ℂ)^4-(w:ℂ)^2+1=0) (ha : a^2=w)
    (j k : ℕ) (hj : 1 ≤ j) (hk : 1 ≤ k) (hjk : j+k < 12) :
    (1-2*(jacobiLogarithmicLambert p (constantUnit (w^j))+
      jacobiLogarithmicLambert p (constantUnit (w^k))-
      jacobiLogarithmicLambert p (constantUnit (w^(j+k)))))^2 =
      1-24*lambertTail ((p:L)^2) ((p:L)^2)+
      4*(ellipticLambert p (constantUnit (w^j))+
        ellipticLambert p (constantUnit (w^k))+
        ellipticLambert p (constantUnit (w^(j+k)))) := by
  have haj : IsUnit (ThetaAddition.jacobi p (constantUnit (a^j))) := by
    apply isUnit_jacobi_mapped_squareRoot scalar (w:ℂ) (a:ℂ) hw _ j hj (by omega)
      p (constantUnit (a^j)) _ Product.CubicScalarExtension.p_nilpotent
    · simpa only [Units.val_pow_eq_pow_val] using congrArg Units.val ha
    · simp only [constantUnit_val, Units.val_pow_eq_pow_val, map_pow]
  have e1 : (constantUnit (a^j))^2 = constantUnit (w^j) := by
    have hh : (a^j)^2=w^j := by rw [← pow_mul, Nat.mul_comm j 2, pow_mul, ha]
    simpa only [constantUnit, map_pow] using congrArg (Units.map scalar.toMonoidHom) hh
  have e2 : constantUnit (w^j)*constantUnit (w^k)=constantUnit (w^(j+k)) := by
    simp only [constantUnit, pow_add, map_mul]
  have h0 := torsion_argument w hw j hj (by omega)
  have h1 := torsion_argument w hw k hk (by omega)
  have h2 := torsion_argument w hw (j+k) (by omega) hjk
  obtain ⟨h0a,h0b,h0c⟩ := h0
  obtain ⟨h1a,h1b,h1c⟩ := h1
  obtain ⟨h2a,h2b,h2c⟩ := h2
  have he := JacobiFrobeniusStickelberger.frobenius_stickelberger p
    (constantUnit (a^j)) (constantUnit (w^k)) Product.CubicScalarExtension.p_nilpotent haj
  simp only [e1,e2] at he
  apply he
  · intro i; fin_cases i
    · exact h0a
    · exact h1a
    · exact h2a
  · intro i; fin_cases i
    · exact h0b
    · exact h1b
    · exact h2b
  · intro i; fin_cases i
    · exact h0c
    · exact h1c
    · exact h2c

open LaurentTorsionCombinations

theorem centered_pair (w a : ℂˣ)
    (hw : (w:ℂ)^4-(w:ℂ)^2+1=0) (ha : a^2=w)
    (j k : ℕ) (hj : 1 ≤ j) (hk : 1 ≤ k) (hjk : j+k < 12) :
    (centeredZ w j+centeredZ w k-centeredZ w (j+k))^2 =
      centeredP w j+centeredP w k+centeredP w (j+k) := by
  have h := frobenius_stickelberger_pair w a hw ha j k hj hk hjk
  simp only [centeredZ, centeredP, ellipticE]
  have hb : 2*scalar (1/2)=1 := by
    have hh := congrArg scalar (show (2:ℂ)*(1/2)=1 by norm_num)
    simpa only [map_mul,map_ofNat,map_one] using hh
  have hc : 12*scalar (1/12)=1 := by
    have hh := congrArg scalar (show (12:ℂ)*(1/12)=1 by norm_num)
    simpa only [map_mul,map_ofNat,map_one] using hh
  have h4 : IsUnit (4:L) := by
    simpa only [map_ofNat] using (isUnit_iff_ne_zero.mpr (by norm_num : (4:ℂ) ≠ 0)).map scalar
  apply h4.mul_left_cancel
  linear_combination h +
    (2*scalar (1/2)-4*(jacobiLogarithmicLambert p (constantUnit (w^j))+
      jacobiLogarithmicLambert p (constantUnit (w^k))-
      jacobiLogarithmicLambert p (constantUnit (w^(j+k))))+1)*hb-hc
end KanadeRussell.Infra.LaurentTorsionAddition
