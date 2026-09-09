import KanadeRussell.Product.A2Core
import KanadeRussell.Product.A2Lattice
import KanadeRussell.Product.LambertScaling
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-! A₂ trisection and the remaining square-identity route to ProductNorm. -/
open PowerSeries PowerSeries.WithPiTopology
open scoped DiscreteUniformity QTheory
namespace KanadeRussell.Product

private theorem eval_three_term (n : ℕ) :
    intEval (q^3) (q^n) = q^(3*n) := by
  rw [map_pow, intEval_X (by simp [q]), ← pow_mul]

/-- Exact decomposition into the index-three sublattice and six shifted cosets. -/
theorem a2_trisection_core : a = intEval (q^3) a + 6*q*intEval (q^3) coreTheta := by
  let f : ℤ × ℤ → PowerSeries ℤ := fun rs => q^(rs.1^2+rs.1*rs.2+rs.2^2).toNat
  have hd : HasSum (fun rs => f (A2Lattice.diagonal rs)) (intEval (q^3) a) := by
    apply (Infra.summable_a2.hasSum.map (intEval (q^3)) (by fun_prop)).congr_fun
    rintro ⟨r,s⟩
    dsimp only [Function.comp_def, f]
    rw [A2Lattice.diagonal_norm, eval_three_term]
    congr 1
    have hn := Infra.a2_nonneg r s
    omega
  have hc : HasSum (fun rs : ℤ × ℤ => q^(1+3*(coreExponent rs.1 rs.2).toNat))
      (q*intEval (q^3) coreTheta) := by
    apply ((summable_coreTheta.hasSum.map (intEval (q^3)) (by fun_prop)).mul_left q).congr_fun
    intro rs
    dsimp only [Function.comp_def]
    rw [eval_three_term, pow_add, pow_one]
  have hf : HasSum (fun kr : Fin 6 × (ℤ × ℤ) => f (A2Lattice.coset kr.1 kr.2))
      (6*q*intEval (q^3) coreTheta) := by
    have h := (hasSum_fintype (fun _ : Fin 6 => (1 : PowerSeries ℤ))).mul_of_nonarchimedean' hc
    have he : ∑ k : Fin 6, (1 : PowerSeries ℤ) = 6 := by norm_num
    rw [he, ← mul_assoc] at h
    apply h.congr_fun
    rintro ⟨k,r,s⟩
    dsimp only [f]
    rw [A2Lattice.coset_norm, one_mul]
    congr 1
    have hn := coreExponent_nonneg r s
    change (1+3*coreExponent r s).toNat = _
    omega
  have hh : HasSum (f ∘ A2Lattice.combine)
      (intEval (q^3) a + 6*q*intEval (q^3) coreTheta) := hd.sum hf
  exact Infra.summable_a2.hasSum.unique (A2Lattice.equiv.hasSum_iff.mp hh)

theorem intEval_E (d e : ℕ) (hd : 0 < d) (he : 0 < e) :
    intEval (q^d) (E e) = E (d*e) := by
  have hq : IsTopologicallyNilpotent (q^d) := by simp [q, hd.ne']
  have hqe : IsTopologicallyNilpotent (q^e) := by simp [q, he.ne']
  rw [E, map_qPochhammerInf (intEval (q^d)) (by fun_prop) _ hqe,
    map_pow, intEval_X hq, ← pow_mul]
  rfl

/-- The A₂ trisection formula, with its Euler denominator cleared. -/
theorem a2_trisection : (a-intEval (q^3) a)*E 3 = 6*q*(E 9)^3 := by
  have hp := congrArg (intEval (q^3)) coreTheta_product
  simp only [map_mul, map_pow, intEval_E 3 1 (by decide) (by decide),
    intEval_E 3 3 (by decide) (by decide), Nat.reduceMul] at hp
  nth_rw 1 [a2_trisection_core]
  rw [add_sub_cancel_left]
  calc
    (6*q*intEval (q^3) coreTheta)*E 3 = 6*q*(E 3*intEval (q^3) coreTheta) := by ring
    _ = _ := by rw [hp]

/-- ProductNorm now follows from the single remaining A₂ square identity. -/
theorem productNorm_of_square (hsq : a^2 = 1+12*lambert 1-36*lambert 3) : ProductNorm :=
  productNorm_of_square_and_trisection hsq a2_trisection

end KanadeRussell.Product
