import KanadeRussell.Tsuchioka.TwoVariableSupport

/-!
Finite coefficientwise contraction of a separately bounded double Laurent series
against a bilateral scalar sequence. Delta evaluation and its Euler derivative
are proved by finite reindexing, without multiplying arbitrary distributions.
-/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.FormalSeries

open scoped BigOperators

variable {A : Type*} [CommRing A]

/-- Convolution in the ratio t2/t1. The results below supply finite support. -/
noncomputable def contract (c : ℤ → A) (f : LaurentSeries (LaurentSeries A))
    (a b : ℤ) : A :=
  ∑ᶠ n : ℤ, c n * (f.coeff (b - n)).coeff (a + n)

/-- An explicit finite interval contains all terms of a bounded contraction. -/
theorem contract_eq_sum {f : LaurentSeries (LaurentSeries A)} {l r : ℤ}
    (hf : RectangularBound f l r) (c : ℤ → A) (a b : ℤ) :
    contract c f a b =
      ∑ n ∈ Finset.Icc (l - a) (b - r), c n * (f.coeff (b - n)).coeff (a + n) := by
  apply finsum_eq_sum_of_support_subset
  simpa only [Finset.coe_Icc] using rectangular_contraction_support hf c a b

theorem contract_add {f : LaurentSeries (LaurentSeries A)} {l r : ℤ}
    (hf : RectangularBound f l r) (c d : ℤ → A) (a b : ℤ) :
    contract (c + d) f a b = contract c f a b + contract d f a b := by
  simp only [contract_eq_sum hf, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem contract_sub {f : LaurentSeries (LaurentSeries A)} {l r : ℤ}
    (hf : RectangularBound f l r) (c d : ℤ → A) (a b : ℤ) :
    contract (c - d) f a b = contract c f a b - contract d f a b := by
  simp only [contract_eq_sum hf, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem contract_const_mul {f : LaurentSeries (LaurentSeries A)} {l r : ℤ}
    (hf : RectangularBound f l r) (c : ℤ → A) (z : A) (a b : ℤ) :
    contract (fun n => z * c n) f a b = z * contract c f a b := by
  simp only [contract_eq_sum hf, mul_assoc, Finset.mul_sum]

/-- The coefficient after the specialization t1=u*t2. -/
noncomputable def diagonalCoefficient (u : Aˣ)
    (f : LaurentSeries (LaurentSeries A)) (d : ℤ) : A :=
  ∑ᶠ i : ℤ, (u ^ i : Aˣ) * (f.coeff (d - i)).coeff i

/-- The same specialization with the inner Euler weight retained. -/
noncomputable def diagonalEulerCoefficient (u : Aˣ)
    (f : LaurentSeries (LaurentSeries A)) (d : ℤ) : A :=
  ∑ᶠ i : ℤ, (i : A) * (u ^ i : Aˣ) * (f.coeff (d - i)).coeff i

theorem diagonalCoefficient_finite {f : LaurentSeries (LaurentSeries A)} {l r : ℤ}
    (hf : RectangularBound f l r) (u : Aˣ) (d : ℤ) :
    (Function.support (fun i : ℤ => (u ^ i : Aˣ) * (f.coeff (d - i)).coeff i)).Finite := by
  simpa only [zero_add] using
    rectangular_contraction_finite hf (fun i => (u ^ i : Aˣ)) 0 d

theorem diagonalEulerCoefficient_finite {f : LaurentSeries (LaurentSeries A)} {l r : ℤ}
    (hf : RectangularBound f l r) (u : Aˣ) (d : ℤ) :
    (Function.support (fun i : ℤ => (i : A) * (u ^ i : Aˣ) *
      (f.coeff (d - i)).coeff i)).Finite := by
  simpa only [zero_add] using
    rectangular_contraction_finite hf (fun i => (i : A) * (u ^ i : Aˣ)) 0 d

/-- Delta contraction evaluates the first variable at the pole, with its exact phase. -/
theorem contract_delta {f : LaurentSeries (LaurentSeries A)} {l r : ℤ}
    (hf : RectangularBound f l r) (u : Aˣ) (a b : ℤ) :
    contract (fun n => ((u ^ n : Aˣ) : A)) f a b =
      (u ^ (-a) : Aˣ) * diagonalCoefficient u f (a + b) := by
  unfold contract diagonalCoefficient
  rw [mul_finsum' _ _ (diagonalCoefficient_finite hf u (a + b))]
  apply finsum_eq_of_bijective (fun n : ℤ => a + n)
    (Equiv.addLeft a).bijective
  intro n
  have hb : a + b - (a + n) = b - n := by omega
  rw [hb, ← mul_assoc, ← Units.val_mul, ← zpow_add]
  simp

/-- Euler-delta contraction has the additional inner derivative term. -/
theorem contract_eulerDelta {f : LaurentSeries (LaurentSeries A)} {l r : ℤ}
    (hf : RectangularBound f l r) (u : Aˣ) (a b : ℤ) :
    contract (fun n : ℤ => (n : A) * (u ^ n : Aˣ)) f a b =
      (u ^ (-a) : Aˣ) *
        (diagonalEulerCoefficient u f (a + b) -
          (a : A) * diagonalCoefficient u f (a + b)) := by
  have hfin := diagonalCoefficient_finite hf u (a + b)
  have hefin := diagonalEulerCoefficient_finite hf u (a + b)
  have hafin : (Function.support (fun i : ℤ =>
      (a : A) * ((u ^ i : Aˣ) * (f.coeff (a + b - i)).coeff i))).Finite :=
    hfin.subset (by
      intro i hi
      change (u ^ i : Aˣ) * (f.coeff (a + b - i)).coeff i ≠ 0
      intro hz
      exact hi (by simp [hz]))
  have hsubfin : (Function.support (fun i : ℤ =>
      (i : A) * (u ^ i : Aˣ) * (f.coeff (a + b - i)).coeff i -
        (a : A) * ((u ^ i : Aˣ) * (f.coeff (a + b - i)).coeff i))).Finite := by
    exact Function.HasFiniteSupport.sub hefin hafin
  unfold contract diagonalCoefficient diagonalEulerCoefficient
  rw [mul_finsum' _ _ hfin, ← finsum_sub_distrib hefin hafin,
    mul_finsum' _ _ hsubfin]
  apply finsum_eq_of_bijective (fun n : ℤ => a + n)
    (Equiv.addLeft a).bijective
  intro n
  have hb : a + b - (a + n) = b - n := by omega
  rw [hb, Int.cast_add, zpow_add, Units.val_mul]
  have hu : ((u ^ (-a) : Aˣ) : A) * (u ^ a : Aˣ) = 1 := by
    rw [← Units.val_mul, ← zpow_add]
    simp
  linear_combination -((n : A) * (u ^ n : Aˣ) *
    (f.coeff (b - n)).coeff (a + n)) * hu

end KanadeRussell.Tsuchioka.FormalSeries
