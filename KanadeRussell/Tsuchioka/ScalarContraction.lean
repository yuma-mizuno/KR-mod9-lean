import KanadeRussell.Tsuchioka.WeightedFields

/-! Scalar-valued kernels acting on finite coefficient contractions. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

open FormalSeries

variable {K : Type*} [Field K] [CharZero K]

noncomputable def scalarContract (c : ℤ → K)
    (f : LaurentSeries (LaurentSeries (Space K))) (a b : ℤ) : Space K :=
  contract (fun n => MvPolynomial.C (c n)) f a b

theorem scalarContract_add {f : LaurentSeries (LaurentSeries (Space K))} {l r : ℤ}
    (hf : RectangularBound f l r) (c d : ℤ → K) (a b : ℤ) :
    scalarContract (c + d) f a b = scalarContract c f a b + scalarContract d f a b := by
  have hc : (fun n => (MvPolynomial.C ((c + d) n) : Space K)) =
      (fun n => MvPolynomial.C (c n)) + (fun n => MvPolynomial.C (d n)) := by
    funext n
    simp
  unfold scalarContract
  rw [hc, contract_add hf]

theorem scalarContract_sub {f : LaurentSeries (LaurentSeries (Space K))} {l r : ℤ}
    (hf : RectangularBound f l r) (c d : ℤ → K) (a b : ℤ) :
    scalarContract (c - d) f a b = scalarContract c f a b - scalarContract d f a b := by
  have hc : (fun n => (MvPolynomial.C ((c - d) n) : Space K)) =
      (fun n => MvPolynomial.C (c n)) - (fun n => MvPolynomial.C (d n)) := by
    funext n
    simp
  unfold scalarContract
  rw [hc, contract_sub hf]

theorem scalarContract_mul {f : LaurentSeries (LaurentSeries (Space K))} {l r : ℤ}
    (hf : RectangularBound f l r) (c : ℤ → K) (z : K) (a b : ℤ) :
    scalarContract (fun n => z * c n) f a b = z • scalarContract c f a b := by
  have hc : (fun n => (MvPolynomial.C (z * c n) : Space K)) =
      (fun n => MvPolynomial.C z * MvPolynomial.C (c n)) := by
    funext n
    simp
  unfold scalarContract
  rw [hc, contract_const_mul hf]
  simp only [Algebra.smul_def, MvPolynomial.algebraMap_eq]

theorem scalarContract_delta_phase (w : K) (p : ℤ)
    (f : LaurentSeries (LaurentSeries (Space K))) (a b : ℤ) :
    scalarContract (Scalar.delta (w ^ (-p))) f a b =
      contract (fun n => MvPolynomial.C (w ^ ((-p) * n))) f a b := by
  unfold scalarContract Scalar.delta
  simp only [← zpow_mul]

end KanadeRussell.Tsuchioka.Fock
