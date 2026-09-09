import KanadeRussell.Tsuchioka.RootData

/-! The normalized Coxeter eigenfunctional on the actual D4 root lattice. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.RootData

variable {K : Type*} [CommRing K]

/-- The Coxeter eigenfunctional normalized to one on the first simple root. -/
def rootWeight (t : K) (x : Lattice) : K :=
  x 0 + (t ^ 3 - t ^ 2) * x 1 +
    (-t ^ 3 + t ^ 2 + t - 1) * x 2 + (t ^ 2 - t) * x 3

@[simp] theorem rootWeight_zero (t : K) : rootWeight t 0 = 0 := by
  simp [rootWeight]

theorem rootWeight_add (t : K) (x y : Lattice) :
    rootWeight t (x + y) = rootWeight t x + rootWeight t y := by
  simp only [rootWeight, Pi.add_apply, Int.cast_add]
  ring

theorem rootWeight_neg (t : K) (x : Lattice) :
    rootWeight t (-x) = -rootWeight t x := by
  simp only [rootWeight, Pi.neg_apply, Int.cast_neg]
  ring

@[simp] theorem rootWeight_first (t : K) : rootWeight t (simpleRoot 0) = 1 := by
  norm_num [rootWeight, simpleRoot]

@[simp] theorem rootWeight_second (t : K) :
    rootWeight t (simpleRoot 1) = t ^ 3 - t ^ 2 := by
  norm_num [rootWeight, simpleRoot]

/-- The defining covariance is derived from the source's Coxeter matrix. -/
theorem rootWeight_coxeter (t : K) (ht : t ^ 4 - t ^ 2 + 1 = 0) (x : Lattice) :
    rootWeight t (coxeter x) = t * rootWeight t x := by
  simp [rootWeight, coxeter_apply]
  push_cast
  linear_combination ((x 2 : K) - (x 1 : K)) * ht

theorem rootWeight_iterate (t : K) (ht : t ^ 4 - t ^ 2 + 1 = 0)
    (p : ℕ) (x : Lattice) :
    rootWeight t ((coxeter^[p]) x) = t ^ p * rootWeight t x := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [Function.iterate_succ_apply', rootWeight_coxeter t ht, ih, pow_succ]
    ring

theorem rootWeight_first_orbit (t : K) (ht : t ^ 4 - t ^ 2 + 1 = 0) (p : ℕ) :
    rootWeight t ((coxeter^[p]) (simpleRoot 0)) = t ^ p := by
  rw [rootWeight_iterate t ht, rootWeight_first, mul_one]

/-- The four root additions used in the first-root operator fusion. -/
theorem first_fusion_four :
    (coxeter^[4]) (simpleRoot 0) + simpleRoot 0 = (coxeter^[2]) (simpleRoot 0) := by
  decide

theorem first_fusion_eight :
    (coxeter^[8]) (simpleRoot 0) + simpleRoot 0 = (coxeter^[10]) (simpleRoot 0) := by
  decide

theorem first_fusion_five :
    (coxeter^[5]) (simpleRoot 0) + simpleRoot 0 = (coxeter^[9]) (simpleRoot 1) := by
  decide

theorem first_fusion_seven :
    (coxeter^[7]) (simpleRoot 0) + simpleRoot 0 = (coxeter^[4]) (simpleRoot 1) := by
  decide

/-- The second-root weight follows from the actual fusion in the root lattice. -/
theorem second_weight_fusion (t : K) (ht : t ^ 4 - t ^ 2 + 1 = 0) :
    t ^ 5 + 1 = t ^ 9 * (t ^ 3 - t ^ 2) := by
  have h := congrArg (rootWeight t) first_fusion_five
  rw [rootWeight_add, rootWeight_first_orbit t ht, rootWeight_first,
    rootWeight_iterate t ht, rootWeight_second] at h
  exact h

end KanadeRussell.Tsuchioka.RootData
