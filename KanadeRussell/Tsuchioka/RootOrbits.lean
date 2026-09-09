import KanadeRussell.Tsuchioka.RootData

/-! Exhaustive classification of the norm-two vectors of the D4 lattice.
The two twisted-Coxeter orbits are derived from the integral Cartan form. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

namespace KanadeRussell.Tsuchioka.RootData

/-- The usual orthogonal coordinates of the D4 root lattice. -/
def orthogonalCoordinates (x : Lattice) : Lattice :=
  ![x 0, -x 0 + x 1, -x 1 + x 2 + x 3, -x 2 + x 3]

def fromOrthogonalCoordinates (a b c d : ℤ) : Lattice :=
  ![a, a + b, (a + b + c - d) / 2, (a + b + c + d) / 2]

theorem orthogonalCoordinates_inverse (x : Lattice) :
    fromOrthogonalCoordinates (orthogonalCoordinates x 0) (orthogonalCoordinates x 1)
      (orthogonalCoordinates x 2) (orthogonalCoordinates x 3) = x := by
  ext i
  fin_cases i <;> simp [fromOrthogonalCoordinates, orthogonalCoordinates] <;> omega

theorem pairing_self_eq_squares (x : Lattice) :
    pairing x x = (orthogonalCoordinates x 0) ^ 2 + (orthogonalCoordinates x 1) ^ 2 +
      (orthogonalCoordinates x 2) ^ 2 + (orthogonalCoordinates x 3) ^ 2 := by
  simp only [orthogonalCoordinates, pairing, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  ring

/-- Roots are precisely the norm-two lattice vectors in this concrete model. -/
def IsRoot (x : Lattice) : Prop := pairing x x = 2

theorem integer_square_bound (a : ℤ) (ha : a ^ 2 ≤ 2) : -1 ≤ a ∧ a ≤ 1 := by
  constructor
  · by_contra h
    have h' : a ≤ -2 := by omega
    nlinarith [sq_nonneg (a + 2)]
  · by_contra h
    have h' : 2 ≤ a := by omega
    nlinarith [sq_nonneg (a - 2)]

theorem root_orthogonal_bounds (x : Lattice) (hx : IsRoot x) :
    (-1 ≤ orthogonalCoordinates x 0 ∧ orthogonalCoordinates x 0 ≤ 1) ∧
    (-1 ≤ orthogonalCoordinates x 1 ∧ orthogonalCoordinates x 1 ≤ 1) ∧
    (-1 ≤ orthogonalCoordinates x 2 ∧ orthogonalCoordinates x 2 ≤ 1) ∧
    (-1 ≤ orthogonalCoordinates x 3 ∧ orthogonalCoordinates x 3 ≤ 1) := by
  have h : (orthogonalCoordinates x 0) ^ 2 + (orthogonalCoordinates x 1) ^ 2 +
      (orthogonalCoordinates x 2) ^ 2 + (orthogonalCoordinates x 3) ^ 2 = 2 := by
    rw [← pairing_self_eq_squares]
    exact hx
  have h0 := sq_nonneg (orthogonalCoordinates x 0)
  have h1 := sq_nonneg (orthogonalCoordinates x 1)
  have h2 := sq_nonneg (orthogonalCoordinates x 2)
  have h3 := sq_nonneg (orthogonalCoordinates x 3)
  exact ⟨integer_square_bound _ (by nlinarith), integer_square_bound _ (by nlinarith),
    integer_square_bound _ (by nlinarith), integer_square_bound _ (by nlinarith)⟩

/-- The source chooses the two simple roots at nodes zero and one. -/
def orbitRepresentative (r : Fin 2) : Lattice :=
  simpleRoot (if r = 0 then 0 else 1)

def orbitRoot (r : Fin 2) (p : Fin 12) : Lattice :=
  (coxeter^[p.val]) (orbitRepresentative r)

theorem coxeter_iterate_preserves_pairing (x y : Lattice) (p : ℕ) :
    pairing ((coxeter^[p]) x) ((coxeter^[p]) y) = pairing x y := by
  induction p with
  | zero => rfl
  | succ p ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      coxeter_preserves_pairing, ih]

theorem orbitRoot_isRoot (r : Fin 2) (p : Fin 12) : IsRoot (orbitRoot r p) := by
  unfold IsRoot orbitRoot
  rw [coxeter_iterate_preserves_pairing]
  fin_cases r <;> decide

/-- This is exhaustive for all integral lattice vectors, not a bounded-root
assumption: the coordinate bound follows from the positive definite norm. -/
theorem isRoot_mem_orbits (x : Lattice) (hx : IsRoot x) :
    ∃ r : Fin 2, ∃ p : Fin 12, x = orbitRoot r p := by
  have hnorm : (orthogonalCoordinates x 0) ^ 2 + (orthogonalCoordinates x 1) ^ 2 +
      (orthogonalCoordinates x 2) ^ 2 + (orthogonalCoordinates x 3) ^ 2 = 2 := by
    rw [← pairing_self_eq_squares]
    exact hx
  obtain ⟨⟨h0l, h0u⟩, ⟨h1l, h1u⟩, ⟨h2l, h2u⟩, ⟨h3l, h3u⟩⟩ :=
    root_orthogonal_bounds x hx
  have hi := orthogonalCoordinates_inverse x
  generalize ha : orthogonalCoordinates x 0 = a at *
  generalize hb : orthogonalCoordinates x 1 = b at *
  generalize hc : orthogonalCoordinates x 2 = c at *
  generalize hd : orthogonalCoordinates x 3 = d at *
  interval_cases a <;> interval_cases b <;> interval_cases c <;> interval_cases d <;>
    norm_num at hnorm
  all_goals rw [← hi]
  all_goals decide

theorem isRoot_iff_mem_orbits (x : Lattice) :
    IsRoot x ↔ ∃ r : Fin 2, ∃ p : Fin 12, x = orbitRoot r p := by
  constructor
  · exact isRoot_mem_orbits x
  · rintro ⟨r, p, rfl⟩
    exact orbitRoot_isRoot r p


/-- The two length-twelve orbits are disjoint, with no repeated roots. -/
theorem orbitRoot_injective :
    Function.Injective (fun q : Fin 2 × Fin 12 => orbitRoot q.1 q.2) := by
  decide

def Root := {x : Lattice // IsRoot x}

def rootParameterization (q : Fin 2 × Fin 12) : Root :=
  ⟨orbitRoot q.1 q.2, orbitRoot_isRoot q.1 q.2⟩

theorem rootParameterization_bijective : Function.Bijective rootParameterization := by
  constructor
  · intro a b h
    exact orbitRoot_injective (congrArg Subtype.val h)
  · rintro ⟨x, hx⟩
    obtain ⟨r, p, hp⟩ := isRoot_mem_orbits x hx
    exact ⟨(r, p), Subtype.ext hp.symm⟩

noncomputable def rootEquiv : (Fin 2 × Fin 12) ≃ Root :=
  Equiv.ofBijective rootParameterization rootParameterization_bijective

noncomputable instance : Fintype Root := Fintype.ofEquiv (Fin 2 × Fin 12) rootEquiv

theorem card_root : Fintype.card Root = 24 := by
  rw [← Fintype.card_congr rootEquiv]
  decide

def firstRoot : Root := rootParameterization (0, 0)

def secondRoot : Root := rootParameterization (1, 0)

@[simp] theorem firstRoot_val : firstRoot.val = simpleRoot 0 := rfl

@[simp] theorem secondRoot_val : secondRoot.val = simpleRoot 1 := rfl

end KanadeRussell.Tsuchioka.RootData
