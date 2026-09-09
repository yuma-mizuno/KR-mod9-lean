import Mathlib

/-! The integral D4 root lattice and Tsuchioka's twisted Coxeter transformation. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.RootData

abbrev Lattice := Fin 4 → ℤ

/-- The D4 Cartan form, with node 1 (the second coordinate) central. -/
def pairing (x y : Lattice) : ℤ :=
  2 * (x 0 * y 0 + x 1 * y 1 + x 2 * y 2 + x 3 * y 3) -
    (x 0 * y 1 + x 1 * y 0 + x 1 * y 2 + x 2 * y 1 +
      x 1 * y 3 + x 3 * y 1)

def simpleRoot (i : Fin 4) : Lattice := fun j => if j.val = i.val then 1 else 0

def reflection (i : Fin 4) (x : Lattice) : Lattice :=
  fun j => x j - pairing x (simpleRoot i) * simpleRoot i j

/-- Triality cycles the outer nodes 0 -> 2 -> 3 -> 0. -/
def triality (x : Lattice) : Lattice := ![x 3, x 1, x 0, x 2]

/-- The source's nu = sigma_1 sigma_2 sigma'. -/
def coxeter (x : Lattice) : Lattice := reflection 0 (reflection 1 (triality x))

theorem coxeter_apply (x : Lattice) :
    coxeter x = ![x 0 - x 1 + x 2, x 0 - x 1 + x 2 + x 3, x 0, x 2] := by
  ext i
  fin_cases i <;>
    simp [coxeter, reflection, pairing, simpleRoot, triality] <;> ring

theorem coxeter_preserves_pairing (x y : Lattice) :
    pairing (coxeter x) (coxeter y) = pairing x y := by
  simp [coxeter_apply, pairing]
  ring

theorem coxeter_six (x : Lattice) : (coxeter^[6]) x = -x := by
  ext i
  fin_cases i <;>
    simp [Function.iterate_succ_apply', coxeter_apply] <;> ring

theorem coxeter_twelve (x : Lattice) : (coxeter^[12]) x = x := by
  rw [show (12 : ℕ) = 6 + 6 from rfl, Function.iterate_add_apply, coxeter_six, coxeter_six]
  simp

/-- The pairing sequence is derived from the Coxeter transformation, not assumed. -/
theorem first_root_orbit_pairing (p : Fin 12) :
    pairing ((coxeter^[p.val]) (simpleRoot 0)) (simpleRoot 0) =
      ![2, 1, 1, 0, -1, -1, -2, -1, -1, 0, 1, 1] p := by
  fin_cases p <;> decide

end KanadeRussell.Tsuchioka.RootData
