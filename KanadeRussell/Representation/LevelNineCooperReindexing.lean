import KanadeRussell.Representation.LevelNineThetaFactorization

/-! Exact affine lattice reindexing between the twelve Cooper monomials and
all three level-nine numerator masks. The product identity is not assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
namespace KanadeRussell.Representation.LevelNineCooperReindexing
open LevelNineNumeratorMasks

def cooperPowers : Fin 12 → ℕ × ℕ := ![(0, 0), (0, 1), (1, 0), (1, 2), (4, 1), (4, 4), (6, 2), (6, 5), (9, 4), (9, 6), (10, 5), (10, 6)]
def cooperSign : Fin 12 → ℤ := ![1, (-1), (-1), 1, 1, (-1), (-1), 1, 1, (-1), (-1), 1]
def residue : Fin 3 → Fin 12 → Fin 9 × Fin 9 := ![![(0, 0), (0, 2), (8, 7), (6, 5), (8, 3), (6, 3), (4, 4), (2, 4), (4, 2), (2, 0), (1, 5), (1, 7)], ![(0, 0), (0, 1), (8, 7), (7, 6), (3, 7), (3, 6), (5, 5), (4, 5), (5, 1), (4, 0), (7, 2), (8, 2)], ![(0, 0), (0, 1), (7, 5), (6, 4), (7, 3), (6, 3), (2, 2), (1, 2), (2, 1), (1, 0), (8, 4), (8, 5)]]
private def matrix : Fin 3 → Fin 12 → ℤ × ℤ × ℤ × ℤ := ![![(1, (-1), 1, 0), (1, 0, 0, 1), (0, 1, (-1), 1), (1, (-1), 0, (-1)), (0, 1, 1, 0), (1, (-1), 1, 0), ((-1), 0, (-1), 1), (0, (-1), (-1), 0), ((-1), 1, 0, 1), (0, (-1), 1, (-1)), ((-1), 0, 0, (-1)), ((-1), 0, (-1), 1)], ![(1, 0, 1, (-1)), (1, 0, 0, 1), ((-1), 1, 0, 1), (0, (-1), 1, (-1)), (1, 0, 0, 1), (1, 0, 1, (-1)), ((-1), 1, (-1), 0), (0, (-1), (-1), 0), ((-1), 1, 0, 1), (0, (-1), 1, (-1)), (0, (-1), (-1), 0), ((-1), 1, (-1), 0)], ![(1, (-1), 1, 0), (1, 0, 0, 1), (0, 1, (-1), 1), (1, (-1), 0, (-1)), (0, 1, 1, 0), (1, (-1), 1, 0), ((-1), 0, (-1), 1), (0, (-1), (-1), 0), ((-1), 1, 0, 1), (0, (-1), 1, (-1)), ((-1), 0, 0, (-1)), ((-1), 0, (-1), 1)]]
private def inverseMatrix : Fin 3 → Fin 12 → ℤ × ℤ × ℤ × ℤ := ![![(0, 1, (-1), 1), (1, 0, 0, 1), (1, (-1), 1, 0), (1, (-1), 0, (-1)), (0, 1, 1, 0), (0, 1, (-1), 1), ((-1), 0, (-1), 1), (0, (-1), (-1), 0), ((-1), 1, 0, 1), ((-1), 1, (-1), 0), ((-1), 0, 0, (-1)), ((-1), 0, (-1), 1)], ![(1, 0, 1, (-1)), (1, 0, 0, 1), ((-1), 1, 0, 1), ((-1), 1, (-1), 0), (1, 0, 0, 1), (1, 0, 1, (-1)), (0, (-1), 1, (-1)), (0, (-1), (-1), 0), ((-1), 1, 0, 1), ((-1), 1, (-1), 0), (0, (-1), (-1), 0), (0, (-1), 1, (-1))], ![(0, 1, (-1), 1), (1, 0, 0, 1), (1, (-1), 1, 0), (1, (-1), 0, (-1)), (0, 1, 1, 0), (0, 1, (-1), 1), ((-1), 0, (-1), 1), (0, (-1), (-1), 0), ((-1), 1, 0, 1), ((-1), 1, (-1), 0), ((-1), 0, 0, (-1)), ((-1), 0, (-1), 1)]]
private def translation : Fin 3 → Fin 12 → ℤ × ℤ := ![![(0, 0), (0, 0), ((-1), (-1)), ((-1), (-1)), ((-1), 0), ((-1), 0), ((-1), (-1)), ((-1), (-1)), ((-1), 0), ((-1), 0), ((-1), (-1)), ((-1), (-1))], ![(0, 0), (0, 0), ((-1), (-1)), ((-1), (-1)), (0, (-1)), (0, (-1)), ((-1), (-1)), ((-1), (-1)), ((-1), 0), ((-1), 0), ((-1), (-1)), ((-1), (-1))], ![(0, 0), (0, 0), ((-1), (-1)), ((-1), (-1)), ((-1), 0), ((-1), 0), ((-1), (-1)), ((-1), (-1)), ((-1), 0), ((-1), 0), ((-2), (-1)), ((-2), (-1))]]

def affineForward (k : Fin 3) (h : Fin 12) (z : ℤ × ℤ) : ℤ × ℤ :=
  let w := matrix k h
  let t := translation k h
  (w.1*z.1+w.2.1*z.2+t.1, w.2.2.1*z.1+w.2.2.2*z.2+t.2)
private def affineBackward (k : Fin 3) (h : Fin 12) (z : ℤ × ℤ) : ℤ × ℤ :=
  let w := inverseMatrix k h
  let t := translation k h
  (w.1*(z.1-t.1)+w.2.1*(z.2-t.2), w.2.2.1*(z.1-t.1)+w.2.2.2*(z.2-t.2))

def affineEquiv (k : Fin 3) (h : Fin 12) : (ℤ × ℤ) ≃ (ℤ × ℤ) where
  toFun := affineForward k h
  invFun := affineBackward k h
  left_inv z := by
    fin_cases k <;> fin_cases h <;> ext <;>
      norm_num [affineForward, affineBackward, matrix, inverseMatrix, translation,
        Matrix.cons_val_succ]
  right_inv z := by
    fin_cases k <;> fin_cases h <;> ext <;>
      norm_num [affineForward, affineBackward, matrix, inverseMatrix, translation,
        Matrix.cons_val_succ] <;> ring

theorem residue_active (k : Fin 3) (h : Fin 12) :
    mask k (residue k h).1 (residue k h).2 ≠ 0 := by
  fin_cases k <;> fin_cases h <;> decide

def activeResidue (k : Fin 3) (h : Fin 12) : ActiveResidue k :=
  ⟨residue k h, residue_active k h⟩

theorem activeResidue_bijective (k : Fin 3) : Function.Bijective (activeResidue k) := by
  fin_cases k <;> decide

def residueEquiv (k : Fin 3) : Fin 12 ≃ ActiveResidue k :=
  Equiv.ofBijective (activeResidue k) (activeResidue_bijective k)

def cooperCosetEquiv (k : Fin 3) : (Fin 12 × (ℤ × ℤ)) ≃ ActiveCoset k :=
  (Equiv.prodCongrRight (fun h => affineEquiv k h)).trans
    ((Equiv.prodCongr (residueEquiv k) (Equiv.refl (ℤ × ℤ))).trans (residueCosetEquiv k))

def cooperExponent (k : Fin 3) (h : Fin 12) (z : ℤ × ℤ) : ℤ :=
  let a := labels k 2
  let b := labels k 1
  let i : ℤ := (cooperPowers h).1
  let j : ℤ := (cooperPowers h).2
  36*(z.1*z.1+z.2*z.2-z.1*z.2)+
    (12*a+4*b-18+9*(i-j))*z.1+(4*b-9+9*(-i+2*j))*z.2+a*i+b*j

theorem cooper_sign (k : Fin 3) (h : Fin 12) :
    mask k (residue k h).1 (residue k h).2 = cooperSign h := by
  fin_cases k <;> fin_cases h <;> decide

theorem cooper_exponent (k : Fin 3) (h : Fin 12) (z : ℤ × ℤ) :
    cosetExponent k (cooperCosetEquiv k (h,z)).val = cooperExponent k h z := by
  change cosetExponent k ⟨(residue k h).1, (residue k h).2,
    (affineForward k h z).1, (affineForward k h z).2⟩ = _
  rw [cosetExponent_expanded]
  fin_cases k <;> fin_cases h <;>
    norm_num [cooperExponent, cooperPowers, labels, residue, affineForward, matrix,
      translation, quadratic, Matrix.cons_val_succ, Matrix.cons_val_two] <;> ring

end KanadeRussell.Representation.LevelNineCooperReindexing
