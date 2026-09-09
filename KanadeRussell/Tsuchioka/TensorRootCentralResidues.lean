import KanadeRussell.Tsuchioka.TensorRootCentralEuler
import KanadeRussell.Tsuchioka.TensorPairResidues

/-! Complete central delta and Euler residues for any tensor root self
pair, with its projected Heisenberg weight and level-three scalar. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

open FormalSeries
open RootData (Lattice)

variable {K : Type*} [Field K] [CharZero K]

theorem tensorRoot_delta_six (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (beta : Lattice) (j : Fin 3) (f : Space K) (a b : ℤ) :
    contract (fun n : ℤ => MvPolynomial.C ((-1 : K) ^ n))
        (tensorNormalProduct w beta beta j j f) (-a) (-b) =
      if a + b = 0 then (-1 : K) ^ a • f else 0 := by
  have hc : (fun n : ℤ => MvPolynomial.C ((-1 : K) ^ n)) =
      (fun n => ((phaseUnit w hw 6 ^ n : (Space K)ˣ) : Space K)) := by
    funext n
    rw [phaseUnit_zpow, root_six_neg_phase w hw]
  rw [hc, show (6 : ℤ) = ((6 : ℕ) : ℤ) from rfl,
    tensorNormalProduct_delta_contraction_same, RootData.coxeter_six, neg_add_cancel, tensorRootSummand_zero]
  norm_num only [Nat.cast_ofNat]
  rw [show (6 : ℤ) * (-a) = -6 * a by ring, root_six_neg_phase w hw]
  by_cases hab : a + b = 0
  · have hz : -a + -b = 0 := by omega
    simp [HahnSeries.C_apply, hz, hab, Algebra.smul_def, MvPolynomial.algebraMap_eq]
  · have hz : -a + -b ≠ 0 := by omega
    simp [HahnSeries.C_apply, HahnSeries.coeff_single, hz, hab]

theorem tensorRoot_delta_sum_six (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (beta : Lattice) (f : Space K) (a b : ℤ) :
    (1 / 144 : K) • ∑ j : Fin 3,
      contract (fun n : ℤ => MvPolynomial.C ((-1 : K) ^ n))
        (tensorNormalProduct w beta beta j j f) (-a) (-b) =
      if a + b = 0 then ((-1 : K) ^ a / 48) • f else 0 := by
  simp only [tensorRoot_delta_six w hw beta]
  by_cases hab : a + b = 0
  · simp only [if_pos hab, Fin.sum_univ_three, ← add_smul, smul_smul]
    congr 1
    ring
  · simp [hab]

theorem tensorRootSelfResidue_delta_central (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (beta : Lattice) (f : Space K) (a b : ℤ) :
    tensorRootPairResidue w beta beta f a b (Scalar.delta (-1 : K)) =
      if a + b = 0 then ((-1 : K) ^ a / 48) • f else 0 := by
  simpa only [tensorRootPairResidue_apply, tensorPairNormalResidue_apply, scalarContract, Scalar.delta] using
    tensorRoot_delta_sum_six w hw beta f a b

/-- The individual Euler residue retains the derivative of the normal product. -/
theorem tensorRootSelfNormalResidue_euler_central (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (beta : Lattice) (j : Fin 3) (f : Space K) (a b : ℤ) :
    tensorPairNormalResidue w beta beta j j f a b (Scalar.eulerDelta (-1 : K)) =
      MvPolynomial.C ((-1 : K) ^ a) *
        diagonalEulerCoefficient (phaseUnit w hw 6) (tensorNormalProduct w beta beta j j f) (-a + -b) +
      (a : K) • tensorPairNormalResidue w beta beta j j f a b (Scalar.delta (-1 : K)) := by
  obtain ⟨l, r, h⟩ := tensorNormalProduct_bounded w beta beta j j f
  have hc : (fun n : ℤ => (MvPolynomial.C (Scalar.delta (-1 : K) n) : Space K)) =
      (fun n => ((phaseUnit w hw 6 ^ n : (Space K)ˣ) : Space K)) := by
    funext n
    simp only [Scalar.delta, phaseUnit_zpow, root_six_neg_phase w hw]
  have he : (fun n : ℤ => (MvPolynomial.C (Scalar.eulerDelta (-1 : K) n) : Space K)) =
      (fun n : ℤ => (n : Space K) * ((phaseUnit w hw 6 ^ n : (Space K)ˣ) : Space K)) := by
    funext n
    simp only [Scalar.eulerDelta, map_mul, map_intCast, phaseUnit_zpow,
      root_six_neg_phase w hw]
  simp only [tensorPairNormalResidue_apply, scalarContract]
  rw [he, hc, contract_eulerDelta h, contract_delta h, phaseUnit_zpow]
  simp only [neg_neg, root_six_neg_phase w hw, Int.cast_neg, Algebra.smul_def,
    MvPolynomial.algebraMap_eq, map_intCast]
  ring

theorem tensorRootSelfResidue_euler_eq_heisenberg_delta (w : K)
    (hw : w ^ 4 - w ^ 2 + 1 = 0) (beta : Lattice) (f : Space K) (a b : ℤ) :
    tensorRootPairResidue w beta beta f a b (Scalar.eulerDelta (-1 : K)) =
      (-((-1 : K) ^ a) * RootData.rootWeight (w ^ (a + b)) beta / 12) • heisenbergMode w (a + b) f +
        (a : K) • tensorRootPairResidue w beta beta f a b (Scalar.delta (-1 : K)) := by
  simp only [tensorRootPairResidue_apply, tensorRootSelfNormalResidue_euler_central w hw beta,
    Finset.sum_add_distrib, ← Finset.mul_sum, sum_tensorNormalProduct_root_central_euler w hw beta,
    ← Finset.smul_sum, MvPolynomial.C_mul', smul_add, smul_smul]
  rw [show -(-a + -b) = a + b by ring]
  module

theorem tensorRootSelfResidue_euler_central (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (beta : Lattice) (f : Space K) (a b : ℤ) :
    tensorRootPairResidue w beta beta f a b (Scalar.eulerDelta (-1 : K)) =
      (-((-1 : K) ^ a) * RootData.rootWeight (w ^ (a + b)) beta / 12) • heisenbergMode w (a + b) f +
        (if a + b = 0 then ((a : K) * (-1 : K) ^ a / 48) • f else 0) := by
  rw [tensorRootSelfResidue_euler_eq_heisenberg_delta w hw beta, tensorRootSelfResidue_delta_central w hw beta]
  by_cases hab : a + b = 0 <;> simp only [hab, if_true, if_false, smul_smul, smul_zero] <;> module

end KanadeRussell.Tsuchioka.Fock
