import KanadeRussell.Tsuchioka.TensorLieCoordinates

/-! The principal derivation on arbitrary finite tensor-mode coordinates. -/

set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Tsuchioka.Fock
attribute [local instance] LieRing.ofAssociativeRing
variable {K : Type*} [Field K] [CharZero K]

theorem principalDerivation_tensorModeEvaluate_lie (w : K) (a : ℤ) (v : Fin 4 → K) :
    ⁅principalDerivation (K := K), tensorModeEvaluate w a v⁆ =
      (a : K) • tensorModeEvaluate w a v -
        ((a : K) * v 3) • (1 : Module.End K (Space K)) := by
  calc
    _ = v 0 • ⁅principalDerivation (K := K), tensorRootMode w (RootData.simpleRoot 0) a⁆ +
        v 1 • ⁅principalDerivation (K := K), tensorRootMode w (RootData.simpleRoot 1) a⁆ +
        v 2 • ⁅principalDerivation (K := K), heisenbergMode w a⁆ := by
      simp only [tensorModeEvaluate_apply, Ring.lie_def, mul_add, add_mul,
        Algebra.mul_smul_comm, Algebra.smul_mul_assoc, mul_one, one_mul]
      module
    _ = _ := by
      rw [principalDerivation_tensorRootMode_lie, principalDerivation_tensorRootMode_lie,
        principalDerivation_heisenbergMode_lie, tensorModeEvaluate_apply]
      module

end KanadeRussell.Tsuchioka.Fock
