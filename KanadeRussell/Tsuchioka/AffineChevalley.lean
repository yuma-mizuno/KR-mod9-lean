import KanadeRussell.Tsuchioka.ChevalleySerreCoefficients
import KanadeRussell.Tsuchioka.TensorCoordinateIteration

/-! The concrete three-tensor operators give a representation of the
D4^(3) Serre presentation. No defining relation is assumed. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock
attribute [local instance] LieRing.ofAssociativeRing
variable {K : Type*} [Field K] [CharZero K]

noncomputable def chevalleyE (w : K) (i : Fin 3) : Module.End K (Space K) :=
  tensorModeEvaluate w 1 (chevalleyECoordinates w i)
noncomputable def chevalleyF (w : K) (i : Fin 3) : Module.End K (Space K) :=
  tensorModeEvaluate w (-1) (chevalleyFCoordinates w i)
noncomputable def chevalleyH (w : K) (i : Fin 3) : Module.End K (Space K) :=
  tensorModeEvaluate w 0 (chevalleyHCoordinates w i)

theorem chevalley_HH (w : K) (hw : w^4-w^2+1=0) (i j : Fin 3) :
    ⁅chevalleyH w i, chevalleyH w j⁆ = 0 := by
  rw [chevalleyH, chevalleyH, tensorModeEvaluate_lie w hw, chevalley_coordinates_HH w hw, map_zero]

theorem chevalley_HE (w : K) (hw : w^4-w^2+1=0) (i j : Fin 3) :
    ⁅chevalleyH w i, chevalleyE w j⁆ = (affineCartanMatrix i j : K) • chevalleyE w j := by
  rw [chevalleyH, chevalleyE, tensorModeEvaluate_lie w hw, chevalley_coordinates_HE w hw,
    map_smul]
  rfl

theorem chevalley_HF (w : K) (hw : w^4-w^2+1=0) (i j : Fin 3) :
    ⁅chevalleyH w i, chevalleyF w j⁆ = -(affineCartanMatrix i j : K) • chevalleyF w j := by
  rw [chevalleyH, chevalleyF, tensorModeEvaluate_lie w hw, chevalley_coordinates_HF w hw,
    map_smul]
  rfl

theorem chevalley_EF (w : K) (hw : w^4-w^2+1=0) (i j : Fin 3) :
    ⁅chevalleyE w i, chevalleyF w j⁆ = if i=j then chevalleyH w i else 0 := by
  rw [chevalleyE, chevalleyF, tensorModeEvaluate_lie w hw, chevalley_coordinates_EF w hw]
  by_cases hij : i=j <;> simp [hij, chevalleyH]

theorem chevalley_coordinates_serreE (w : K) (hw : w^4-w^2+1=0)
    (i j : Fin 3) (hij : i ≠ j) :
    tensorCoordinateAd w (1) (chevalleyECoordinates w i) (chevalleyECoordinates w j)
      ((-affineCartanMatrix i j).toNat+1) = 0 := by
  fin_cases i <;> fin_cases j <;> try exact (hij rfl).elim
  · change tensorCoordinateAd w (1) (chevalleyECoordinates w 0)
      (chevalleyECoordinates w 1) 2 = 0
    norm_num only [tensorCoordinateAd]
    rw [chevalley_E_step_0_1_1 w hw, chevalley_E_step_0_1_2 w hw]
  · change tensorCoordinateAd w (1) (chevalleyECoordinates w 0)
      (chevalleyECoordinates w 2) 1 = 0
    norm_num only [tensorCoordinateAd]
    rw [chevalley_E_step_0_2_1 w hw]
  · change tensorCoordinateAd w (1) (chevalleyECoordinates w 1)
      (chevalleyECoordinates w 0) 2 = 0
    norm_num only [tensorCoordinateAd]
    rw [chevalley_E_step_1_0_1 w hw, chevalley_E_step_1_0_2 w hw]
  · change tensorCoordinateAd w (1) (chevalleyECoordinates w 1)
      (chevalleyECoordinates w 2) 4 = 0
    norm_num only [tensorCoordinateAd]
    rw [chevalley_E_step_1_2_1 w hw, chevalley_E_step_1_2_2 w hw, chevalley_E_step_1_2_3 w hw, chevalley_E_step_1_2_4 w hw]
  · change tensorCoordinateAd w (1) (chevalleyECoordinates w 2)
      (chevalleyECoordinates w 0) 1 = 0
    norm_num only [tensorCoordinateAd]
    rw [chevalley_E_step_2_0_1 w hw]
  · change tensorCoordinateAd w (1) (chevalleyECoordinates w 2)
      (chevalleyECoordinates w 1) 2 = 0
    norm_num only [tensorCoordinateAd]
    rw [chevalley_E_step_2_1_1 w hw, chevalley_E_step_2_1_2 w hw]

theorem chevalley_serreE (w : K) (hw : w^4-w^2+1=0) (i j : Fin 3) :
    ((LieAlgebra.ad K (Module.End K (Space K)) (chevalleyE w i))^
      (-affineCartanMatrix i j).toNat) ⁅chevalleyE w i, chevalleyE w j⁆ = 0 := by
  by_cases hij : i=j
  · subst j
    simp only [lie_self, map_zero]
  · have h := tensorModeEvaluate_ad w hw (1)
      (chevalleyECoordinates w i) (chevalleyECoordinates w j)
      ((-affineCartanMatrix i j).toNat+1)
    rw [chevalley_coordinates_serreE w hw i j hij, map_zero] at h
    simpa only [pow_succ, Module.End.mul_apply, LieAlgebra.ad_apply, chevalleyE] using h.symm

theorem chevalley_coordinates_serreF (w : K) (hw : w^4-w^2+1=0)
    (i j : Fin 3) (hij : i ≠ j) :
    tensorCoordinateAd w (-1) (chevalleyFCoordinates w i) (chevalleyFCoordinates w j)
      ((-affineCartanMatrix i j).toNat+1) = 0 := by
  fin_cases i <;> fin_cases j <;> try exact (hij rfl).elim
  · change tensorCoordinateAd w (-1) (chevalleyFCoordinates w 0)
      (chevalleyFCoordinates w 1) 2 = 0
    norm_num only [tensorCoordinateAd]
    rw [chevalley_F_step_0_1_1 w hw, chevalley_F_step_0_1_2 w hw]
  · change tensorCoordinateAd w (-1) (chevalleyFCoordinates w 0)
      (chevalleyFCoordinates w 2) 1 = 0
    norm_num only [tensorCoordinateAd]
    rw [chevalley_F_step_0_2_1 w hw]
  · change tensorCoordinateAd w (-1) (chevalleyFCoordinates w 1)
      (chevalleyFCoordinates w 0) 2 = 0
    norm_num only [tensorCoordinateAd]
    rw [chevalley_F_step_1_0_1 w hw, chevalley_F_step_1_0_2 w hw]
  · change tensorCoordinateAd w (-1) (chevalleyFCoordinates w 1)
      (chevalleyFCoordinates w 2) 4 = 0
    norm_num only [tensorCoordinateAd]
    rw [chevalley_F_step_1_2_1 w hw, chevalley_F_step_1_2_2 w hw, chevalley_F_step_1_2_3 w hw, chevalley_F_step_1_2_4 w hw]
  · change tensorCoordinateAd w (-1) (chevalleyFCoordinates w 2)
      (chevalleyFCoordinates w 0) 1 = 0
    norm_num only [tensorCoordinateAd]
    rw [chevalley_F_step_2_0_1 w hw]
  · change tensorCoordinateAd w (-1) (chevalleyFCoordinates w 2)
      (chevalleyFCoordinates w 1) 2 = 0
    norm_num only [tensorCoordinateAd]
    rw [chevalley_F_step_2_1_1 w hw, chevalley_F_step_2_1_2 w hw]

theorem chevalley_serreF (w : K) (hw : w^4-w^2+1=0) (i j : Fin 3) :
    ((LieAlgebra.ad K (Module.End K (Space K)) (chevalleyF w i))^
      (-affineCartanMatrix i j).toNat) ⁅chevalleyF w i, chevalleyF w j⁆ = 0 := by
  by_cases hij : i=j
  · subst j
    simp only [lie_self, map_zero]
  · have h := tensorModeEvaluate_ad w hw (-1)
      (chevalleyFCoordinates w i) (chevalleyFCoordinates w j)
      ((-affineCartanMatrix i j).toNat+1)
    rw [chevalley_coordinates_serreF w hw i j hij, map_zero] at h
    simpa only [pow_succ, Module.End.mul_apply, LieAlgebra.ad_apply, chevalleyF] using h.symm

/-- All six relation families have been proved for the constructed tensor operators. -/
noncomputable def affineTensorSerreSystem (w : K) (hw : w^4-w^2+1=0) :
    SerreSystem K (Fin 3) affineCartanMatrix (Module.End K (Space K)) where
  H := chevalleyH w
  E := chevalleyE w
  F := chevalleyF w
  HH := chevalley_HH w hw
  EF := chevalley_EF w hw
  HE i j := (chevalley_HE w hw i j).trans
    (Int.cast_smul_eq_zsmul K (affineCartanMatrix i j) (chevalleyE w j))
  HF i j := (chevalley_HF w hw i j).trans <|
    (neg_smul (affineCartanMatrix i j : K) (chevalleyF w j)).trans <|
      congrArg Neg.neg (Int.cast_smul_eq_zsmul K (affineCartanMatrix i j) (chevalleyF w j))
  adE := chevalley_serreE w hw
  adF := chevalley_serreF w hw

/-- The Lie algebra action through the source affine Cartan matrix's Serre quotient. -/
noncomputable def affineTensorRepresentation (w : K) (hw : w^4-w^2+1=0) :
    Matrix.ToLieAlgebra K affineCartanMatrix →ₗ⁅K⁆ Module.End K (Space K) :=
  (affineTensorSerreSystem w hw).representation

@[simp] theorem affineTensorRepresentation_E (w : K) (hw : w^4-w^2+1=0) (i : Fin 3) :
    affineTensorRepresentation w hw (LieSubmodule.Quotient.mk
      (FreeLieAlgebra.of K (CartanMatrix.Generators.E i))) = chevalleyE w i :=
  (affineTensorSerreSystem w hw).representation_generator (.E i)

@[simp] theorem affineTensorRepresentation_F (w : K) (hw : w^4-w^2+1=0) (i : Fin 3) :
    affineTensorRepresentation w hw (LieSubmodule.Quotient.mk
      (FreeLieAlgebra.of K (CartanMatrix.Generators.F i))) = chevalleyF w i :=
  (affineTensorSerreSystem w hw).representation_generator (.F i)

@[simp] theorem affineTensorRepresentation_H (w : K) (hw : w^4-w^2+1=0) (i : Fin 3) :
    affineTensorRepresentation w hw (LieSubmodule.Quotient.mk
      (FreeLieAlgebra.of K (CartanMatrix.Generators.H i))) = chevalleyH w i :=
  (affineTensorSerreSystem w hw).representation_generator (.H i)

end KanadeRussell.Tsuchioka.Fock
