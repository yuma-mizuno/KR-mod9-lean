import Mathlib.Algebra.Lie.SerreConstruction

/-! The universal property of the Serre presentation used below.
A system satisfying all six defining families yields an actual Lie algebra homomorphism. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka

variable {R I L : Type*} [CommRing R] [DecidableEq I] [LieRing L] [LieAlgebra R L]

/-- All defining relations of the integer-matrix Serre presentation. -/
structure SerreSystem (R : Type*) [CommRing R] (I : Type*) [DecidableEq I]
    (A : Matrix I I ℤ) (L : Type*) [LieRing L] [LieAlgebra R L] where
  H : I → L
  E : I → L
  F : I → L
  HH : ∀ i j, ⁅H i, H j⁆ = 0
  EF : ∀ i j, ⁅E i, F j⁆ = if i=j then H i else 0
  HE : ∀ i j, ⁅H i, E j⁆ = A i j • E j
  HF : ∀ i j, ⁅H i, F j⁆ = -(A i j • F j)
  adE : ∀ i j, ((LieAlgebra.ad R L (E i)) ^ (-A i j).toNat) ⁅E i, E j⁆ = 0
  adF : ∀ i j, ((LieAlgebra.ad R L (F i)) ^ (-A i j).toNat) ⁅F i, F j⁆ = 0

namespace SerreSystem

variable {A : Matrix I I ℤ} (S : SerreSystem R I A L)

def generator : CartanMatrix.Generators I → L
  | .H i => S.H i
  | .E i => S.E i
  | .F i => S.F i

noncomputable def freeMap : FreeLieAlgebra R (CartanMatrix.Generators I) →ₗ⁅R⁆ L :=
  FreeLieAlgebra.lift R S.generator

@[simp] theorem freeMap_of (g : CartanMatrix.Generators I) :
    S.freeMap (FreeLieAlgebra.of R g) = S.generator g :=
  FreeLieAlgebra.lift_of_apply S.generator g

theorem map_ad_power {L' : Type*} [LieRing L'] [LieAlgebra R L']
    (f : L →ₗ⁅R⁆ L') (x y : L) (n : ℕ) :
    f (((LieAlgebra.ad R L x)^n) y) =
      ((LieAlgebra.ad R L' (f x))^n) (f y) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ', Module.End.mul_apply, LieAlgebra.ad_apply, LieHom.map_lie, ih]

theorem relations_le_ker : CartanMatrix.Relations.toIdeal R A ≤ S.freeMap.ker := by
  rw [CartanMatrix.Relations.toIdeal, LieSubmodule.lieSpan_le]
  intro x hx
  change S.freeMap x = 0
  simp only [CartanMatrix.Relations.toSet, Set.mem_union, Set.mem_range] at hx
  rcases hx with (((((hx | hx) | hx) | hx) | hx) | hx) <;>
    obtain ⟨p,rfl⟩ := hx <;> rcases p with ⟨i,j⟩
  · simpa [CartanMatrix.Relations.HH, generator] using S.HH i j
  · by_cases hij : i=j
    · subst j
      simp [CartanMatrix.Relations.EF, generator, S.EF]
    · simp [CartanMatrix.Relations.EF, generator, hij, S.EF]
  · simp [CartanMatrix.Relations.HE, generator, S.HE]
  · simp [CartanMatrix.Relations.HF, generator, S.HF]
  · simpa [CartanMatrix.Relations.adE, Function.uncurry, Function.comp_def,
      map_ad_power, generator] using S.adE i j
  · simpa [CartanMatrix.Relations.adF, Function.uncurry, Function.comp_def,
      map_ad_power, generator] using S.adF i j

/-- A checked Serre system acts through the quotient Lie algebra, not just the free algebra. -/
noncomputable def representation : Matrix.ToLieAlgebra R A →ₗ⁅R⁆ L :=
  { (CartanMatrix.Relations.toIdeal R A).toSubmodule.liftQ S.freeMap.toLinearMap
      S.relations_le_ker with
    map_lie' := by
      intro x y
      induction x using Submodule.Quotient.induction_on with
      | H x =>
        induction y using Submodule.Quotient.induction_on with
        | H y => exact S.freeMap.map_lie x y }

@[simp] theorem representation_generator (g : CartanMatrix.Generators I) :
    S.representation (LieSubmodule.Quotient.mk (FreeLieAlgebra.of R g) :
      Matrix.ToLieAlgebra R A) = S.generator g :=
  S.freeMap_of g

end SerreSystem
end KanadeRussell.Tsuchioka
