import KanadeRussell.Heisenberg.FiniteVacuumGrading
import KanadeRussell.Heisenberg.GradeRecurrence

/-! Each finite family of oscillator kernels multiplies the graded character
by the corresponding finite Euler product. -/
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Heisenberg.GradedSystem
open PowerSeries
variable {K V ι : Type*} [Field K] [CharZero K]
  [AddCommGroup V] [Module K V]
variable (G : GradedSystem K V ι)

noncomputable def character : PowerSeries ℤ :=
  PowerSeries.mk fun n => (Module.finrank K (G.grade (n : ℤ)) : ℤ)

noncomputable def finiteVacuumCharacter (s : Finset ι) : PowerSeries ℤ :=
  PowerSeries.mk fun n =>
    (Module.finrank K (G.grade (n : ℤ) ⊓ G.finiteVacuum s : Submodule K V) : ℤ)

noncomputable def vacuumCharacter : PowerSeries ℤ :=
  PowerSeries.mk fun n =>
    (Module.finrank K (G.grade (n : ℤ) ⊓ vacuum G.annihilate : Submodule K V) : ℤ)

@[simp] theorem finiteVacuumCharacter_empty : G.finiteVacuumCharacter ∅ = G.character := by
  ext n
  simp only [finiteVacuumCharacter, character, coeff_mk]
  rw [G.finiteVacuum_empty, inf_top_eq]

theorem one_sub_X_pow_mul_finiteVacuumCharacter [DecidableEq ι]
    (hfin : ∀ d : ℤ, Module.Finite K (G.grade d)) (s : Finset ι) (i : ι) (hi : i ∉ s) :
    (1 - (PowerSeries.X : PowerSeries ℤ) ^ G.weight i) * G.finiteVacuumCharacter s =
      G.finiteVacuumCharacter (insert i s) := by
  ext n
  letI := hfin (n : ℤ)
  letI := G.awayFrom_grade_finite s (n : ℤ)
  have hd := (G.awayFrom s).finrank_grade_eq_ker_add ⟨i, hi⟩ (n : ℤ)
  rw [G.awayFrom_grade_finrank, G.awayFrom_grade_ker_finrank,
    G.awayFrom_grade_finrank] at hd
  change Module.finrank K (G.grade (n : ℤ) ⊓ G.finiteVacuum s : Submodule K V) =
    Module.finrank K (G.grade (n : ℤ) ⊓ G.finiteVacuum (insert i s) : Submodule K V) +
    Module.finrank K (G.grade ((n : ℤ) - G.weight i) ⊓ G.finiteVacuum s : Submodule K V) at hd
  rw [sub_mul, one_mul, map_sub, coeff_X_pow_mul']
  simp only [finiteVacuumCharacter, coeff_mk]
  by_cases hn : G.weight i ≤ n
  · rw [if_pos hn]
    have he : (n : ℤ) - G.weight i = ((n - G.weight i : ℕ) : ℤ) := by omega
    rw [he] at hd
    have hz := congrArg (fun x : ℕ => (x : ℤ)) hd
    push_cast at hz
    omega
  · rw [if_neg hn, sub_zero]
    have he : (n : ℤ) - G.weight i < 0 := by omega
    rw [G.negative _ he, bot_inf_eq, finrank_bot, add_zero] at hd
    exact congrArg (fun x : ℕ => (x : ℤ)) hd

theorem prod_one_sub_X_pow_mul_character
    (hfin : ∀ d : ℤ, Module.Finite K (G.grade d)) (s : Finset ι) :
    (∏ i ∈ s, (1 - (PowerSeries.X : PowerSeries ℤ) ^ G.weight i)) * G.character =
      G.finiteVacuumCharacter s := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, mul_assoc, ih,
      G.one_sub_X_pow_mul_finiteVacuumCharacter hfin s i hi]

theorem coeff_finiteVacuumCharacter_eq_vacuumCharacter (s : Finset ι) (n : ℕ)
    (hs : ∀ i, G.weight i ≤ n → i ∈ s) :
    coeff n (G.finiteVacuumCharacter s) = coeff n G.vacuumCharacter := by
  simp only [finiteVacuumCharacter, vacuumCharacter, coeff_mk]
  rw [G.finiteVacuum_grade_eq_vacuum s (n : ℤ) (by
    intro i hi
    exact hs i (by exact_mod_cast hi))]

end KanadeRussell.Heisenberg.GradedSystem
