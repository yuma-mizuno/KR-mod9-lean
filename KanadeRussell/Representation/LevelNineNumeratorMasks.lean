import KanadeRussell.Representation.AffineWeightLattice
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Representation.LevelNineNumeratorMasks
open AffineWeightLattice
open Tsuchioka.Fock

def labels : Fin 3 → RootCoefficients := ![![2,2,1], ![4,1,1], ![1,1,2]]
def positiveResidues : Fin 3 → List (ℤ × ℤ) := ![
  [(0,0),(1,7),(2,4),(4,2),(6,5),(8,3)],
  [(0,0),(3,7),(4,5),(5,1),(7,6),(8,2)],
  [(0,0),(1,2),(2,1),(6,4),(7,3),(8,5)]]
def negativeResidues : Fin 3 → List (ℤ × ℤ) := ![
  [(0,2),(1,5),(2,0),(4,4),(6,3),(8,7)],
  [(0,1),(3,6),(4,0),(5,5),(7,2),(8,7)],
  [(0,1),(1,0),(2,2),(6,3),(7,5),(8,4)]]
def mask (k : Fin 3) (x y : ℤ) : ℤ :=
  if (x%9,y%9) ∈ positiveResidues k then 1 else
    if (x%9,y%9) ∈ negativeResidues k then -1 else 0

def reflectX (k i : Fin 3) (x y : ℤ) : ℤ :=
  ![-x+y+labels k 0, x, x-y-labels k 2] i
def reflectY (k i : Fin 3) (x y : ℤ) : ℤ :=
  ![y, x-y+labels k 1, -y-2*labels k 2] i

theorem mask_periodic (k : Fin 3) (x y x' y' : ℤ)
    (hx : x%9=x'%9) (hy : y%9=y'%9) : mask k x y=mask k x' y' := by
  simp only [mask, hx, hy]

/-- Exact signed reflection covariance on all 81 residue classes. -/
theorem mask_reflection_finite : ∀ (k i : Fin 3) (x y : Fin 9),
    mask k (reflectX k i x y) (reflectY k i x y) = -mask k x y := by decide

/-- The finite residue certificate transports to every integer pair. -/
theorem mask_reflection (k i : Fin 3) (x y : ℤ) :
    mask k (reflectX k i x y) (reflectY k i x y) = -mask k x y := by
  let r : Fin 9 := ⟨(x%9).toNat, by omega⟩
  let s : Fin 9 := ⟨(y%9).toNat, by omega⟩
  have hr : (r : ℤ)=x%9 := by simp [r]; omega
  have hs : (s : ℤ)=y%9 := by simp [s]; omega
  have hX : reflectX k i x y %9 = reflectX k i r s %9 := by
    rw [hr, hs]
    fin_cases i <;> simp [reflectX] <;> omega
  have hY : reflectY k i x y %9 = reflectY k i r s %9 := by
    rw [hr, hs]
    fin_cases i <;> simp [reflectY] <;> omega
  rw [mask_periodic k _ _ _ _ hX hY, mask_reflection_finite]
  congr 1
  apply mask_periodic <;> simp [hr, hs]

/-- Every supported residue lies on the integral level-nine quadratic shell. -/
theorem mask_shell_finite : ∀ (k : Fin 3) (x y : Fin 9), mask k x y ≠ 0 →
    ((x : ℤ)^2+(y : ℤ)^2-x*y-labels k 0*x-labels k 1*y)%9=0 := by decide

@[simp] theorem mask_zero (k : Fin 3) : mask k 0 0=1 := by
  fin_cases k <;> decide

def candidate (k : Fin 3) (beta : RootCoefficients) : ℤ :=
  if casimir (labels k) beta=0 then mask k (beta 0-beta 2) (beta 1-2*beta 2) else 0

@[simp] theorem candidate_zero (k : Fin 3) : candidate k 0=1 := by
  simp [candidate, casimir_eq]

theorem candidate_casimir (k : Fin 3) (beta : RootCoefficients) :
    casimir (labels k) beta * candidate k beta = 0 := by
  unfold candidate
  split_ifs with h <;> simp [h]

private theorem fin_two : (2 : Fin 3)=⟨2, by decide⟩ := by decide

private theorem projection_reflectionX (nu beta : RootCoefficients) (i : Fin 3) :
    (simpleReflection nu i beta) 0-(simpleReflection nu i beta) 2 =
      ![-(beta 0-beta 2)+(beta 1-2*beta 2)+nu 0,
        beta 0-beta 2, (beta 0-beta 2)-(beta 1-2*beta 2)-nu 2] i := by
  fin_cases i <;> norm_num [simpleReflection, weightLabels, Fin.sum_univ_three,
    affineCartanMatrix, Pi.single_apply, Matrix.cons_val_two] <;> norm_num [Fin.ext_iff] <;> simp only [fin_two] <;> ring

private theorem projection_reflectionY (nu beta : RootCoefficients) (i : Fin 3) :
    (simpleReflection nu i beta) 1-2*(simpleReflection nu i beta) 2 =
      ![beta 1-2*beta 2, (beta 0-beta 2)-(beta 1-2*beta 2)+nu 1,
        -(beta 1-2*beta 2)-2*nu 2] i := by
  fin_cases i <;> norm_num [simpleReflection, weightLabels, Fin.sum_univ_three,
    affineCartanMatrix, Pi.single_apply, Matrix.cons_val_two] <;> norm_num [Fin.ext_iff] <;> simp only [fin_two] <;> ring

/-- These explicit shell candidates are antisymmetric for the actual three
shifted highest weights and the actual Cartan reflections. -/
theorem candidate_reflection (k i : Fin 3) (beta : RootCoefficients) :
    candidate k (simpleReflection (labels k) i beta) = -candidate k beta := by
  unfold candidate
  rw [casimir_simpleReflection]
  split_ifs
  · rw [projection_reflectionX, projection_reflectionY]
    exact mask_reflection k i _ _
  · simp

/-- A complete bound for a negative rank-two quadratic with bounded linear coefficients. -/
theorem negative_quadratic_bound (x y A B : ℤ) (hA : -8 ≤ A ∧ A ≤ 8)
    (hB : -8 ≤ B ∧ B ≤ 8) (h : x^2+y^2-x*y+A*x+B*y < 0) :
    -32 < x ∧ x < 32 ∧ -32 < y ∧ y < 32 := by
  have hA2 : A^2 ≤ 64 := by nlinarith
  have hB2 : B^2 ≤ 64 := by nlinarith
  have hsq : x^2+y^2 < 512 := by
    nlinarith [sq_nonneg (x-y), sq_nonneg (x+2*A), sq_nonneg (y+2*B)]
  constructor
  · by_contra hx
    have hx' : x ≤ -32 := by omega
    nlinarith [sq_nonneg y]
  constructor
  · by_contra hx
    have hx' : 32 ≤ x := by omega
    nlinarith [sq_nonneg y]
  constructor
  · by_contra hy
    have hy' : y ≤ -32 := by omega
    nlinarith [sq_nonneg x]
  · by_contra hy
    have hy' : 32 ≤ y := by omega
    nlinarith [sq_nonneg x]

def quadratic (k : Fin 3) (x y : ℤ) : ℤ :=
  x^2+y^2-x*y-labels k 0*x-labels k 1*y

theorem casimir_coordinates (k : Fin 3) (beta : RootCoefficients) :
    casimir (labels k) beta = quadratic k (beta 0-beta 2) (beta 1-2*beta 2)-9*beta 2 := by
  fin_cases k <;> norm_num [casimir_eq, quadratic, labels, Matrix.cons_val_two] <;> ring

private theorem shell_negative_bound (k : Fin 3) (x y t : ℤ)
    (ht : quadratic k x y=9*t) (hb : t<0 ∨ t+x<0 ∨ 2*t+y<0) :
    -32<x ∧ x<32 ∧ -32<y ∧ y<32 := by
  have hnu : 1 ≤ labels k 0 ∧ labels k 0 ≤ 4 ∧ 1 ≤ labels k 1 ∧ labels k 1 ≤ 2 := by
    fin_cases k <;> decide
  have hq : 0 ≤ x^2+y^2-x*y := by nlinarith [sq_nonneg (x-y), sq_nonneg x, sq_nonneg y]
  unfold quadratic at ht
  rcases hb with hb | hb | hb
  · apply negative_quadratic_bound x y (-labels k 0) (-labels k 1) (by omega) (by omega)
    nlinarith
  · apply negative_quadratic_bound x y (9-labels k 0) (-labels k 1) (by omega) (by omega)
    nlinarith
  · apply negative_quadratic_bound x y (-2*labels k 0) (9-2*labels k 1) (by omega) (by omega)
    nlinarith

set_option maxRecDepth 100000 in
/-- A complete check on the bounded region where cone failure could occur. -/
theorem cone_box : ∀ (k : Fin 3) (r s : Fin 63),
    mask k ((r : ℤ)-31) ((s : ℤ)-31) ≠ 0 →
      0 ≤ quadratic k ((r : ℤ)-31) ((s : ℤ)-31) ∧
      0 ≤ quadratic k ((r : ℤ)-31) ((s : ℤ)-31)+9*((r : ℤ)-31) ∧
      0 ≤ 2*quadratic k ((r : ℤ)-31) ((s : ℤ)-31)+9*((s : ℤ)-31) := by decide

/-- The explicit signed shell candidate is supported in the actual positive root cone. -/
theorem candidate_support (k : Fin 3) (beta : RootCoefficients) (hn : candidate k beta ≠ 0) :
    ∀ i, 0 ≤ beta i := by
  have hc : casimir (labels k) beta=0 := by
    by_contra h
    simp [candidate, h] at hn
  have hm : mask k (beta 0-beta 2) (beta 1-2*beta 2) ≠ 0 := by simpa [candidate, hc] using hn
  have ht : quadratic k (beta 0-beta 2) (beta 1-2*beta 2)=9*beta 2 := by
    rw [casimir_coordinates] at hc
    omega
  intro i
  by_contra hneg
  have hb : beta 2<0 ∨ beta 2+(beta 0-beta 2)<0 ∨ 2*beta 2+(beta 1-2*beta 2)<0 := by
    fin_cases i <;> simp only [Fin.reduceFinMk] at hneg <;> omega
  obtain ⟨hx0,hx1,hy0,hy1⟩ := shell_negative_bound k _ _ _ ht hb
  let r : Fin 63 := ⟨(beta 0-beta 2+31).toNat, by omega⟩
  let s : Fin 63 := ⟨(beta 1-2*beta 2+31).toNat, by omega⟩
  have hr : (r : ℤ)-31=beta 0-beta 2 := by simp only [r]; omega
  have hs : (s : ℤ)-31=beta 1-2*beta 2 := by simp only [s]; omega
  have hh := cone_box k r s
  rw [hr, hs] at hh
  obtain ⟨h0,h1,h2⟩ := hh hm
  omega

end KanadeRussell.Representation.LevelNineNumeratorMasks
