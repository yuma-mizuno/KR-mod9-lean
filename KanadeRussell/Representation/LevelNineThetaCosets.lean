import KanadeRussell.Representation.LevelNineThetaCoordinates
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KanadeRussell.Representation.LevelNineNumeratorMasks

/-- Euclidean residue and translation coordinates for the rank-two lattice. -/
@[ext] structure CosetPoint where
  r : Fin 9
  s : Fin 9
  m : ℤ
  l : ℤ
  deriving DecidableEq

def CosetPoint.pair (c : CosetPoint) : ℤ × ℤ := (9*c.m+c.r,9*c.l+c.s)

def pairCoset (p : ℤ × ℤ) : CosetPoint where
  r := ⟨(p.1%9).toNat, by omega⟩
  s := ⟨(p.2%9).toNat, by omega⟩
  m := p.1/9
  l := p.2/9

def cosetEquivPair : CosetPoint ≃ ℤ × ℤ where
  toFun := CosetPoint.pair
  invFun := pairCoset
  left_inv c := by
    cases c with
    | mk r s m l =>
      apply CosetPoint.ext
      · apply Fin.ext
        simp only [pairCoset, CosetPoint.pair]
        omega
      · apply Fin.ext
        simp only [pairCoset, CosetPoint.pair]
        omega
      · simp only [pairCoset, CosetPoint.pair]
        omega
      · simp only [pairCoset, CosetPoint.pair]
        omega
  right_inv p := by
    apply Prod.ext <;> simp only [CosetPoint.pair, pairCoset] <;> omega

/-- The integral shell coordinate after extracting a residue class. -/
def cosetT (k : Fin 3) (c : CosetPoint) : ℤ :=
  9*(c.m^2+c.l^2-c.m*c.l)+(2*(c.r : ℤ)-c.s-labels k 0)*c.m+
    (2*(c.s : ℤ)-c.r-labels k 1)*c.l+quadratic k c.r c.s/9

def cosetExponent (k : Fin 3) (c : CosetPoint) : ℤ :=
  (c.r : ℤ)+c.s+9*(c.m+c.l)+4*cosetT k c

theorem cosetExponent_expanded (k : Fin 3) (c : CosetPoint) :
    cosetExponent k c = 36*(c.m^2+c.l^2-c.m*c.l)+
      (8*(c.r : ℤ)-4*c.s+9-4*labels k 0)*c.m+
      (8*(c.s : ℤ)-4*c.r+9-4*labels k 1)*c.l+
      (c.r : ℤ)+c.s+4*(quadratic k c.r c.s/9) := by
  unfold cosetExponent cosetT
  ring

theorem mask_coset (k : Fin 3) (c : CosetPoint) :
    mask k c.pair.1 c.pair.2 = mask k c.r c.s := by
  apply mask_periodic <;> simp only [CosetPoint.pair] <;> omega

/-- The residue shell congruence gives an exact integral quadratic lift. -/
theorem quadratic_coset (k : Fin 3) (c : CosetPoint) (hc : mask k c.r c.s ≠ 0) :
    quadratic k c.pair.1 c.pair.2=9*cosetT k c := by
  have hr := mask_shell_finite k c.r c.s hc
  change quadratic k c.r c.s %9=0 at hr
  have hq : quadratic k c.r c.s=9*(quadratic k c.r c.s/9) := by omega
  simp only [quadratic, CosetPoint.pair, cosetT] at hq ⊢
  linear_combination hq

abbrev CosetDegree (k : Fin 3) (n : ℕ) :=
  {c : CosetPoint // mask k c.r c.s ≠ 0 ∧ cosetExponent k c=n}

private theorem coset_condition (k : Fin 3) (n : ℕ) (c : CosetPoint) :
    (mask k c.r c.s ≠ 0 ∧ cosetExponent k c=n) ↔
      (mask k c.pair.1 c.pair.2 ≠ 0 ∧
        quadratic k c.pair.1 c.pair.2=9*(quadratic k c.pair.1 c.pair.2/9) ∧
        c.pair.1+c.pair.2+4*(quadratic k c.pair.1 c.pair.2/9)=n) := by
  rw [mask_coset]
  constructor
  · rintro ⟨hm,hd⟩
    have hq := quadratic_coset k c hm
    have ht : quadratic k c.pair.1 c.pair.2/9=cosetT k c := by omega
    refine ⟨hm, by omega, ?_⟩
    rw [ht]
    simp only [cosetExponent, CosetPoint.pair] at hd ⊢
    linear_combination hd
  · rintro ⟨hm,hq,hd⟩
    have ht : quadratic k c.pair.1 c.pair.2/9=cosetT k c := by
      have he := quadratic_coset k c hm
      omega
    refine ⟨hm, ?_⟩
    rw [ht] at hd
    simp only [cosetExponent, CosetPoint.pair] at hd ⊢
    linear_combination hd

/-- Exact fiber bijection, not merely a match of finitely many coefficients. -/
def cosetDegreeEquivTheta (k : Fin 3) (n : ℕ) : CosetDegree k n ≃ ThetaDegree k n :=
  cosetEquivPair.subtypeEquiv (coset_condition k n)

instance cosetDegreeFintype (k : Fin 3) (n : ℕ) : Fintype (CosetDegree k n) :=
  Fintype.ofEquiv (ThetaDegree k n) (cosetDegreeEquivTheta k n).symm

/-- Exactly twelve residue classes carry the signs of each numerator. -/
theorem active_residue_count (k : Fin 3) :
    Fintype.card {r : Fin 9 × Fin 9 // mask k r.1 r.2 ≠ 0}=12 := by
  fin_cases k <;> decide

/-- The actual mask numerator coefficient is its twelve-coset rank-two theta sum. -/
theorem coeff_principalNumerator_cosets (k : Fin 3) (n : ℕ) :
    PowerSeries.coeff n (principalNumerator k) =
      ∑ c : CosetDegree k n, mask k c.val.r c.val.s := by
  rw [coeff_principalNumerator_theta]
  apply Fintype.sum_equiv (cosetDegreeEquivTheta k n).symm
  intro p
  have he := (cosetDegreeEquivTheta k n).apply_symm_apply p
  have hp := congrArg Subtype.val he
  change ((cosetDegreeEquivTheta k n).symm p).val.pair=p.val at hp
  rw [← hp]
  exact mask_coset k _

end KanadeRussell.Representation.LevelNineNumeratorMasks
