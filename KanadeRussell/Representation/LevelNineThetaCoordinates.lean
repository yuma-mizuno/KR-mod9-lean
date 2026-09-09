import KanadeRussell.Representation.PrincipalMaskNumerators
import KanadeRussell.Representation.ConcreteRootNumeratorMasks
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KanadeRussell.Representation.LevelNineNumeratorMasks
open AffineWeightLattice

/-- The nonzero summands of the finite principal coefficient. -/
abbrev OccupiedDegree (k : Fin 3) (n : ℕ) :=
  {b : PrincipalDegreeOccupation n // candidate k b.root ≠ 0}

/-- Integer rank-two points on the integral shell and fixed principal degree. -/
abbrev ThetaDegree (k : Fin 3) (n : ℕ) :=
  {p : ℤ × ℤ // mask k p.1 p.2 ≠ 0 ∧
    quadratic k p.1 p.2 = 9*(quadratic k p.1 p.2/9) ∧
    p.1+p.2+4*(quadratic k p.1 p.2/9) = n}

def thetaRoot (k : Fin 3) (p : ℤ × ℤ) : RootCoefficients :=
  ![quadratic k p.1 p.2/9+p.1, 2*(quadratic k p.1 p.2/9)+p.2, quadratic k p.1 p.2/9]

private theorem occupied_casimir (k : Fin 3) (n : ℕ) (b : OccupiedDegree k n) :
    casimir (labels k) b.val.root=0 := by
  by_contra h
  have := b.property
  simp [candidate, h] at this

def toThetaDegree (k : Fin 3) (n : ℕ) (b : OccupiedDegree k n) : ThetaDegree k n := by
  let x := b.val.root 0-b.val.root 2
  let y := b.val.root 1-2*b.val.root 2
  have ht : quadratic k x y=9*b.val.root 2 := by
    have hc := occupied_casimir k n b
    rw [casimir_coordinates] at hc
    dsimp [x,y]
    omega
  have ht' : quadratic k x y/9=b.val.root 2 := by omega
  refine ⟨(x,y), ?_, ?_, ?_⟩
  · simpa only [candidate, occupied_casimir k n b, if_true] using b.property
  · change quadratic k x y=9*(quadratic k x y/9)
    omega
  · have hd := b.val.root_degree
    simp only [totalDegree, Fin.sum_univ_three] at hd
    dsimp [x,y]
    rw [ht']
    omega

 theorem thetaRoot_casimir (k : Fin 3) (n : ℕ) (p : ThetaDegree k n) :
    casimir (labels k) (thetaRoot k p.val)=0 := by
  rw [casimir_coordinates]
  simp only [thetaRoot, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail, Function.comp_apply]
  change quadratic k ((quadratic k p.val.1 p.val.2/9+p.val.1)-quadratic k p.val.1 p.val.2/9)
    ((2*(quadratic k p.val.1 p.val.2/9)+p.val.2)-2*(quadratic k p.val.1 p.val.2/9))-
      9*(quadratic k p.val.1 p.val.2/9)=0
  simp only [add_sub_cancel_left]
  exact sub_eq_zero.mpr p.property.2.1

 theorem thetaRoot_candidate (k : Fin 3) (n : ℕ) (p : ThetaDegree k n) :
    candidate k (thetaRoot k p.val)=mask k p.val.1 p.val.2 := by
  simp only [candidate, thetaRoot_casimir]
  simp [thetaRoot, Matrix.cons_val_two]

 theorem thetaRoot_degree (k : Fin 3) (n : ℕ) (p : ThetaDegree k n) :
    totalDegree (thetaRoot k p.val)=n := by
  simp [totalDegree, Fin.sum_univ_three, thetaRoot]
  linear_combination p.property.2.2

 theorem toThetaDegree_bijective (k : Fin 3) (n : ℕ) : Function.Bijective (toThetaDegree k n) := by
  constructor
  · intro a b h
    apply Subtype.ext
    apply PrincipalDegreeOccupation.root_injective n
    have hp := congrArg Subtype.val h
    have hx := congrArg Prod.fst hp
    have hy := congrArg Prod.snd hp
    change a.val.root 0-a.val.root 2=b.val.root 0-b.val.root 2 at hx
    change a.val.root 1-2*a.val.root 2=b.val.root 1-2*b.val.root 2 at hy
    have ha := a.val.root_degree
    have hb := b.val.root_degree
    simp only [totalDegree, Fin.sum_univ_three] at ha hb
    have h0 : a.val.root 0=b.val.root 0 := by omega
    have h1 : a.val.root 1=b.val.root 1 := by omega
    have h2 : a.val.root 2=b.val.root 2 := by omega
    ext i
    fin_cases i <;> first | exact h0 | exact h1 | exact h2
  · intro p
    have hm : candidate k (thetaRoot k p.val) ≠ 0 := by rw [thetaRoot_candidate]; exact p.property.1
    obtain ⟨b,hb⟩ := PrincipalDegreeOccupation.exists_root n (thetaRoot k p.val)
      (candidate_support k _ hm) (thetaRoot_degree k n p)
    refine ⟨⟨b, by simpa only [hb] using hm⟩, ?_⟩
    apply Subtype.ext
    change (b.root 0-b.root 2,b.root 1-2*b.root 2)=p.val
    rw [hb]
    simp [thetaRoot, Matrix.cons_val_two]

def occupiedDegreeEquivTheta (k : Fin 3) (n : ℕ) : OccupiedDegree k n ≃ ThetaDegree k n :=
  Equiv.ofBijective (toThetaDegree k n) (toThetaDegree_bijective k n)

instance thetaDegreeFintype (k : Fin 3) (n : ℕ) : Fintype (ThetaDegree k n) :=
  Fintype.ofEquiv (OccupiedDegree k n) (occupiedDegreeEquivTheta k n)

/-- Every principal coefficient is an exact finite rank-two theta-fiber sum. -/
theorem principal_coefficient_eq_theta (k : Fin 3) (n : ℕ) :
    (∑ b : PrincipalDegreeOccupation n, candidate k b.root) =
      ∑ p : ThetaDegree k n, mask k p.val.1 p.val.2 := by
  classical
  have hs := Fintype.sum_subtype_add_sum_subtype
    (fun b : PrincipalDegreeOccupation n => candidate k b.root ≠ 0) (fun b => candidate k b.root)
  have hz : (∑ b : {b : PrincipalDegreeOccupation n // ¬ candidate k b.root ≠ 0}, candidate k b.val.root)=0 := by
    apply Finset.sum_eq_zero
    intro b hb
    exact not_ne_iff.mp b.property
  rw [hz, add_zero] at hs
  rw [← hs]
  apply Fintype.sum_equiv (occupiedDegreeEquivTheta k n)
  intro b
  change candidate k b.val.root = mask k (b.val.root 0-b.val.root 2) (b.val.root 1-2*b.val.root 2)
  simp only [candidate, occupied_casimir k n b, if_true]

 theorem coeff_principalNumerator_theta (k : Fin 3) (n : ℕ) :
    PowerSeries.coeff n (principalNumerator k) =
      ∑ p : ThetaDegree k n, mask k p.val.1 p.val.2 := by
  rw [coeff_principalNumerator, principal_coefficient_eq_theta]

end KanadeRussell.Representation.LevelNineNumeratorMasks
