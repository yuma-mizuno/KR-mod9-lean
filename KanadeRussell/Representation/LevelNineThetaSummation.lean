import KanadeRussell.Representation.LevelNineThetaCosets
import KanadeRussell.Infra.PowerSeriesTopology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open PowerSeries PowerSeries.WithPiTopology
open scoped DiscreteUniformity
namespace KanadeRussell.Representation.LevelNineNumeratorMasks
open AffineWeightLattice

abbrev ActiveCoset (k : Fin 3) := {c : CosetPoint // mask k c.r c.s ≠ 0}

/-- All occupied cosets have nonnegative degree, by the actual cone-support theorem. -/
theorem cosetExponent_nonneg (k : Fin 3) (c : ActiveCoset k) : 0 ≤ cosetExponent k c.val := by
  have hq := quadratic_coset k c.val c.property
  have ht : quadratic k c.val.pair.1 c.val.pair.2/9=cosetT k c.val := by omega
  have hc : casimir (labels k) (thetaRoot k c.val.pair)=0 := by
    rw [casimir_coordinates]
    simp [thetaRoot, Matrix.cons_val_two]
    omega
  have hm : candidate k (thetaRoot k c.val.pair) ≠ 0 := by
    simp only [candidate, hc]
    simpa [thetaRoot, Matrix.cons_val_two, mask_coset] using c.property
  have hs := candidate_support k _ hm
  have hd : totalDegree (thetaRoot k c.val.pair)=cosetExponent k c.val := by
    simp [totalDegree, Fin.sum_univ_three, thetaRoot, cosetExponent, CosetPoint.pair]
    simp only [CosetPoint.pair] at ht
    linear_combination 4*ht
  rw [← hd]
  exact Finset.sum_nonneg (fun i _ => hs i)

def cosetMonomial (k : Fin 3) (c : ActiveCoset k) : PowerSeries ℤ :=
  PowerSeries.monomial (cosetExponent k c.val).toNat (mask k c.val.r c.val.s)

def degreeEmbedding (k : Fin 3) (n : ℕ) (c : CosetDegree k n) : ActiveCoset k :=
  ⟨c.val,c.property.1⟩

private theorem degreeEmbedding_injective (k : Fin 3) (n : ℕ) :
    Function.Injective (degreeEmbedding k n) := by
  intro a b h
  apply Subtype.ext
  exact congrArg (fun c : ActiveCoset k => c.val) h

/-- The original integral numerator is the convergent sum of all occupied coset
monomials. Finiteness of every coefficient fiber has been proved, not assumed. -/
theorem hasSum_cosetMonomial (k : Fin 3) : HasSum (cosetMonomial k) (principalNumerator k) := by
  classical
  apply (hasSum_iff_hasSum_coeff ℤ).mpr
  intro n
  have hz : ∀ c ∉ Set.range (degreeEmbedding k n), coeff n (cosetMonomial k c)=0 := by
    intro c hc
    have hn : (cosetExponent k c.val).toNat ≠ n := by
      intro he
      have hnonneg := cosetExponent_nonneg k c
      have he' : cosetExponent k c.val=n := by omega
      exact hc ⟨⟨c.val,c.property,he'⟩,rfl⟩
    simp [cosetMonomial, PowerSeries.coeff_monomial, Ne.symm hn]
  apply ((degreeEmbedding_injective k n).hasSum_iff hz).mp
  rw [coeff_principalNumerator_cosets]
  convert hasSum_fintype (fun c : CosetDegree k n => mask k c.val.r c.val.s) using 1
  funext c
  simp only [Function.comp_apply, cosetMonomial, degreeEmbedding, c.property.2, Int.toNat_natCast]
  simp

end KanadeRussell.Representation.LevelNineNumeratorMasks
