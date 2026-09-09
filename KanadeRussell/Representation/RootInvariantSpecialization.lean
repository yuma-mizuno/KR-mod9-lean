import KanadeRussell.Representation.RootInvariantNullSupport
import KanadeRussell.Representation.RootPrincipalSpecialization
import KanadeRussell.Representation.RootCoefficientFunction

/-! Principal specialization is injective on reflection-invariant multivariate
series: their support lies on the null ray, with one root at each degree 4n. -/
set_option autoImplicit false
namespace KanadeRussell.Representation
open AffineWeightLattice
variable {K : Type*} [Field K]

private theorem null_degree (n : ℕ) : totalDegree ((n : ℤ) • marks) = (4*n : ℕ) := by
  norm_num [totalDegree, marks, Fin.sum_univ_three, Matrix.cons_val_two]
  ring

/-- A null-ray coefficient is exactly the corresponding principal coefficient. -/
theorem coeff_rootPrincipalSpecialization_of_invariant (f : MvPowerSeries (Fin 3) K)
    (hf : ∀ i beta, rootCoefficient f (simpleReflection 0 i beta) = rootCoefficient f beta)
    (n : ℕ) :
    PowerSeries.coeff (4*n) (rootPrincipalSpecialization f) =
      rootCoefficient f ((n : ℤ) • marks) := by
  classical
  have hnonneg : ∀ i, 0 ≤ ((n : ℤ) • marks) i := by
    intro i
    fin_cases i <;> norm_num [marks, Matrix.cons_val_two]
  obtain ⟨b, hb⟩ := PrincipalDegreeOccupation.exists_root (4*n) ((n : ℤ) • marks) hnonneg (null_degree n)
  rw [coeff_rootPrincipalSpecialization]
  have hcoeff (p : PrincipalDegreeOccupation (4*n)) :
      MvPowerSeries.coeff p.exponent f = rootCoefficient f p.root := by
    rw [← p.exponent_root, rootCoefficient_ofExponent]
  calc
    _ = ∑ p : PrincipalDegreeOccupation (4*n), rootCoefficient f p.root :=
      Finset.sum_congr rfl (fun p _ => hcoeff p)
    _ = rootCoefficient f b.root := by
      apply Finset.sum_eq_single b
      · intro p hp hpb
        by_contra hn
        obtain ⟨m, hm⟩ := invariant_nonzero_eq_nat_smul_marks (rootCoefficient f)
          (rootCoefficient_of_not_nonneg f) hf p.root hn
        have hd := p.root_degree
        rw [hm, null_degree] at hd
        have hmn : m = n := by omega
        apply hpb
        apply PrincipalDegreeOccupation.root_injective (4*n)
        rw [hm, hmn, hb]
      · simp
    _ = _ := by rw [hb]

/-- Principal specialization loses no information for invariant root series. -/
theorem rootPrincipalSpecialization_injective_on_invariant
    (f g : MvPowerSeries (Fin 3) K)
    (hf : ∀ i beta, rootCoefficient f (simpleReflection 0 i beta) = rootCoefficient f beta)
    (hg : ∀ i beta, rootCoefficient g (simpleReflection 0 i beta) = rootCoefficient g beta)
    (hspec : rootPrincipalSpecialization f = rootPrincipalSpecialization g) : f = g := by
  have hroot : rootCoefficient f = rootCoefficient g := by
    apply invariant_eq_of_nat_smul_marks (rootCoefficient f) (rootCoefficient g)
      (rootCoefficient_of_not_nonneg f) (rootCoefficient_of_not_nonneg g) hf hg
    intro n
    rw [← coeff_rootPrincipalSpecialization_of_invariant f hf n,
      ← coeff_rootPrincipalSpecialization_of_invariant g hg n, hspec]
  ext e
  have h := congrFun hroot (rootCoefficientsOfExponent e)
  simpa only [rootCoefficient_ofExponent] using h

end KanadeRussell.Representation
