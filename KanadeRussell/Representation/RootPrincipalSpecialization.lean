import KanadeRussell.Representation.RootMultiplicitySeries
import KanadeRussell.Representation.RootMultiplicitySpecialization
import Mathlib.RingTheory.MvPowerSeries.Rename

/-! Principal specialization of the multivariate root character. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MvPowerSeries.WithPiTopology

namespace KanadeRussell.Representation
open AffineWeightLattice

def PrincipalDegreeOccupation.exponent {n : ℕ} (b : PrincipalDegreeOccupation n) :
    Fin 3 →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun i => (b.val i).val)

@[simp] theorem PrincipalDegreeOccupation.exponent_apply {n : ℕ}
    (b : PrincipalDegreeOccupation n) (i : Fin 3) : b.exponent i = (b.val i).val := rfl

theorem PrincipalDegreeOccupation.exponent_root {n : ℕ} (b : PrincipalDegreeOccupation n) :
    rootCoefficientsOfExponent b.exponent = b.root := rfl

theorem exponent_degree_eq_sum (e : Fin 3 →₀ ℕ) : e.degree = ∑ i : Fin 3, e i := by
  change (∑ i ∈ e.support, e i) = _
  exact Finsupp.sum_fintype e (fun (_ : Fin 3) (a : ℕ) => a) (fun _ => rfl)

theorem PrincipalDegreeOccupation.exponent_degree {n : ℕ} (b : PrincipalDegreeOccupation n) :
    b.exponent.degree = n := by
  rw [exponent_degree_eq_sum]
  exact b.property

theorem exponent_map_principal (e : Fin 3 →₀ ℕ) :
    Finsupp.mapDomain (fun _ : Fin 3 => ()) e = Finsupp.single () e.degree := by
  have h := Finsupp.degree_mapDomain (fun _ : Fin 3 => ()) e
  have hs := Finsupp.unique_single (Finsupp.mapDomain (fun _ : Fin 3 => ()) e)
  rw [hs, Finsupp.degree_single] at h
  exact hs.trans (congrArg (Finsupp.single ()) h)

variable {K : Type*} [Field K]

/-- Send all three simple-root variables to the same principal variable. -/
def rootPrincipalSpecialization : MvPowerSeries (Fin 3) K →ₐ[K] PowerSeries K :=
  MvPowerSeries.rename (fun _ : Fin 3 => ())

theorem rootPrincipalSpecialization_monomial (e : Fin 3 →₀ ℕ) (c : K) :
    rootPrincipalSpecialization (MvPowerSeries.monomial e c) = PowerSeries.monomial e.degree c := by
  rw [rootPrincipalSpecialization, MvPowerSeries.rename_monomial, exponent_map_principal]
  rfl

theorem coeff_rootPrincipalSpecialization (f : MvPowerSeries (Fin 3) K) (n : ℕ) :
    PowerSeries.coeff n (rootPrincipalSpecialization f) =
      ∑ b : PrincipalDegreeOccupation n, MvPowerSeries.coeff b.exponent f := by
  classical
  rw [rootPrincipalSpecialization, PowerSeries.coeff, MvPowerSeries.coeff_rename]
  symm
  apply Finset.sum_bij (fun b _ => b.exponent)
  · intro b hb
    simp only [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff,
      exponent_map_principal, b.exponent_degree]
  · intro a ha b hb hab
    apply PrincipalDegreeOccupation.root_injective n
    exact congrArg rootCoefficientsOfExponent hab
  · intro e he
    have hm : Finsupp.mapDomain (fun _ : Fin 3 => ()) e = Finsupp.single () n := by
      simpa only [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff] using he
    have hd : e.degree = n := by
      have h := congrArg Finsupp.degree hm
      simpa only [Finsupp.degree_mapDomain, Finsupp.degree_single] using h
    have hd' : totalDegree (rootCoefficientsOfExponent e) = n := by
      rw [exponent_degree_eq_sum] at hd
      change (∑ i : Fin 3, (e i : ℤ)) = (n : ℤ)
      exact_mod_cast hd
    obtain ⟨b, hb⟩ := PrincipalDegreeOccupation.exists_root n (rootCoefficientsOfExponent e)
      (rootCoefficientsOfExponent_nonneg e) hd'
    refine ⟨b, Finset.mem_univ b, ?_⟩
    exact rootCoefficientsOfExponent_injective hb
  · intro b hb
    rfl

theorem continuous_rootPrincipalSpecialization [UniformSpace K] [DiscreteUniformity K] :
    Continuous (rootPrincipalSpecialization (K := K)) := by
  have he : (rootPrincipalSpecialization (K := K) : MvPowerSeries (Fin 3) K → PowerSeries K) =
      MvPowerSeries.subst (MvPowerSeries.X ∘ (fun _ : Fin 3 => ())) := by
    funext f
    exact MvPowerSeries.rename_eq_subst (fun _ : Fin 3 => ()) f
  rw [he]
  exact MvPowerSeries.continuous_subst (MvPowerSeries.HasSubst.X_comp _)

namespace PrincipalHighestWeightModule
variable {V : Type*} [CharZero K] [AddCommGroup V] [Module K V]

/-- The multivariate character specializes to the original principal character. -/
theorem rootPrincipalSpecialization_rootCharacter (M : PrincipalHighestWeightModule K V) :
    rootPrincipalSpecialization M.rootCharacter = PowerSeries.map (Int.castRingHom K) M.character := by
  ext n
  rw [coeff_rootPrincipalSpecialization, PowerSeries.coeff_map]
  change _ = ((PowerSeries.coeff n M.character : ℤ) : K)
  rw [M.coeff_character_cast_eq_sum_rootMultiplicity]
  apply Finset.sum_congr rfl
  intro b hb
  rw [M.coeff_rootCharacter, b.exponent_root]

end PrincipalHighestWeightModule
end KanadeRussell.Representation
