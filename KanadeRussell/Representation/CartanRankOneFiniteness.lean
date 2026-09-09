import KanadeRussell.Representation.FiniteNilpotence
import KanadeRussell.Representation.HighestWeightSupport

/-! A finite rank-one orbit can be chosen stable under every Cartan operator
whose commutators with the root operators have opposite scalar coefficients. -/
namespace KanadeRussell.Representation
attribute [local instance] LieRing.ofAssociativeRing
variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]

noncomputable def rankOneOrbit (E F : Module.End K V) (v : V) : Submodule K V :=
  Submodule.span K (Set.range (fun p : ℕ × ℕ => (F^p.1) ((E^p.2) v)))

theorem mem_rankOneOrbit (E F : Module.End K V) (v : V) (a b : ℕ) :
    (F^a) ((E^b) v) ∈ rankOneOrbit E F v := Submodule.subset_span ⟨(a,b), rfl⟩

theorem self_mem_rankOneOrbit (E F : Module.End K V) (v : V) : v ∈ rankOneOrbit E F v := by
  simpa using mem_rankOneOrbit E F v 0 0

theorem rankOneOrbit_stable_of_generators (E F A : Module.End K V) (v : V)
    (hA : ∀ a b : ℕ, A ((F^a) ((E^b) v)) ∈ rankOneOrbit E F v) :
    ∀ x ∈ rankOneOrbit E F v, A x ∈ rankOneOrbit E F v := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨⟨a,b⟩, rfl⟩ := hx; exact hA a b
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul c x hx ih => simpa only [map_smul] using Submodule.smul_mem _ c ih

theorem rankOneOrbit_F_stable (E F : Module.End K V) (v : V) :
    ∀ x ∈ rankOneOrbit E F v, F x ∈ rankOneOrbit E F v :=
  rankOneOrbit_stable_of_generators E F F v (by
    intro a b
    simpa [pow_succ', Module.End.mul_apply] using mem_rankOneOrbit E F v (a+1) b)

theorem rankOneOrbit_Cartan_stable (E F B : Module.End K V) (v : V) (c mu : K)
    (hBE : ⁅B,E⁆ = c • E) (hBF : ⁅B,F⁆ = (-c) • F) (hv : B v = mu • v) :
    ∀ x ∈ rankOneOrbit E F v, B x ∈ rankOneOrbit E F v :=
  rankOneOrbit_stable_of_generators E F B v (by
    intro a b
    rw [weight_pow_of_commutator B F (-c) _ _ hBF
      (weight_pow_of_commutator B E c mu v hBE hv b) a]
    exact Submodule.smul_mem _ _ (mem_rankOneOrbit E F v a b))

theorem rankOneOrbit_E_stable (E F H : Module.End K V) (v : V) (mu : K)
    (hEF : ⁅E,F⁆ = H) (hHE : ⁅H,E⁆ = (2:K) • E)
    (hHF : ⁅H,F⁆ = (-2:K) • F) (hv : H v = mu • v) :
    ∀ x ∈ rankOneOrbit E F v, E x ∈ rankOneOrbit E F v :=
  rankOneOrbit_stable_of_generators E F E v (by
    intro a b
    cases a with
    | zero => simpa [pow_succ', Module.End.mul_apply] using mem_rankOneOrbit E F v 0 (b+1)
    | succ a =>
      rw [rankOne_normal_order E F H _ _ hEF hHF
        (weight_pow_of_commutator H E 2 mu v hHE hv b) a]
      apply Submodule.add_mem
      · simpa [pow_succ', Module.End.mul_apply] using mem_rankOneOrbit E F v (a+1) (b+1)
      · exact Submodule.smul_mem _ _ (mem_rankOneOrbit E F v a b))

theorem rankOneOrbit_finite (E F H : Module.End K V) (v : V) (mu : K)
    (hEF : ⁅E,F⁆ = H) (hHE : ⁅H,E⁆ = (2:K) • E)
    (hHF : ⁅H,F⁆ = (-2:K) • F) (hv : H v = mu • v)
    (hEnil : ∀ x : V, ∃ n : ℕ, (E^n) x = 0)
    (hFnil : ∀ x : V, ∃ n : ℕ, (F^n) x = 0) : Module.Finite K (rankOneOrbit E F v) := by
  obtain ⟨S, hvs, hfin, hEs, hFs, _⟩ :=
    rankOne_locally_finite E F H mu v hEF hHE hHF hv hEnil hFnil
  have hpow (A : Module.End K V) (hA : ∀ x ∈ S, A x ∈ S) (n : ℕ) (x : V)
      (hx : x ∈ S) : (A^n) x ∈ S := by
    induction n with
    | zero => simpa using hx
    | succ n ih => simpa only [pow_succ', Module.End.mul_apply] using hA _ ih
  have hle : rankOneOrbit E F v ≤ S := by
    apply Submodule.span_le.mpr
    rintro x ⟨⟨a,b⟩, rfl⟩
    exact hpow F hFs a _ (hpow E hEs b v hvs)
  letI := hfin
  exact Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)

end KanadeRussell.Representation
