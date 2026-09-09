import KanadeRussell.Representation.CharacterSpecialization
import KanadeRussell.Tsuchioka.Fock

/-! The principal Heisenberg Euler product stabilizes in every bounded degree.
The finite product is indexed by exactly the oscillator weights in that bound. -/
open PowerSeries PowerSeries.WithPiTopology Filter Topology
open scoped DiscreteUniformity QTheory

namespace KanadeRussell.Tsuchioka.Fock

theorem isMode_iff_mod_six (n : ℕ) : IsMode n ↔ n % 6 = 1 ∨ n % 6 = 5 := by
  dsimp [IsMode]
  omega

end KanadeRussell.Tsuchioka.Fock

namespace KanadeRussell.Representation
open Tsuchioka.Fock

/-- All principal oscillator modes whose weight is at most `N`. -/
def boundedModes (N : ℕ) : Finset Mode := (Finset.range (N + 1)).subtype IsMode

@[simp] theorem mem_boundedModes (N : ℕ) (m : Mode) : m ∈ boundedModes N ↔ m.val ≤ N := by
  simp [boundedModes]

noncomputable def finiteHeisenbergEuler (N : ℕ) : PowerSeries ℤ :=
  ∏ m ∈ (Finset.range (N + 1)).filter IsMode, (1 - X ^ m)

theorem finiteHeisenbergEuler_eq_prod_boundedModes (N : ℕ) :
    finiteHeisenbergEuler N = ∏ m ∈ boundedModes N, (1 - (X : PowerSeries ℤ) ^ m.val) := by
  exact (Finset.prod_subtype_eq_prod_filter
    (s := Finset.range (N+1)) (p := IsMode) (fun m : ℕ => 1 - (X : PowerSeries ℤ)^m)).symm

theorem finiteHeisenbergEuler_eq_prod (N : ℕ) (s : Finset Mode)
    (hs : ∀ m : Mode, m ∈ s ↔ m.val ≤ N) :
    finiteHeisenbergEuler N = ∏ m ∈ s, (1 - (X : PowerSeries ℤ) ^ m.val) := by
  have he : boundedModes N = s := by ext m; simp [hs]
  rw [finiteHeisenbergEuler_eq_prod_boundedModes, he]

private theorem coeff_prod_truncate (s : Finset ℕ) (N n : ℕ) (hn : n ≤ N)
    (C : PowerSeries ℤ) :
    coeff n ((∏ m ∈ s, (1 - (X : PowerSeries ℤ) ^ m)) * C) =
      coeff n ((∏ m ∈ s.filter (· ≤ N), (1 - (X : PowerSeries ℤ) ^ m)) * C) := by
  rw [← Finset.prod_filter_mul_prod_filter_not s (· ≤ N), mul_right_comm]
  apply coeff_mul_prod_one_sub_of_lt_order
  intro m hm
  have hlarge := (Finset.mem_filter.mp hm).2
  rw [order_X_pow]
  exact_mod_cast (show n < m by omega)

private def progressionWeights (M r : ℕ) : Finset ℕ :=
  (Finset.range M).image (fun k => 6 * k + r)

private theorem progressionWeights_disjoint (M : ℕ) :
    Disjoint (progressionWeights M 1) (progressionWeights M 5) := by
  apply Finset.disjoint_left.mpr
  intro n hn hn'
  obtain ⟨a, ha, hna⟩ := Finset.mem_image.mp hn
  obtain ⟨b, hb, hnb⟩ := Finset.mem_image.mp hn'
  omega

private theorem progressionWeights_truncate (M N : ℕ) (hMN : N < M) :
    ((progressionWeights M 1 ∪ progressionWeights M 5).filter (· ≤ N)) =
      (Finset.range (N + 1)).filter IsMode := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_union, progressionWeights,
    Finset.mem_image, Finset.mem_range, isMode_iff_mod_six]
  constructor
  · rintro ⟨(⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩), hn⟩ <;> omega
  · rintro ⟨hn, hres⟩
    refine ⟨?_, by omega⟩
    rcases hres with hres | hres
    · exact Or.inl ⟨n / 6, by omega, by omega⟩
    · exact Or.inr ⟨n / 6, by omega, by omega⟩

private theorem qPochhammer_eq_progressionWeights (M r : ℕ) :
    qPochhammer ((X : PowerSeries ℤ)^r) (X^6) M =
      ∏ m ∈ progressionWeights M r, (1 - (X : PowerSeries ℤ)^m) := by
  rw [progressionWeights, Finset.prod_image]
  · simp [qPochhammer, ← pow_mul, ← pow_add, Nat.add_comm]
  · intro a ha b hb hab
    dsimp at hab
    omega

private theorem coeff_rectangularEuler (M N n : ℕ) (hMN : N < M) (hn : n ≤ N)
    (C : PowerSeries ℤ) :
    coeff n ((qPochhammer (X : PowerSeries ℤ) (X^6) M *
      qPochhammer (X^5) (X^6) M) * C) =
      coeff n (finiteHeisenbergEuler N * C) := by
  have hfirst := qPochhammer_eq_progressionWeights M 1
  simp only [pow_one] at hfirst
  rw [hfirst, qPochhammer_eq_progressionWeights M 5]
  rw [← Finset.prod_union (progressionWeights_disjoint M)]
  rw [coeff_prod_truncate _ N n hn C, progressionWeights_truncate M N hMN]
  rfl

/-- Every coefficient through `N` is unchanged after truncating the Euler product,
even after multiplication by an arbitrary formal power series. -/
theorem coeff_principalHeisenbergEuler_mul_eq_finite (C : PowerSeries ℤ) (N n : ℕ)
    (hn : n ≤ N) :
    coeff n (Product.principalHeisenbergEuler * C) =
      coeff n (finiteHeisenbergEuler N * C) := by
  have hq : IsTopologicallyNilpotent ((X : PowerSeries ℤ)^6) := by simp
  have h1 := tendsto_qPochhammer_qPochhammerInf (a := (X : PowerSeries ℤ)) hq
  have h5 := tendsto_qPochhammer_qPochhammerInf (a := (X : PowerSeries ℤ)^5) hq
  have hlim := ((continuous_coeff ℤ n).tendsto _).comp ((h1.mul h5).mul_const C)
  have hevent : ∀ᶠ M : ℕ in atTop,
      coeff n ((qPochhammer (X : PowerSeries ℤ) (X^6) M *
        qPochhammer (X^5) (X^6) M) * C) =
        coeff n (finiteHeisenbergEuler N * C) :=
    eventually_atTop.mpr ⟨N+1, fun M hM => coeff_rectangularEuler M N n (by omega) hn C⟩
  have heq := tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hevent.mono fun _ h => h.symm))
  simpa [Product.principalHeisenbergEuler_eq_six, Product.progressionProduct, q] using heq

theorem coeff_principalHeisenbergEuler_eq_finite (N n : ℕ) (hn : n ≤ N) :
    coeff n Product.principalHeisenbergEuler = coeff n (finiteHeisenbergEuler N) := by
  simpa using coeff_principalHeisenbergEuler_mul_eq_finite 1 N n hn

end KanadeRussell.Representation
