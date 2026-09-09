import KanadeRussell.Representation.NegativeWords

/-! The bounded principal filtration and primitive-vector extraction in arbitrary
E-stable submodules. No grading or Cartan stability is imposed on the submodule. -/
namespace KanadeRussell.Representation.PrincipalHighestWeightModule
attribute [local instance] LieRing.ofAssociativeRing
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable (M : PrincipalHighestWeightModule K V)

noncomputable def principalFiltration (d : ℤ) : Submodule K V :=
  ⨆ n : ℤ, ⨆ (_ : n ≤ d), M.grade n

theorem grade_le_principalFiltration (n d : ℤ) (hnd : n ≤ d) :
    M.grade n ≤ M.principalFiltration d :=
  le_iSup_of_le n (le_iSup_of_le hnd le_rfl)

theorem principalFiltration_mono : Monotone M.principalFiltration := by
  intro d e hde
  apply iSup_le
  intro n
  apply iSup_le
  intro hnd
  exact M.grade_le_principalFiltration n e (hnd.trans hde)

theorem principalFiltration_eq_bot_of_neg (d : ℤ) (hd : d < 0) :
    M.principalFiltration d = ⊥ := by
  apply le_antisymm _ bot_le
  apply iSup_le
  intro n
  apply iSup_le
  intro hnd
  rw [M.grade_negative n (lt_of_le_of_lt hnd hd)]

theorem E_mem_principalFiltration (i : Fin 3) (d : ℤ) (v : V)
    (hv : v ∈ M.principalFiltration d) : M.action.E i v ∈ M.principalFiltration (d-1) := by
  have hle : M.principalFiltration d ≤ (M.principalFiltration (d-1)).comap (M.action.E i) := by
    apply iSup_le
    intro n
    apply iSup_le
    intro hnd
    intro x hx
    exact M.grade_le_principalFiltration (n-1) (d-1) (by omega) (M.E_grade i n x hx)
  exact hle hv

/-- Every vector has a finite upper principal-degree bound. -/
theorem exists_mem_principalFiltration (v : V) :
    ∃ N : ℕ, v ∈ M.principalFiltration (N : ℤ) := by
  have hv : v ∈ M.negativeWordSpan := by rw [M.negativeWordSpan_eq_top]; trivial
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨u,rfl⟩ := hv
    exact ⟨u.length, M.grade_le_principalFiltration _ _ le_rfl (M.negativeWordValue_mem_grade u)⟩
  | zero => exact ⟨0, Submodule.zero_mem _⟩
  | add v w hv hw ihv ihw =>
    obtain ⟨N,hN⟩ := ihv
    obtain ⟨P,hP⟩ := ihw
    refine ⟨max N P, Submodule.add_mem _ ?_ ?_⟩
    · exact M.principalFiltration_mono (by omega) hN
    · exact M.principalFiltration_mono (by omega) hP
  | smul c v hv ih =>
    obtain ⟨N,hN⟩ := ih
    exact ⟨N, Submodule.smul_mem _ c hN⟩

/-- A nonzero E-stable submodule contains a nonzero primitive vector, even if
it is not assumed graded or invariant under the Cartan operators. -/
theorem exists_primitive_of_nonzero_E_stable (S : Submodule K V) (hS : S ≠ ⊥)
    (hE : ∀ i v, v ∈ S → M.action.E i v ∈ S) :
    ∃ v : V, v ∈ S ∧ v ≠ 0 ∧ ∀ i, M.action.E i v = 0 := by
  classical
  have hex : ∃ N : ℕ, ∃ v : V, v ∈ S ∧ v ≠ 0 ∧ v ∈ M.principalFiltration (N : ℤ) := by
    obtain ⟨v,hv,hv0⟩ := S.ne_bot_iff.mp hS
    obtain ⟨N,hN⟩ := M.exists_mem_principalFiltration v
    exact ⟨N,v,hv,hv0,hN⟩
  let N := Nat.find hex
  obtain ⟨v,hv,hv0,hvN⟩ := Nat.find_spec hex
  refine ⟨v,hv,hv0,?_⟩
  intro i
  have hlower := M.E_mem_principalFiltration i (N : ℤ) v hvN
  by_cases hN : N=0
  · rw [hN] at hlower
    have hz : M.principalFiltration ((0:ℤ)-1) = ⊥ :=
      M.principalFiltration_eq_bot_of_neg _ (by omega)
    simpa only [Nat.cast_zero, hz, Submodule.mem_bot] using hlower
  · by_contra hne
    have hcast : ((N-1 : ℕ) : ℤ) = (N : ℤ)-1 := by omega
    have hmin := Nat.find_min hex (show N-1 < N by omega)
    apply hmin
    exact ⟨M.action.E i v, hE i v hv, hne, by rwa [hcast]⟩

end KanadeRussell.Representation.PrincipalHighestWeightModule
