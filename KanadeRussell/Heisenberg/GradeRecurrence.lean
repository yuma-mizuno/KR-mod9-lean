import KanadeRussell.Heisenberg.GradedVacuum

/-! Finite Taylor integration and the exact dimension recurrence for one oscillator. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace KanadeRussell.Heisenberg
variable {K V ι : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]

noncomputable def integrationCoeff (n : ℕ) : K := (-1)^n / ((n+1).factorial : K)

@[simp] theorem integrationCoeff_zero : integrationCoeff (K := K) 0 = 1 := by
  norm_num [integrationCoeff]

theorem integrationCoeff_succ (n : ℕ) :
    integrationCoeff (K := K) (n+1) * (n+2) = -integrationCoeff n := by
  have hn : (n+2:K) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n+1)
  have hf : ((n+1).factorial:K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n+1)
  unfold integrationCoeff
  rw [Nat.factorial_succ (n+1), Nat.cast_mul, pow_succ]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [show (n+1+1:K) = n+2 by ring]
  field_simp
noncomputable def integration (a b : Module.End K V) : ℕ → Module.End K V
  | 0 => b
  | n+1 => integration a b n + integrationCoeff (K := K) (n+1) • (b^(n+2) * a^(n+1))

theorem annihilation_integration (a b : Module.End K V)
    (hab : ∀ v, a (b v) = b (a v) + v) (n : ℕ) (v : V) :
    a (integration a b n v) = v + integrationCoeff (K := K) n • (b^(n+1)) ((a^(n+1)) v) := by
  induction n with
  | zero => simpa [integration, add_comm] using hab v
  | succ n ih =>
    simp only [integration, LinearMap.add_apply, LinearMap.smul_apply, Module.End.mul_apply, map_add, map_smul]
    rw [ih, annihilation_creation_pow a b hab (n+1)]
    simp only [smul_add, smul_smul]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [show (n+1+1:K) = n+2 by ring, integrationCoeff_succ]
    rw [pow_succ' a (n+1), Module.End.mul_apply]
    module

namespace GradedSystem
variable (G : GradedSystem K V ι)

omit [CharZero K] in
theorem integration_mem (i : ι) (n : ℕ) (d : ℤ) (v : V) (hv : v ∈ G.grade d) :
    integration (G.annihilate i) (G.create i) n v ∈ G.grade (d+G.weight i) := by
  induction n with
  | zero => exact G.raise i d v hv
  | succ n ih =>
    apply (G.grade (d+G.weight i)).add_mem ih
    apply (G.grade (d+G.weight i)).smul_mem
    have h := G.create_pow_mem i (n+2) (d-(n+1:ℕ)*G.weight i) _
      (G.annihilate_pow_mem i (n+1) d v hv)
    simpa only [Module.End.mul_apply, show d - (n+1:ℕ)*G.weight i + (n+2:ℕ)*G.weight i = d+G.weight i by push_cast; ring] using h

theorem annihilate_grade_surjective (i : ι) (d : ℤ) (v : V)
    (hv : v ∈ G.grade (d-G.weight i)) :
    ∃ u ∈ G.grade d, G.annihilate i u = v := by
  let n := (d-G.weight i).toNat
  refine ⟨integration (G.annihilate i) (G.create i) n v, ?_, ?_⟩
  · simpa only [sub_add_cancel] using G.integration_mem i n (d-G.weight i) v hv
  · rw [annihilation_integration _ _ (G.pair i), G.annihilate_nilpotent i (d-G.weight i) v hv,
      map_zero, smul_zero, add_zero]

theorem annihilate_grade_map (i : ι) (d : ℤ) :
    (G.grade d).map (G.annihilate i) = G.grade (d-G.weight i) := by
  apply le_antisymm
  · rintro _ ⟨v,hv,rfl⟩
    exact G.lower i d v hv
  · intro v hv
    exact G.annihilate_grade_surjective i d v hv

theorem annihilate_target_grade_finite (i : ι) (d : ℤ) [Module.Finite K (G.grade d)] :
    Module.Finite K (G.grade (d-G.weight i)) := by
  rw [← G.annihilate_grade_map i d]
  infer_instance

theorem finrank_grade_eq_ker_add (i : ι) (d : ℤ) [Module.Finite K (G.grade d)] :
    Module.finrank K (G.grade d) =
      Module.finrank K (G.grade d ⊓ LinearMap.ker (G.annihilate i) : Submodule K V) +
      Module.finrank K (G.grade (d-G.weight i)) := by
  let f := (G.annihilate i).domRestrict (G.grade d)
  have hr : LinearMap.range f = G.grade (d-G.weight i) := by
    rw [LinearMap.range_domRestrict]
    exact G.annihilate_grade_map i d
  have hk : (LinearMap.ker f).map (G.grade d).subtype =
      G.grade d ⊓ LinearMap.ker (G.annihilate i) := by
    change ((LinearMap.ker (G.annihilate i)).comap (G.grade d).subtype).map (G.grade d).subtype = _
    rw [Submodule.map_comap_subtype]
  have he : Module.finrank K (LinearMap.ker f) =
      Module.finrank K (G.grade d ⊓ LinearMap.ker (G.annihilate i) : Submodule K V) := by
    rw [← hk, Submodule.finrank_map_subtype_eq]
  have h := f.finrank_range_add_finrank_ker
  rw [hr, he] at h
  omega

end GradedSystem
end KanadeRussell.Heisenberg
