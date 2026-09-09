import KanadeRussell.Representation.PrincipalHighestWeight

namespace KanadeRussell.Representation
attribute [local instance] LieRing.ofAssociativeRing
variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]

 theorem rankOne_string_recurrence (E F H : Module.End K V) (mu : K) (v : V)
    (hEF : ⁅E,F⁆ = H) (hHF : ⁅H,F⁆ = (-2 : K) • F)
    (hE : E v = 0) (hH : H v = mu • v) (n : ℕ) :
    H ((F^n) v) = (mu - 2*(n:K)) • ((F^n) v) ∧
    E ((F^(n+1)) v) = (((n:K)+1)*(mu-n)) • ((F^n) v) := by
  have ef (x : V) : E (F x) = H x + F (E x) := by
    have h := congrArg (fun a : Module.End K V => a x) hEF
    simpa only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply,
      sub_eq_iff_eq_add] using h
  have hf (x : V) : H (F x) = (-2:K) • F x + F (H x) := by
    have h := congrArg (fun a : Module.End K V => a x) hHF
    simpa only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply,
      LinearMap.smul_apply, sub_eq_iff_eq_add] using h
  induction n with
  | zero => simp [ef, hE, hH]
  | succ n ih =>
    have hh : H ((F^(n+1)) v) = (mu-2*((n:K)+1)) • ((F^(n+1)) v) := by
      rw [pow_succ', Module.End.mul_apply, hf, ih.1, map_smul, ← add_smul]
      congr 1
      ring
    constructor
    · simpa using hh
    · rw [pow_succ', Module.End.mul_apply, ef, hh, ih.2, map_smul]
      rw [← Module.End.mul_apply, ← pow_succ', ← add_smul]
      push_cast
      congr 1
      ring

 theorem rankOne_string_endpoint (E F H : Module.End K V) (mu : K) (v : V)
    (hEF : ⁅E,F⁆ = H) (hHF : ⁅H,F⁆ = (-2 : K) • F)
    (hv : v ≠ 0) (hE : E v = 0) (hH : H v = mu • v)
    (hnil : ∃ N : ℕ, (F^N) v = 0) :
    ∃ n : ℕ, mu = (n:K) ∧ (F^(n+1)) v = 0 ∧ ∀ j ≤ n, (F^j) v ≠ 0 := by
  classical
  let N := Nat.find hnil
  have hz : (F^N) v = 0 := Nat.find_spec hnil
  have hp : 0 < N := by
    by_contra h
    have : N = 0 := by omega
    exact hv (by simpa [this] using hz)
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  have hnon : ∀ j ≤ n, (F^j) v ≠ 0 := by
    intro j hj
    exact Nat.find_min hnil (by omega)
  have hr := (rankOne_string_recurrence E F H mu v hEF hHF hE hH n).2
  have hz' : (F^(n+1)) v = 0 := by simpa [hn] using hz
  rw [hz', map_zero, eq_comm, smul_eq_zero_iff_left (hnon n le_rfl),
    mul_eq_zero, sub_eq_zero] at hr
  exact ⟨n, hr.resolve_left (Nat.cast_add_one_ne_zero n), hz', hnon⟩

namespace PrincipalHighestWeightModule

theorem highestVector_root_string (M : PrincipalHighestWeightModule K V) (i : Fin 3) :
    ((M.action.F i)^(M.highestWeight i+1)) M.highestVector = 0 ∧
    ∀ j ≤ M.highestWeight i, ((M.action.F i)^j) M.highestVector ≠ 0 := by
  have hef : ⁅M.action.E i, M.action.F i⁆ = M.action.H i := by
    simpa using M.action.EF i i
  have hhf : ⁅M.action.H i, M.action.F i⁆ = (-2:K) • M.action.F i := by
    rw [M.action.HF]
    have hii : Tsuchioka.Fock.affineCartanMatrix i i = 2 := by fin_cases i <;> rfl
    rw [hii]
    simp [neg_smul, ← Int.cast_smul_eq_zsmul K]
  obtain ⟨n, hn, hz, hnon⟩ := rankOne_string_endpoint
    (M.action.E i) (M.action.F i) (M.action.H i) (M.highestWeight i : K)
    M.highestVector hef hhf M.highestVector_ne_zero (M.E_highestVector i)
    (M.H_highestVector i) (M.F_locally_nilpotent i M.highestVector)
  have heq : M.highestWeight i = n := Nat.cast_injective hn
  simpa [heq] using And.intro hz hnon

end PrincipalHighestWeightModule
end KanadeRussell.Representation
