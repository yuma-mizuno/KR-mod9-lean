import KanadeRussell.Representation.PrincipalModePairing

/-! Finite commutator telescoping for normal-ordered principal modes. -/
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Tsuchioka.Fock
attribute [local instance] LieRing.ofAssociativeRing
variable {K : Type*} [Field K] [CharZero K]

theorem normalOrderedMode_lie_chevalleyF (w : K) (n : ℤ) (i : Fin 3) :
    ⁅normalOrderedMode w n, chevalleyF w i⁆ =
      modeCasimirLower w n i + modeCasimirUpper w n i := by
  simp only [normalOrderedMode, modeCasimirLower, modeCasimirUpper,
    Ring.lie_def, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← smul_add]
  apply Finset.sum_congr rfl
  intro r hr
  have he : principalMode w (-n) r *
      (principalMode w n r * chevalleyF w i - chevalleyF w i * principalMode w n r) +
      (principalMode w (-n) r * chevalleyF w i - chevalleyF w i * principalMode w (-n) r) *
        principalMode w n r =
      principalMode w (-n) r * principalMode w n r * chevalleyF w i -
        chevalleyF w i * (principalMode w (-n) r * principalMode w n r) := by
          simp only [mul_sub, sub_mul, mul_assoc]
          abel
  rw [he]
  exact (smul_sub _ _ _).symm

noncomputable def modeCasimirPartial (w : K) (N : ℕ) : Module.End K (Space K) :=
  (2:K) • ∑ n ∈ Finset.range N, normalOrderedMode w ((n:ℤ)+1)

theorem modeCasimirPartial_lie (w : K) (N : ℕ) (hN : 1 ≤ N) (i : Fin 3)
    (hbulk : ∀ n : ℕ, 1 ≤ n →
      modeCasimirLower w ((n:ℤ)+1) i + modeCasimirUpper w (n:ℤ) i = 0) :
    ⁅modeCasimirPartial w N, chevalleyF w i⁆ =
      (2:K) • modeCasimirLower w 1 i + (2:K) • modeCasimirUpper w (N:ℤ) i := by
  have hs : (∑ n ∈ Finset.range N,
      (modeCasimirLower w ((n:ℤ)+1) i + modeCasimirUpper w ((n:ℤ)+1) i)) =
      modeCasimirLower w 1 i + modeCasimirUpper w (N:ℤ) i := by
    induction N, hN using Nat.le_induction with
    | base => simp
    | succ n hn ih =>
      rw [Finset.sum_range_succ, ih]
      have h := hbulk n hn
      push_cast
      have he := eq_neg_of_add_eq_zero_left h
      rw [he]
      abel
  have hh : ⁅modeCasimirPartial w N, chevalleyF w i⁆ =
      (2:K) • ∑ n ∈ Finset.range N,
        ⁅normalOrderedMode w ((n:ℤ)+1), chevalleyF w i⁆ := by
    simp only [modeCasimirPartial, Ring.lie_def, smul_mul_assoc, mul_smul_comm,
      Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib, smul_sub]
  rw [hh]
  simp_rw [normalOrderedMode_lie_chevalleyF]
  rw [hs, smul_add]

theorem modeCasimirPartial_lie_of_boundary (w : K) (N : ℕ) (hN : 1 ≤ N)
    (i : Fin 3) (d : K)
    (hbulk : ∀ n : ℕ, 1 ≤ n →
      modeCasimirLower w ((n:ℤ)+1) i + modeCasimirUpper w (n:ℤ) i = 0)
    (hboundary : modeCasimirLower w 1 i = d • (chevalleyF w i * chevalleyH w i)) :
    ⁅modeCasimirPartial w N, chevalleyF w i⁆ =
      (2*d) • (chevalleyF w i * chevalleyH w i) +
        (2:K) • modeCasimirUpper w (N:ℤ) i := by
  rw [modeCasimirPartial_lie w N hN i hbulk, hboundary, smul_smul]

theorem modeCasimirUpper_apply_eq_zero (w : K) (n : ℤ) (i : Fin 3) (v : Space K)
    (hv : ∀ r : Fin 3, principalMode w n r v=0) : modeCasimirUpper w n i v=0 := by
  simp [modeCasimirUpper, LinearMap.sum_apply, LinearMap.smul_apply,
    Module.End.mul_apply, hv]

end KanadeRussell.Tsuchioka.Fock
