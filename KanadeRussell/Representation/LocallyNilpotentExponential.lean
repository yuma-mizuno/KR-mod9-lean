import KanadeRussell.Representation.RankOneLocalFiniteness
import Mathlib.RingTheory.Nilpotent.Exp

set_option maxRecDepth 2000
namespace KanadeRussell.Representation
variable {K V W : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

local instance : Module ℚ (Module.End K V) :=
  Module.compHom (Module.End K V) (algebraMap ℚ K)

noncomputable def exponentialPartial (A : Module.End K V) (N : ℕ) : Module.End K V :=
  ∑ n ∈ Finset.range N, (n.factorial : K)⁻¹ • A^n

omit [CharZero K] in
theorem exponentialPartial_apply (A : Module.End K V) (N : ℕ) (v : V) :
    exponentialPartial A N v = ∑ n ∈ Finset.range N, (n.factorial : K)⁻¹ • (A^n) v := by
  simp [exponentialPartial, LinearMap.sum_apply]

theorem exponentialPartial_eq_of_le (A : Module.End K V) (v : V) {N M : ℕ}
    (hN : (A^N) v = 0) (hNM : N ≤ M) :
    exponentialPartial A N v = exponentialPartial A M v := by
  simp only [exponentialPartial_apply]
  apply Finset.sum_subset (Finset.range_mono hNM)
  intro n hn hnN
  rw [end_pow_apply_zero_of_le A v hN (by simpa using hnN), smul_zero]

theorem exponentialPartial_eq (A : Module.End K V) (v : V) {N M : ℕ}
    (hN : (A^N) v = 0) (hM : (A^M) v = 0) :
    exponentialPartial A N v = exponentialPartial A M v :=
  (exponentialPartial_eq_of_le A v hN (Nat.le_max_left N M)).trans
    (exponentialPartial_eq_of_le A v hM (Nat.le_max_right N M)).symm

noncomputable def locallyNilpotentExpValue (A : Module.End K V)
    (hA : ∀ v : V, ∃ N : ℕ, (A^N) v = 0) (v : V) : V :=
  exponentialPartial A (Classical.choose (hA v)) v

theorem locallyNilpotentExpValue_eq (A : Module.End K V)
    (hA : ∀ v : V, ∃ N : ℕ, (A^N) v = 0) (v : V) {N : ℕ} (hN : (A^N) v = 0) :
    locallyNilpotentExpValue A hA v = exponentialPartial A N v :=
  exponentialPartial_eq A v (Classical.choose_spec (hA v)) hN

noncomputable def locallyNilpotentExpLinear (A : Module.End K V)
    (hA : ∀ v : V, ∃ N : ℕ, (A^N) v = 0) : Module.End K V where
  toFun := locallyNilpotentExpValue A hA
  map_add' v w := by
    obtain ⟨N,hN⟩ := hA v
    obtain ⟨M,hM⟩ := hA w
    have hv := end_pow_apply_zero_of_le A v hN (Nat.le_max_left N M)
    have hw := end_pow_apply_zero_of_le A w hM (Nat.le_max_right N M)
    have hvw : (A^(max N M)) (v+w) = 0 := by rw [map_add, hv, hw, add_zero]
    rw [locallyNilpotentExpValue_eq A hA _ hvw,
      locallyNilpotentExpValue_eq A hA _ hv, locallyNilpotentExpValue_eq A hA _ hw, map_add]
  map_smul' c v := by
    obtain ⟨N,hN⟩ := hA v
    have hcv : (A^N) (c • v) = 0 := by rw [map_smul, hN, smul_zero]
    rw [locallyNilpotentExpValue_eq A hA _ hcv,
      locallyNilpotentExpValue_eq A hA _ hN, map_smul]
    rfl

theorem locallyNilpotentExpLinear_eq_sum (A : Module.End K V)
    (hA : ∀ v : V, ∃ N : ℕ, (A^N) v = 0) (v : V) {N : ℕ} (hN : (A^N) v = 0) :
    locallyNilpotentExpLinear A hA v =
      ∑ n ∈ Finset.range N, (n.factorial : K)⁻¹ • (A^n) v := by
  change locallyNilpotentExpValue A hA v = _
  rw [locallyNilpotentExpValue_eq A hA v hN, exponentialPartial_apply]

omit [CharZero K] in
theorem intertwiner_pow_apply (A : Module.End K V) (B : Module.End K W) (f : V →ₗ[K] W)
    (hf : ∀ v, f (A v) = B (f v)) (n : ℕ) (v : V) :
    f ((A^n) v) = (B^n) (f v) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pow_succ', Module.End.mul_apply, hf, ih]

theorem locallyNilpotentExpLinear_intertwine (A : Module.End K V) (B : Module.End K W)
    (hA : ∀ v : V, ∃ N : ℕ, (A^N) v = 0)
    (hB : ∀ w : W, ∃ N : ℕ, (B^N) w = 0)
    (f : V →ₗ[K] W) (hf : ∀ v, f (A v) = B (f v)) (v : V) :
    f (locallyNilpotentExpLinear A hA v) = locallyNilpotentExpLinear B hB (f v) := by
  obtain ⟨N,hN⟩ := hA v
  have hBN : (B^N) (f v) = 0 := by rw [← intertwiner_pow_apply A B f hf, hN, map_zero]
  rw [locallyNilpotentExpLinear_eq_sum A hA v hN,
    locallyNilpotentExpLinear_eq_sum B hB (f v) hBN, map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [map_smul, intertwiner_pow_apply A B f hf]

omit [CharZero K] in
theorem locallyNilpotent_neg (A : Module.End K V)
    (hA : ∀ v : V, ∃ N : ℕ, (A^N) v = 0) :
    ∀ v : V, ∃ N : ℕ, ((-A)^N) v = 0 := by
  intro v
  obtain ⟨N,hN⟩ := hA v
  exact ⟨N, by rw [neg_pow, Module.End.mul_apply, hN, map_zero]⟩

theorem locallyNilpotentExpLinear_eq_exp (A : Module.End K V) (hA : IsNilpotent A)
    (hlocal : ∀ v : V, ∃ N : ℕ, (A^N) v = 0) :
    locallyNilpotentExpLinear A hlocal = IsNilpotent.exp A := by
  obtain ⟨N,hN⟩ := hA
  ext v
  rw [locallyNilpotentExpLinear_eq_sum A hlocal v (by rw [hN, LinearMap.zero_apply]),
    IsNilpotent.exp_eq_sum hN]
  simp only [← Rat.cast_smul_eq_qsmul K, Rat.cast_inv, Rat.cast_natCast,
    LinearMap.sum_apply, LinearMap.smul_apply]

theorem uniformExp_intertwine_locallyNilpotent (A : Module.End K V) (B : Module.End K W)
    (hA : IsNilpotent A) (hB : ∀ w : W, ∃ N : ℕ, (B^N) w = 0)
    (f : V →ₗ[K] W) (hf : ∀ v, f (A v) = B (f v)) (v : V) :
    f (IsNilpotent.exp A v) = locallyNilpotentExpLinear B hB (f v) := by
  have hl : ∀ v : V, ∃ N : ℕ, (A^N) v = 0 := by
    obtain ⟨N,hN⟩ := hA
    exact fun v => ⟨N, by rw [hN, LinearMap.zero_apply]⟩
  rw [← locallyNilpotentExpLinear_eq_exp A hA hl]
  exact locallyNilpotentExpLinear_intertwine A B hl hB f hf v

theorem locallyNilpotentExpLinear_neg_left (A : Module.End K V)
    (hA : ∀ v : V, ∃ N : ℕ, (A^N) v = 0) (v : V) :
    locallyNilpotentExpLinear (-A) (locallyNilpotent_neg A hA)
      (locallyNilpotentExpLinear A hA v) = v := by
  obtain ⟨N,hN⟩ := hA v
  let S := LinearMap.ker (A^N)
  have hs : ∀ x ∈ S, A x ∈ S := by
    intro x hx
    change (A^N) (A x) = 0
    change (A^N) x = 0 at hx
    rw [← Module.End.mul_apply, ← pow_succ, pow_succ', Module.End.mul_apply, hx, map_zero]
  let B : Module.End K S := A.restrict hs
  have hf : ∀ x : S, S.subtype (B x) = A (S.subtype x) := fun _ => rfl
  have hB : IsNilpotent B := by
    refine ⟨N, ?_⟩
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change S.subtype ((B^N) x) = 0
    rw [intertwiner_pow_apply B A S.subtype hf]
    exact x.property
  let x : S := ⟨v,hN⟩
  have hp := uniformExp_intertwine_locallyNilpotent B A hB hA S.subtype hf x
  have hn := uniformExp_intertwine_locallyNilpotent (-B) (-A) hB.neg
    (locallyNilpotent_neg A hA) S.subtype (by intro y; rfl) (IsNilpotent.exp B x)
  change locallyNilpotentExpLinear (-A) _ (locallyNilpotentExpLinear A _ (S.subtype x)) = S.subtype x
  rw [← hp, ← hn]
  have hi := congrArg (fun a : Module.End K S => a x) (IsNilpotent.exp_neg_mul_exp_self hB)
  rw [Module.End.mul_apply, Module.End.one_apply] at hi
  rw [hi]

noncomputable def locallyNilpotentExp (A : Module.End K V)
    (hA : ∀ v : V, ∃ N : ℕ, (A^N) v = 0) : V ≃ₗ[K] V :=
  LinearEquiv.ofLinear (locallyNilpotentExpLinear A hA)
    (locallyNilpotentExpLinear (-A) (locallyNilpotent_neg A hA))
    (by
      ext v
      have h := locallyNilpotentExpLinear_neg_left (-A) (locallyNilpotent_neg A hA) v
      simpa using h)
    (by ext v; exact locallyNilpotentExpLinear_neg_left A hA v)

theorem locallyNilpotentExp_apply_eq_sum (A : Module.End K V)
    (hA : ∀ v : V, ∃ N : ℕ, (A^N) v = 0) (v : V) {N : ℕ} (hN : (A^N) v = 0) :
    locallyNilpotentExp A hA v =
      ∑ n ∈ Finset.range N, (n.factorial : K)⁻¹ • (A^n) v :=
  locallyNilpotentExpLinear_eq_sum A hA v hN

@[simp] theorem locallyNilpotentExp_symm (A : Module.End K V)
    (hA : ∀ v : V, ∃ N : ℕ, (A^N) v = 0) :
    (locallyNilpotentExp A hA).symm = locallyNilpotentExp (-A) (locallyNilpotent_neg A hA) := by
  ext v
  rfl

theorem locallyNilpotentExp_intertwine (A : Module.End K V) (B : Module.End K W)
    (hA : ∀ v : V, ∃ N : ℕ, (A^N) v = 0)
    (hB : ∀ w : W, ∃ N : ℕ, (B^N) w = 0)
    (f : V →ₗ[K] W) (hf : ∀ v, f (A v) = B (f v)) (v : V) :
    f (locallyNilpotentExp A hA v) = locallyNilpotentExp B hB (f v) :=
  locallyNilpotentExpLinear_intertwine A B hA hB f hf v

end KanadeRussell.Representation
