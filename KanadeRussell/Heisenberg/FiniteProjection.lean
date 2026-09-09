import Mathlib

/-! Finite vacuum projection for a normalized Heisenberg pair.
The projection is constructed from the operators and the factorial coefficients;
no vacuum decomposition or character theorem is assumed. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace KanadeRussell.Heisenberg
variable {K V W : Type*} [Field K] [CharZero K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

noncomputable def taylorCoeff (n : ℕ) : K := (-1)^n / (n.factorial : K)

omit [CharZero K] in
@[simp] theorem taylorCoeff_zero : taylorCoeff (K := K) 0 = 1 := by
  norm_num [taylorCoeff]

theorem taylorCoeff_succ (n : ℕ) :
    taylorCoeff (K := K) (n+1) * (n+1) = -taylorCoeff n := by
  have hn : (n+1:K) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hf : (n.factorial:K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  simp only [taylorCoeff, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  field_simp

noncomputable def projection (a b : Module.End K V) : ℕ → Module.End K V
  | 0 => 1
  | n+1 => projection a b n + taylorCoeff (K := K) (n+1) • (b^(n+1) * a^(n+1))

omit [CharZero K] in
theorem projection_eq_sum (a b : Module.End K V) (n : ℕ) :
    projection a b n = ∑ r ∈ Finset.range (n+1), taylorCoeff (K := K) r • (b^r * a^r) := by
  induction n with
  | zero => simp [projection]
  | succ n ih => rw [projection, Finset.sum_range_succ, ← ih]

theorem annihilation_creation_pow (a b : Module.End K V)
    (hab : ∀ v, a (b v) = b (a v) + v) (n : ℕ) (v : V) :
    a ((b^(n+1)) v) = (b^(n+1)) (a v) + (n+1:K) • (b^n) v := by
  induction n with
  | zero => simpa using hab v
  | succ n ih =>
    rw [pow_succ' b (n+1), Module.End.mul_apply, hab, ih, map_add, map_smul]
    simp only [pow_succ', Module.End.mul_apply]
    push_cast
    module

/-- Only the final Taylor term survives differentiation. -/
theorem annihilation_projection (a b : Module.End K V)
    (hab : ∀ v, a (b v) = b (a v) + v) (n : ℕ) (v : V) :
    a (projection a b n v) = taylorCoeff (K := K) n • (b^n) ((a^(n+1)) v) := by
  induction n with
  | zero => simp [projection]
  | succ n ih =>
    simp only [projection, LinearMap.add_apply, LinearMap.smul_apply,
      Module.End.mul_apply, map_add, map_smul]
    rw [ih, annihilation_creation_pow a b hab]
    simp only [smul_add, smul_smul]
    rw [taylorCoeff_succ]
    rw [pow_succ' a (n+1), Module.End.mul_apply]
    module

theorem projection_mem_ker (a b : Module.End K V)
    (hab : ∀ v, a (b v) = b (a v) + v) (n : ℕ) (v : V)
    (hv : (a^(n+1)) v = 0) : a (projection a b n v) = 0 := by
  rw [annihilation_projection a b hab, hv, map_zero, smul_zero]

omit [CharZero K] in
theorem pow_apply_eq_zero (a : Module.End K V) (v : V) (hv : a v = 0) (n : ℕ) :
    (a^(n+1)) v = 0 := by
  rw [pow_succ, Module.End.mul_apply, hv, map_zero]

omit [CharZero K] in
theorem projection_fixed (a b : Module.End K V) (n : ℕ) (v : V) (hv : a v = 0) :
    projection a b n v = v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [projection, LinearMap.add_apply, LinearMap.smul_apply, Module.End.mul_apply]
    rw [ih, pow_apply_eq_zero a v hv n, map_zero, smul_zero, add_zero]

theorem projection_idempotent (a b : Module.End K V)
    (hab : ∀ v, a (b v) = b (a v) + v) (n : ℕ) (v : V)
    (hv : (a^(n+1)) v = 0) :
    projection a b n (projection a b n v) = projection a b n v :=
  projection_fixed a b n _ (projection_mem_ker a b hab n v hv)

omit [CharZero K] in
theorem intertwine_pow (f : V →ₗ[K] W) (a : Module.End K V) (a' : Module.End K W)
    (ha : ∀ v, f (a v) = a' (f v)) (n : ℕ) (v : V) :
    f ((a^n) v) = (a'^n) (f v) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pow_succ', Module.End.mul_apply, ha, ih]

omit [CharZero K] in
theorem projection_natural (f : V →ₗ[K] W)
    (a b : Module.End K V) (a' b' : Module.End K W)
    (ha : ∀ v, f (a v) = a' (f v)) (hb : ∀ v, f (b v) = b' (f v))
    (n : ℕ) (v : V) :
    f (projection a b n v) = projection a' b' n (f v) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [projection, LinearMap.add_apply, LinearMap.smul_apply, Module.End.mul_apply,
      map_add, map_smul, ih, intertwine_pow f b b' hb, intertwine_pow f a a' ha]

omit [CharZero K] in
/-- A different annihilator that commutes with both operators keeps its kernel. -/
theorem projection_preserves_ker (a b c : Module.End K V)
    (hca : ∀ v, c (a v) = a (c v)) (hcb : ∀ v, c (b v) = b (c v))
    (n : ℕ) (v : V) (hv : c v = 0) : c (projection a b n v) = 0 := by
  rw [projection_natural c a b a b hca hcb, hv, map_zero]

omit [CharZero K] in
/-- Any subspace preserved by balanced creation/annihilation powers is preserved. -/
theorem projection_mem (a b : Module.End K V) (S : Submodule K V)
    (v : V) (hv : v ∈ S) (hS : ∀ r, (b^r) ((a^r) v) ∈ S) (n : ℕ) :
    projection a b n v ∈ S := by
  induction n with
  | zero => exact hv
  | succ n ih =>
    exact S.add_mem ih (S.smul_mem _ (hS (n+1)))

omit [CharZero K] in
/-- A nonzero central scalar is absorbed into the creation operator. -/
theorem normalized_pair (a b : Module.End K V) (c : K) (hc : c ≠ 0)
    (hab : ∀ v, a (b v) = b (a v) + c • v) (v : V) :
    a ((c⁻¹ • b) v) = (c⁻¹ • b) (a v) + v := by
  simp only [LinearMap.smul_apply, map_smul, hab, smul_add, smul_smul,
    inv_mul_cancel₀ hc, one_smul]

end KanadeRussell.Heisenberg
