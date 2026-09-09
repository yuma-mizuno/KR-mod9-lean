import KanadeRussell.Representation.RankOneStrings

namespace KanadeRussell.Representation
attribute [local instance] LieRing.ofAssociativeRing
variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]

theorem weight_pow_of_commutator (H A : Module.End K V) (c mu : K) (v : V)
    (hHA : ⁅H,A⁆ = c • A) (hv : H v = mu • v) (n : ℕ) :
    H ((A^n) v) = (mu+(n:K)*c) • ((A^n) v) := by
  have ha (x : V) : H (A x) = c • A x + A (H x) := by
    have h := congrArg (fun a : Module.End K V => a x) hHA
    simpa only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply,
      LinearMap.smul_apply, sub_eq_iff_eq_add] using h
  induction n with
  | zero => simpa using hv
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ha, ih, map_smul, ← add_smul]
    push_cast
    congr 1
    ring

theorem rankOne_normal_order (E F H : Module.End K V) (mu : K) (v : V)
    (hEF : ⁅E,F⁆ = H) (hHF : ⁅H,F⁆ = (-2:K) • F)
    (hv : H v = mu • v) (n : ℕ) :
    E ((F^(n+1)) v) = (F^(n+1)) (E v) +
      (((n:K)+1)*(mu-n)) • ((F^n) v) := by
  have ef (x : V) : E (F x) = F (E x) + H x := by
    have h := congrArg (fun a : Module.End K V => a x) hEF
    simpa only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply,
      sub_eq_iff_eq_add, add_comm] using h
  induction n with
  | zero => simpa [hv] using ef v
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ef, ih, map_add, map_smul,
      weight_pow_of_commutator H F (-2) mu v hHF hv (n+1)]
    have hp (m : ℕ) (x : V) : F ((F^m) x) = (F^(m+1)) x := by
      rw [pow_succ', Module.End.mul_apply]
    rw [hp, hp]
    rw [add_assoc, ← add_smul]
    simp only [pow_succ', Module.End.mul_apply]
    push_cast
    congr 2
    ring

omit [CharZero K] in
theorem end_pow_apply_zero_of_le (A : Module.End K V) (v : V) {n m : ℕ}
    (hn : (A^n) v = 0) (hnm : n ≤ m) : (A^m) v = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  rw [add_comm, pow_add, Module.End.mul_apply, hn, map_zero]

/-- A weight vector has a finite-dimensional stable rank-one orbit whenever
both root operators are locally nilpotent. -/
theorem rankOne_locally_finite (E F H : Module.End K V) (mu : K) (v : V)
    (hEF : ⁅E,F⁆ = H) (hHE : ⁅H,E⁆ = (2:K) • E)
    (hHF : ⁅H,F⁆ = (-2:K) • F) (hv : H v = mu • v)
    (hEnil : ∀ x : V, ∃ n : ℕ, (E^n) x = 0)
    (hFnil : ∀ x : V, ∃ n : ℕ, (F^n) x = 0) :
    ∃ S : Submodule K V, v ∈ S ∧ Module.Finite K S ∧
      (∀ x ∈ S, E x ∈ S) ∧ (∀ x ∈ S, F x ∈ S) ∧ (∀ x ∈ S, H x ∈ S) := by
  classical
  let orbit : ℕ × ℕ → V := fun p => (F^p.1) ((E^p.2) v)
  let S := Submodule.span K (Set.range orbit)
  have horbit (a b : ℕ) : (F^a) ((E^b) v) ∈ S :=
    Submodule.subset_span ⟨(a,b), rfl⟩
  have heweight (b : ℕ) : H ((E^b) v) = (mu+(b:K)*2) • ((E^b) v) :=
    weight_pow_of_commutator H E 2 mu v hHE hv b
  have stable (A : Module.End K V) (ha : ∀ a b, A ((F^a) ((E^b) v)) ∈ S) :
      ∀ x ∈ S, A x ∈ S := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨⟨a,b⟩, rfl⟩ := hx; exact ha a b
    | zero => simp
    | add x y hx hy ihx ihy => simpa using S.add_mem ihx ihy
    | smul c x hx ih => simpa using S.smul_mem c ih
  have hEs : ∀ x ∈ S, E x ∈ S := stable E (by
    intro a b
    cases a with
    | zero => simpa [pow_succ', Module.End.mul_apply] using horbit 0 (b+1)
    | succ a =>
      rw [rankOne_normal_order E F H _ _ hEF hHF (heweight b) a]
      apply S.add_mem
      · simpa [pow_succ', Module.End.mul_apply] using horbit (a+1) (b+1)
      · exact S.smul_mem _ (horbit a b))
  have hFs : ∀ x ∈ S, F x ∈ S := stable F (by
    intro a b
    simpa [pow_succ', Module.End.mul_apply] using horbit (a+1) b)
  have hHs : ∀ x ∈ S, H x ∈ S := stable H (by
    intro a b
    rw [weight_pow_of_commutator H F (-2) _ _ hHF (heweight b) a]
    exact S.smul_mem _ (horbit a b))
  obtain ⟨B, hB⟩ := hEnil v
  choose N hN using fun b : Fin B => hFnil ((E^(b:ℕ)) v)
  let T : Set V := Set.range (fun p : Σ b : Fin B, Fin (N b) =>
    (F^(p.2:ℕ)) ((E^(p.1:ℕ)) v)) ∪ {0}
  have hT : T.Finite := (Set.finite_range _).union (Set.finite_singleton _)
  have hsub : Set.range orbit ⊆ T := by
    rintro x ⟨⟨a,b⟩, rfl⟩
    by_cases hb : b < B
    · by_cases ha : a < N ⟨b,hb⟩
      · exact Or.inl ⟨⟨⟨b,hb⟩,⟨a,ha⟩⟩,rfl⟩
      · apply Or.inr
        exact end_pow_apply_zero_of_le F _ (hN ⟨b,hb⟩) (by omega)
    · apply Or.inr
      change (F^a) ((E^b) v) = 0
      rw [end_pow_apply_zero_of_le E v hB (by omega), map_zero]
  have hfinite : Module.Finite K S := Module.Finite.span_of_finite K (hT.subset hsub)
  exact ⟨S, by simpa using horbit 0 0, hfinite, hEs, hFs, hHs⟩

end KanadeRussell.Representation
