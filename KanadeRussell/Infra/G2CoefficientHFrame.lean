import KanadeRussell.Infra.G2CoefficientRigidity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace KanadeRussell.Infra.G2CoefficientRigidity
variable {R : Type*} [CommRing R]

def hPowers : Fin 12 → ℕ × ℕ :=
  ![(0,0),(0,1),(1,0),(1,2),(4,1),(4,4),(6,2),(6,5),(9,4),(9,6),(10,5),(10,6)]
def hSign : Fin 12 → ℤ := ![1,-1,-1,1,1,-1,-1,1,1,-1,-1,1]
def hResidue (h : Fin 12) : Fin 12 × Fin 4 :=
  (⟨(hPowers h).1, by fin_cases h <;> decide⟩,
   ⟨(hPowers h).2%4, Nat.mod_lt _ (by decide)⟩)

theorem hResidue_injective : Function.Injective hResidue := by decide

theorem residue_cases (p : Rˣ) (M : Fin 12) (N : Fin 4) :
    (∃ h, hResidue h = (M,N)) ∨ residueMultiplier p M N = 0 := by
  fin_cases M <;> fin_cases N
  · exact Or.inl ⟨0, by decide⟩
  · exact Or.inl ⟨1, by decide⟩
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inl ⟨2, by decide⟩
  · exact Or.inr rfl
  · exact Or.inl ⟨3, by decide⟩
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inl ⟨5, by decide⟩
  · exact Or.inl ⟨4, by decide⟩
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inl ⟨7, by decide⟩
  · exact Or.inl ⟨6, by decide⟩
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inl ⟨8, by decide⟩
  · exact Or.inr rfl
  · exact Or.inl ⟨9, by decide⟩
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inl ⟨10, by decide⟩
  · exact Or.inl ⟨11, by decide⟩
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inr rfl

theorem residueMultiplier_eq_zero_of_not_h (p : Rˣ) (M : Fin 12) (N : Fin 4)
    (h : ∀ j, hResidue j ≠ (M,N)) : residueMultiplier p M N = 0 :=
  (residue_cases p M N).resolve_left (by rintro ⟨j,hj⟩; exact h j hj)

variable (p : Rˣ) (C : ℤ → ℤ → R)
    (h12 : ∀ M N, C (M+12) N = ((p^(2*(2*M-3*N+11)) : Rˣ) : R)*C M N)
    (h4 : ∀ M N, C M (N+4) = ((p^(2*(-M+2*N+3)) : Rˣ) : R)*C M N)
    (htwo : IsUnit (2 : R))
    (hs : ∀ M N, C (3*N-M+1) N = -C M N)
    (ht : ∀ M N, C M (M-N+1) = -C M N)

include h12 h4 htwo hs ht in
theorem coefficient_h (h : Fin 12) :
    C (hPowers h).1 (hPowers h).2 = (hSign h : R)*C 0 0 := by
  fin_cases h
  · have hr := residue_classification p C h12 h4 htwo hs ht 0 0
    change C 0 0 = (1 : R)*((p^(0 : ℤ) : Rˣ) : R)*C 0 0 at hr
    have hz : C 0 0 = ((p^(0 : ℤ) : Rˣ) : R)*C 0 0 := by
      have hh := translate p C h12 h4 0 0 0 0
      convert hh using 1 <;> norm_num [translationExponent]
    have result : C 0 0 = (1 : R)*C 0 0 := by
      rw [hz, hr]
      have he : p^(0 : ℤ)*p^(0 : ℤ) = 1 := by rw [← zpow_add]; norm_num
      calc
        _ = (1 : R)*((p^(0 : ℤ)*p^(0 : ℤ) : Rˣ) : R)*C 0 0 := by
          rw [Units.val_mul]
          ring
        _ = _ := by rw [he]; simp
    convert result using 1 <;> norm_num [hPowers, hSign, Matrix.cons_val_succ]
  · have hr := residue_classification p C h12 h4 htwo hs ht 0 1
    change C 0 1 = (-1 : R)*((p^(0 : ℤ) : Rˣ) : R)*C 0 0 at hr
    have hz : C 0 1 = ((p^(0 : ℤ) : Rˣ) : R)*C 0 1 := by
      have hh := translate p C h12 h4 0 1 0 0
      convert hh using 1 <;> norm_num [translationExponent]
    have result : C 0 1 = (-1 : R)*C 0 0 := by
      rw [hz, hr]
      have he : p^(0 : ℤ)*p^(0 : ℤ) = 1 := by rw [← zpow_add]; norm_num
      calc
        _ = (-1 : R)*((p^(0 : ℤ)*p^(0 : ℤ) : Rˣ) : R)*C 0 0 := by
          rw [Units.val_mul]
          ring
        _ = _ := by rw [he]; simp
    convert result using 1 <;> norm_num [hPowers, hSign, Matrix.cons_val_succ]
  · have hr := residue_classification p C h12 h4 htwo hs ht 1 0
    change C 1 0 = (-1 : R)*((p^(0 : ℤ) : Rˣ) : R)*C 0 0 at hr
    have hz : C 1 0 = ((p^(0 : ℤ) : Rˣ) : R)*C 1 0 := by
      have hh := translate p C h12 h4 1 0 0 0
      convert hh using 1 <;> norm_num [translationExponent]
    have result : C 1 0 = (-1 : R)*C 0 0 := by
      rw [hz, hr]
      have he : p^(0 : ℤ)*p^(0 : ℤ) = 1 := by rw [← zpow_add]; norm_num
      calc
        _ = (-1 : R)*((p^(0 : ℤ)*p^(0 : ℤ) : Rˣ) : R)*C 0 0 := by
          rw [Units.val_mul]
          ring
        _ = _ := by rw [he]; simp
    convert result using 1 <;> norm_num [hPowers, hSign, Matrix.cons_val_succ]
  · have hr := residue_classification p C h12 h4 htwo hs ht 1 2
    change C 1 2 = (1 : R)*((p^(0 : ℤ) : Rˣ) : R)*C 0 0 at hr
    have hz : C 1 2 = ((p^(0 : ℤ) : Rˣ) : R)*C 1 2 := by
      have hh := translate p C h12 h4 1 2 0 0
      convert hh using 1 <;> norm_num [translationExponent]
    have result : C 1 2 = (1 : R)*C 0 0 := by
      rw [hz, hr]
      have he : p^(0 : ℤ)*p^(0 : ℤ) = 1 := by rw [← zpow_add]; norm_num
      calc
        _ = (1 : R)*((p^(0 : ℤ)*p^(0 : ℤ) : Rˣ) : R)*C 0 0 := by
          rw [Units.val_mul]
          ring
        _ = _ := by rw [he]; simp
    convert result using 1 <;> norm_num [hPowers, hSign, Matrix.cons_val_succ]
  · have hr := residue_classification p C h12 h4 htwo hs ht 4 1
    change C 4 1 = (1 : R)*((p^(0 : ℤ) : Rˣ) : R)*C 0 0 at hr
    have hz : C 4 1 = ((p^(0 : ℤ) : Rˣ) : R)*C 4 1 := by
      have hh := translate p C h12 h4 4 1 0 0
      convert hh using 1 <;> norm_num [translationExponent]
    have result : C 4 1 = (1 : R)*C 0 0 := by
      rw [hz, hr]
      have he : p^(0 : ℤ)*p^(0 : ℤ) = 1 := by rw [← zpow_add]; norm_num
      calc
        _ = (1 : R)*((p^(0 : ℤ)*p^(0 : ℤ) : Rˣ) : R)*C 0 0 := by
          rw [Units.val_mul]
          ring
        _ = _ := by rw [he]; simp
    convert result using 1 <;> norm_num [hPowers, hSign, Matrix.cons_val_succ]
  · have hr := residue_classification p C h12 h4 htwo hs ht 4 0
    change C 4 0 = (-1 : R)*((p^(2 : ℤ) : Rˣ) : R)*C 0 0 at hr
    have hz : C 4 4 = ((p^(-2 : ℤ) : Rˣ) : R)*C 4 0 := by
      have hh := translate p C h12 h4 4 0 0 1
      convert hh using 1 <;> norm_num [translationExponent]
    have result : C 4 4 = (-1 : R)*C 0 0 := by
      rw [hz, hr]
      have he : p^(-2 : ℤ)*p^(2 : ℤ) = 1 := by rw [← zpow_add]; norm_num
      calc
        _ = (-1 : R)*((p^(-2 : ℤ)*p^(2 : ℤ) : Rˣ) : R)*C 0 0 := by
          rw [Units.val_mul]
          ring
        _ = _ := by rw [he]; simp
    convert result using 1 <;> norm_num [hPowers, hSign, Matrix.cons_val_succ]
  · have hr := residue_classification p C h12 h4 htwo hs ht 6 2
    change C 6 2 = (-1 : R)*((p^(0 : ℤ) : Rˣ) : R)*C 0 0 at hr
    have hz : C 6 2 = ((p^(0 : ℤ) : Rˣ) : R)*C 6 2 := by
      have hh := translate p C h12 h4 6 2 0 0
      convert hh using 1 <;> norm_num [translationExponent]
    have result : C 6 2 = (-1 : R)*C 0 0 := by
      rw [hz, hr]
      have he : p^(0 : ℤ)*p^(0 : ℤ) = 1 := by rw [← zpow_add]; norm_num
      calc
        _ = (-1 : R)*((p^(0 : ℤ)*p^(0 : ℤ) : Rˣ) : R)*C 0 0 := by
          rw [Units.val_mul]
          ring
        _ = _ := by rw [he]; simp
    convert result using 1 <;> norm_num [hPowers, hSign, Matrix.cons_val_succ]
  · have hr := residue_classification p C h12 h4 htwo hs ht 6 1
    change C 6 1 = (1 : R)*((p^(2 : ℤ) : Rˣ) : R)*C 0 0 at hr
    have hz : C 6 5 = ((p^(-2 : ℤ) : Rˣ) : R)*C 6 1 := by
      have hh := translate p C h12 h4 6 1 0 1
      convert hh using 1 <;> norm_num [translationExponent]
    have result : C 6 5 = (1 : R)*C 0 0 := by
      rw [hz, hr]
      have he : p^(-2 : ℤ)*p^(2 : ℤ) = 1 := by rw [← zpow_add]; norm_num
      calc
        _ = (1 : R)*((p^(-2 : ℤ)*p^(2 : ℤ) : Rˣ) : R)*C 0 0 := by
          rw [Units.val_mul]
          ring
        _ = _ := by rw [he]; simp
    convert result using 1 <;> norm_num [hPowers, hSign, Matrix.cons_val_succ]
  · have hr := residue_classification p C h12 h4 htwo hs ht 9 0
    change C 9 0 = (1 : R)*((p^(12 : ℤ) : Rˣ) : R)*C 0 0 at hr
    have hz : C 9 4 = ((p^(-12 : ℤ) : Rˣ) : R)*C 9 0 := by
      have hh := translate p C h12 h4 9 0 0 1
      convert hh using 1 <;> norm_num [translationExponent]
    have result : C 9 4 = (1 : R)*C 0 0 := by
      rw [hz, hr]
      have he : p^(-12 : ℤ)*p^(12 : ℤ) = 1 := by rw [← zpow_add]; norm_num
      calc
        _ = (1 : R)*((p^(-12 : ℤ)*p^(12 : ℤ) : Rˣ) : R)*C 0 0 := by
          rw [Units.val_mul]
          ring
        _ = _ := by rw [he]; simp
    convert result using 1 <;> norm_num [hPowers, hSign, Matrix.cons_val_succ]
  · have hr := residue_classification p C h12 h4 htwo hs ht 9 2
    change C 9 2 = (-1 : R)*((p^(4 : ℤ) : Rˣ) : R)*C 0 0 at hr
    have hz : C 9 6 = ((p^(-4 : ℤ) : Rˣ) : R)*C 9 2 := by
      have hh := translate p C h12 h4 9 2 0 1
      convert hh using 1 <;> norm_num [translationExponent]
    have result : C 9 6 = (-1 : R)*C 0 0 := by
      rw [hz, hr]
      have he : p^(-4 : ℤ)*p^(4 : ℤ) = 1 := by rw [← zpow_add]; norm_num
      calc
        _ = (-1 : R)*((p^(-4 : ℤ)*p^(4 : ℤ) : Rˣ) : R)*C 0 0 := by
          rw [Units.val_mul]
          ring
        _ = _ := by rw [he]; simp
    convert result using 1 <;> norm_num [hPowers, hSign, Matrix.cons_val_succ]
  · have hr := residue_classification p C h12 h4 htwo hs ht 10 1
    change C 10 1 = (-1 : R)*((p^(10 : ℤ) : Rˣ) : R)*C 0 0 at hr
    have hz : C 10 5 = ((p^(-10 : ℤ) : Rˣ) : R)*C 10 1 := by
      have hh := translate p C h12 h4 10 1 0 1
      convert hh using 1 <;> norm_num [translationExponent]
    have result : C 10 5 = (-1 : R)*C 0 0 := by
      rw [hz, hr]
      have he : p^(-10 : ℤ)*p^(10 : ℤ) = 1 := by rw [← zpow_add]; norm_num
      calc
        _ = (-1 : R)*((p^(-10 : ℤ)*p^(10 : ℤ) : Rˣ) : R)*C 0 0 := by
          rw [Units.val_mul]
          ring
        _ = _ := by rw [he]; simp
    convert result using 1 <;> norm_num [hPowers, hSign, Matrix.cons_val_succ]
  · have hr := residue_classification p C h12 h4 htwo hs ht 10 2
    change C 10 2 = (1 : R)*((p^(6 : ℤ) : Rˣ) : R)*C 0 0 at hr
    have hz : C 10 6 = ((p^(-6 : ℤ) : Rˣ) : R)*C 10 2 := by
      have hh := translate p C h12 h4 10 2 0 1
      convert hh using 1 <;> norm_num [translationExponent]
    have result : C 10 6 = (1 : R)*C 0 0 := by
      rw [hz, hr]
      have he : p^(-6 : ℤ)*p^(6 : ℤ) = 1 := by rw [← zpow_add]; norm_num
      calc
        _ = (1 : R)*((p^(-6 : ℤ)*p^(6 : ℤ) : Rˣ) : R)*C 0 0 := by
          rw [Units.val_mul]
          ring
        _ = _ := by rw [he]; simp
    convert result using 1 <;> norm_num [hPowers, hSign, Matrix.cons_val_succ]

include h12 h4 htwo hs ht in
/-- Every translated H coefficient has its exact Cooper quadratic factor. -/
theorem coefficient_h_translate (h : Fin 12) (m n : ℤ) :
    C (12*m+(hPowers h).1) (4*n+(hPowers h).2) =
      (hSign h : R)*((p^(2*(12*m*m-12*m*n+4*n*n-m-n+
        (2*m-n)*(hPowers h).1+(2*n-3*m)*(hPowers h).2)) : Rˣ) : R)*C 0 0 := by
  rw [add_comm (12*m), add_comm (4*n), translate p C h12 h4,
    coefficient_h p C h12 h4 htwo hs ht]
  have he : translationExponent (hPowers h).1 (hPowers h).2 m n =
      2*(12*m*m-12*m*n+4*n*n-m-n+(2*m-n)*(hPowers h).1+(2*n-3*m)*(hPowers h).2) := by
    unfold translationExponent
    ring
  rw [he]
  ring

end KanadeRussell.Infra.G2CoefficientRigidity
