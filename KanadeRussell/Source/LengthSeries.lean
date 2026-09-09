import KanadeRussell.Source.Contiguity
import KanadeRussell.Infra.Weighted
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-! Length-refined source sums and their two convergent index-shift identities. -/
open PowerSeries PowerSeries.WithPiTopology
open scoped DiscreteUniformity QTheory
namespace KanadeRussell.Source.LengthSeries
open Infra

noncomputable def T (a b : ℕ) : PowerSeries QSeries :=
  weightedSeries (fun mn : ℕ×ℕ => mn.1+2*mn.2) (sourceTerm a b)

theorem hasSum_T (a b : ℕ) :
    HasSum (fun mn : ℕ×ℕ => monomial (mn.1+2*mn.2) (sourceTerm a b mn)) (T a b) :=
  hasSum_weightedSeries _ (summable_sourceTerm a b)

theorem summableCoeff_T (a b : ℕ) : SummableCoeff (T a b) :=
  weightedSeries_summableCoeff _ (summable_sourceTerm a b)

theorem sumCoeff_T (a b : ℕ) : sumCoeff (T a b) = ∑' mn, sourceTerm a b mn :=
  sumCoeff_weightedSeries _ (summable_sourceTerm a b)

theorem constantCoeff_T (a b : ℕ) : constantCoeff (T a b) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  rw [T, weightedSeries, coeff_mk, tsum_eq_single (0,0)]
  · simp [sourceTerm]
  · rintro ⟨m,n⟩ h
    have hn : ¬ 0 = m+2*n := by
      intro he
      apply h
      have hm : m = 0 := by omega
      have hn : n = 0 := by omega
      simp [hm, hn]
    simp only [if_neg hn]

theorem term_second_parameter (a b m n : ℕ) :
    q^(3*n)*sourceTerm a b (m,n) = sourceTerm a (b+3) (m,n) := by
  simp only [sourceTerm]
  rw [← mul_assoc, ← mul_assoc, ← pow_add]
  congr 2
  congr 1
  ring

theorem term_first_shift (a b m n : ℕ) :
    (1-q^(m+1))*sourceTerm a b (m+1,n) = q^(a+1)*sourceTerm (a+2) (b+3) (m,n) := by
  have hc := bInv_qFactorial_step q m (by simpa using isUnit_qPochhammer_q 0 m) (by simpa using isUnit_qPochhammer_q 0 (m+1))
  have he : (m+1)^2+3*(m+1)*n+3*n^2+a*(m+1)+b*n =
      (a+1)+(m^2+3*m*n+3*n^2+(a+2)*m+(b+3)*n) := by ring
  simp only [sourceTerm]
  rw [he, pow_add]
  linear_combination q^(a+1)*q^(m^2+3*m*n+3*n^2+(a+2)*m+(b+3)*n)*bInv (q^3;q^3)_n*hc

theorem term_second_shift (a b m n : ℕ) :
    (1-q^(3*(n+1)))*sourceTerm a b (m,n+1) = q^(b+3)*sourceTerm (a+3) (b+6) (m,n) := by
  have hc := bInv_qFactorial_step (q^3) n (isUnit_qPochhammer_q 2 n) (isUnit_qPochhammer_q 2 (n+1))
  simp only [← pow_mul] at hc
  have he : m^2+3*m*(n+1)+3*(n+1)^2+a*m+b*(n+1) =
      (b+3)+(m^2+3*m*n+3*n^2+(a+3)*m+(b+6)*n) := by ring
  simp only [sourceTerm]
  rw [he, pow_add]
  linear_combination q^(b+3)*q^(m^2+3*m*n+3*n^2+(a+3)*m+(b+6)*n)*bInv (q;q)_m*hc

theorem first_contiguity (a b : ℕ) :
    T a b-T (a+1) b = monomial 1 (q^(a+1))*T (a+2) (b+3) := by
  let g : ℕ×ℕ → PowerSeries QSeries := fun mn =>
    monomial (mn.1+2*mn.2) (sourceTerm a b mn)-monomial (mn.1+2*mn.2) (sourceTerm (a+1) b mn)
  have hi : Function.Injective (fun mn : ℕ×ℕ => (mn.1+1,mn.2)) := by
    rintro ⟨m,n⟩ ⟨k,l⟩ h
    simp only [Prod.mk.injEq, Nat.add_right_cancel_iff] at h
    exact Prod.ext h.1 h.2
  have hz : ∀ mn ∉ Set.range (fun mn : ℕ×ℕ => (mn.1+1,mn.2)), g mn = 0 := by
    rintro ⟨m,n⟩ h
    have hm : m = 0 := by
      by_contra hn
      exact h ⟨(m-1,n), by simp [Nat.sub_add_cancel (by omega : 1 ≤ m)]⟩
    subst m
    simp [g, sourceTerm]
  have hs : HasSum g (T a b-T (a+1) b) := (hasSum_T a b).sub (hasSum_T (a+1) b)
  apply hs.unique
  apply (hi.hasSum_iff hz).mp
  apply ((hasSum_T (a+2) (b+3)).mul_left (monomial 1 (q^(a+1)))).congr_fun
  rintro ⟨m,n⟩
  dsimp only [g, Function.comp_def]
  rw [← map_sub, ← sourceTerm_rescale, ← one_sub_mul, term_first_shift,
    monomial_mul_monomial]
  congr 2; omega

theorem second_contiguity (a b : ℕ) :
    T a b-T a (b+3) = monomial 2 (q^(b+3))*T (a+3) (b+6) := by
  let g : ℕ×ℕ → PowerSeries QSeries := fun mn =>
    monomial (mn.1+2*mn.2) (sourceTerm a b mn)-monomial (mn.1+2*mn.2) (sourceTerm a (b+3) mn)
  have hi : Function.Injective (fun mn : ℕ×ℕ => (mn.1,mn.2+1)) := by
    rintro ⟨m,n⟩ ⟨k,l⟩ h
    simp only [Prod.mk.injEq, Nat.add_right_cancel_iff] at h
    exact Prod.ext h.1 h.2
  have hz : ∀ mn ∉ Set.range (fun mn : ℕ×ℕ => (mn.1,mn.2+1)), g mn = 0 := by
    rintro ⟨m,n⟩ h
    have hn : n = 0 := by
      by_contra hn
      exact h ⟨(m,n-1), by simp [Nat.sub_add_cancel (by omega : 1 ≤ n)]⟩
    subst n
    simp [g, sourceTerm]
  have hs : HasSum g (T a b-T a (b+3)) := (hasSum_T a b).sub (hasSum_T a (b+3))
  apply hs.unique
  apply (hi.hasSum_iff hz).mp
  apply ((hasSum_T (a+3) (b+6)).mul_left (monomial 2 (q^(b+3)))).congr_fun
  rintro ⟨m,n⟩
  dsimp only [g, Function.comp_def]
  rw [← map_sub, ← term_second_parameter, ← one_sub_mul, term_second_shift,
    monomial_mul_monomial]
  congr 2; omega

theorem rescale_T (a b d : ℕ) : rescale (q^d) (T a b) = T (a+d) (b+2*d) := by
  rw [T, weightedSeries_rescale _ _ (summable_sourceTerm a b)]
  congr 1
  funext mn
  rcases mn with ⟨m,n⟩
  simp only [sourceTerm, ← mul_assoc, ← pow_mul, ← pow_add]
  congr 2
  congr 1
  ring


theorem third_recurrence : T 2 3 =
    rescale (q^3) (T 0 0)+monomial 1 (q^3)*rescale (q^3) (T 1 3)+
      monomial 2 (q^6)*rescale (q^3) (T 2 3) := by
  have hs := second_contiguity 2 3
  have hf := first_contiguity 2 6
  simp only [rescale_T]
  norm_num only [Nat.reduceAdd, Nat.reduceMul] at hs hf ⊢
  linear_combination hs+hf

theorem second_recurrence : T 1 3 =
    (1+monomial 1 (q^2))*rescale (q^3) (T 0 0)+monomial 1 (q^3)*rescale (q^3) (T 1 3)+
      monomial 2 (q^6)*rescale (q^3) (T 2 3) := by
  have hf := first_contiguity 1 3
  have ht := third_recurrence
  simp only [rescale_T] at ht ⊢
  norm_num only [Nat.reduceAdd, Nat.reduceMul] at hf ht ⊢
  linear_combination hf+ht

theorem first_recurrence : T 0 0 =
    (1+monomial 1 q+monomial 1 (q^2)+monomial 2 (q^3))*rescale (q^3) (T 0 0)+
      (monomial 1 (q^3)+monomial 2 (q^4))*rescale (q^3) (T 1 3)+
      monomial 2 (q^6)*rescale (q^3) (T 2 3) := by
  have h0 := first_contiguity 0 0
  have h1 := second_contiguity 1 0
  have h2 := first_contiguity 3 6
  have h3 := third_recurrence
  have h4 := first_contiguity 1 3
  simp only [rescale_T] at h3 ⊢
  norm_num only [Nat.reduceAdd, Nat.reduceMul, pow_one] at h0 h1 h2 h3 h4 ⊢
  have he : monomial 1 q*monomial 1 (q^3) = (monomial 2 (q^4):PowerSeries QSeries) := by
    rw [monomial_mul_monomial, ← pow_succ']
  have he' : monomial 1 q*monomial 2 (q^6) =
      (monomial 2 (q^3)*monomial 1 (q^4):PowerSeries QSeries) := by
    simp only [monomial_mul_monomial, ← pow_succ', ← pow_add, Nat.reduceAdd]
  linear_combination h0+h1+h4+(1+monomial 1 q)*h3-monomial 2 (q^3)*h2+
    T 4 9*he+T 5 9*he'

end KanadeRussell.Source.LengthSeries
