import KanadeRussell.Representation.ScalarLambertTransform
import KanadeRussell.Product.Lambert
import Mathlib.NumberTheory.Divisors

/-! The finite scalar transform agrees with the existing convergent Lambert
series. The height-weighted form is obtained by exchanging divisor indices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open PowerSeries PowerSeries.WithPiTopology
open scoped DiscreteUniformity
namespace KanadeRussell.Representation
variable {K : Type*} [Field K]

private theorem hasSum_lambertTerm_expansion (h : ℕ) (hh : 0 < h) :
    HasSum (fun k : ℕ => (k+1) • (q : PowerSeries ℤ)^((k+1)*h)) (Product.lambertTerm h) := by
  have hx : IsTopologicallyNilpotent ((q : PowerSeries ℤ)^h) := by simp [q, hh.ne']
  have hg : HasSum (fun k : ℕ => ((q : PowerSeries ℤ)^h)^k) (bInv (1-q^h)) := by
    rw [hx.bInv_one_sub_eq]
    exact hx.summable_pow.hasSum
  have hc := (hg.mul_antidiagonal hg).mul_left (q^h)
  have he (k : ℕ) : (∑ p ∈ Finset.antidiagonal k,
      ((q : PowerSeries ℤ)^h)^p.1*((q : PowerSeries ℤ)^h)^p.2) =
      (k+1) • ((q : PowerSeries ℤ)^h)^k := by
    calc
      _ = ∑ _p ∈ Finset.antidiagonal k, ((q : PowerSeries ℤ)^h)^k :=
        Finset.sum_congr rfl (fun p hp => by rw [← pow_add, Finset.mem_antidiagonal.mp hp])
      _ = _ := by simp
  rw [Product.lambertTerm, if_neg hh.ne', pow_two]
  apply hc.congr_fun
  intro k
  rw [he]
  have hp : (q : PowerSeries ℤ)^((k+1)*h) = q^h*(q^h)^k := by
    rw [← pow_succ', ← pow_mul, Nat.mul_comm h]
  rw [hp]
  simp only [nsmul_eq_mul]
  ring

theorem coeff_lambertTerm_finite (h n : ℕ) (hh : 0 < h) :
    PowerSeries.coeff n (Product.lambertTerm h) =
      ∑ k ∈ Finset.range (n+1), if (k+1)*h=n then ((k+1 : ℕ) : ℤ) else 0 := by
  classical
  have hc := (hasSum_lambertTerm_expansion h hh).map (PowerSeries.coeff n)
    (continuous_coeff ℤ n)
  rw [← hc.tsum_eq, tsum_eq_sum (s := Finset.range (n+1))]
  · apply Finset.sum_congr rfl
    intro k hk
    simp only [Function.comp_apply, map_nsmul, q, PowerSeries.coeff_X_pow]
    by_cases he : (k+1)*h=n
    · simp [he]
    · simp [he, Ne.symm he]
  · intro k hk
    have hne : n ≠ (k+1)*h := by
      have hk' : n+1 ≤ k := Nat.le_of_not_gt (fun h => hk (Finset.mem_range.mpr h))
      nlinarith
    simp only [Function.comp_apply, map_nsmul, q, PowerSeries.coeff_X_pow, if_neg hne, nsmul_zero]

theorem coeff_lambert_finite (d n : ℕ) (hd : 0 < d) :
    PowerSeries.coeff n (Product.lambert d) =
      ∑ h ∈ Finset.range n, ∑ k ∈ Finset.range (n+1),
        if (k+1)*(h+1)=n then (if d ∣ h+1 then ((k+1 : ℕ) : ℤ) else 0) else 0 := by
  classical
  have hs := Product.hasSum_lambert_multiples d hd
  have hs' : HasSum (fun h : ℕ => if d ∣ h+1 then Product.lambertTerm (h+1) else 0)
      (Product.lambert d) := by
    have h := (hasSum_nat_add_iff' 1).mpr hs
    simpa [Product.lambertTerm] using h
  have hc := hs'.map (PowerSeries.coeff n) (continuous_coeff ℤ n)
  rw [← hc.tsum_eq, tsum_eq_sum (s := Finset.range n)]
  · apply Finset.sum_congr rfl
    intro h hh
    by_cases hdv : d ∣ h+1
    · simp only [Function.comp_apply, if_pos hdv]
      exact coeff_lambertTerm_finite (h+1) n (by omega)
    · simp [hdv]
  · intro h hh
    have hhn : ¬ h+1 ≤ n := by
      have hge : n ≤ h := Nat.le_of_not_gt (fun h => hh (Finset.mem_range.mpr h))
      omega
    by_cases hdv : d ∣ h+1
    · simp [hdv, Product.lambertTerm, q, PowerSeries.coeff_X_pow_mul', hhn]
    · simp [hdv]

theorem scalarLambertTransform_repetition_divisor (d : ℕ) (hd : 0 < d) :
    scalarLambertTransform (fun h k => if d ∣ h+1 then ((k+1 : ℕ) : K) else 0) =
      PowerSeries.map (Int.castRingHom K) (Product.lambert d) := by
  classical
  ext n
  rw [coeff_scalarLambertTransform, PowerSeries.coeff_map, coeff_lambert_finite d n hd]
  simp

/-- The finite transform can also be indexed by positive divisor pairs. -/
theorem coeff_scalarLambertTransform_divisors (f : ℕ → ℕ → K) (n : ℕ) :
    PowerSeries.coeff n (scalarLambertTransform f) =
      ∑ p ∈ n.divisorsAntidiagonal, f (p.1-1) (p.2-1) := by
  classical
  rw [coeff_scalarLambertTransform,
    ← Finset.sum_product (Finset.range n) (Finset.range (n+1))
      (fun p : ℕ × ℕ => if (p.2+1)*(p.1+1)=n then f p.1 p.2 else 0),
    ← Finset.sum_filter]
  apply Finset.sum_bij (fun p _ => (p.1+1,p.2+1))
  · intro p hp
    have he := (Finset.mem_filter.mp hp).2
    apply Nat.mem_divisorsAntidiagonal.mpr
    exact ⟨by simpa only [Nat.mul_comm] using he, by nlinarith⟩
  · intro a ha b hb hab
    have h1 := congrArg Prod.fst hab
    have h2 := congrArg Prod.snd hab
    apply Prod.ext <;> omega
  · intro p hp
    obtain ⟨he, hn⟩ := Nat.mem_divisorsAntidiagonal.mp hp
    obtain ⟨ha,hb⟩ := Nat.ne_zero_of_mem_divisorsAntidiagonal hp
    have hpa : 0 < p.1 := Nat.pos_of_ne_zero ha
    have hpb : 0 < p.2 := Nat.pos_of_ne_zero hb
    have hle1 : p.1 ≤ n := by nlinarith
    have hle2 : p.2 ≤ n := by nlinarith
    refine ⟨(p.1-1,p.2-1), ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩
      · simpa only [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr ha),
          Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hb), Nat.mul_comm] using he
    · apply Prod.ext <;> simp [Nat.sub_add_cancel, Nat.one_le_iff_ne_zero, ha, hb]
  · intro p hp
    simp

private theorem divisor_pair_height_exchange (d n : ℕ) (hd : 0 < d) :
    (∑ p ∈ n.divisorsAntidiagonal, if d ∣ p.1 then (p.1 : K) else 0) =
      (d : K) * ∑ p ∈ n.divisorsAntidiagonal, if d ∣ p.1 then (p.2 : K) else 0 := by
  classical
  rw [← Finset.sum_filter, ← Finset.sum_filter, Finset.mul_sum]
  let S := n.divisorsAntidiagonal.filter (fun p => d ∣ p.1)
  let R : ℕ × ℕ → ℕ × ℕ := fun p => (d*p.2,p.1/d)
  have hmem (p : ℕ × ℕ) (hp : p ∈ S) : R p ∈ S := by
    obtain ⟨hp,hdiv⟩ := Finset.mem_filter.mp hp
    obtain ⟨hprod,hn⟩ := Nat.mem_divisorsAntidiagonal.mp hp
    apply Finset.mem_filter.mpr
    constructor
    · apply Nat.mem_divisorsAntidiagonal.mpr
      refine ⟨?_,hn⟩
      change d*p.2*(p.1/d)=n
      calc
        _ = (d*(p.1/d))*p.2 := by ring
        _ = n := by rw [Nat.mul_div_cancel' hdiv, hprod]
    · exact dvd_mul_right d p.2
  have htwice (p : ℕ × ℕ) (hp : p ∈ S) : R (R p)=p := by
    have hdiv := (Finset.mem_filter.mp hp).2
    apply Prod.ext
    · exact Nat.mul_div_cancel' hdiv
    · exact Nat.mul_div_cancel_left p.2 hd
  change (∑ p ∈ S, (p.1 : K)) = ∑ p ∈ S, (d : K)*(p.2 : K)
  apply Finset.sum_bij (fun p _ => R p)
  · exact hmem
  · intro a ha b hb hab
    have hr := congrArg R hab
    rwa [htwice a ha, htwice b hb] at hr
  · intro p hp
    exact ⟨R p,hmem p hp,htwice p hp⟩
  · intro p hp
    have hdiv := (Finset.mem_filter.mp hp).2
    change (p.1 : K) = (d : K)*(p.1/d : ℕ)
    rw [← Nat.cast_mul, Nat.mul_div_cancel' hdiv]

/-- Restricting heights to multiples of `d` contributes a factor `d` after
exchanging the two positive divisor indices. -/
theorem scalarLambertTransform_height_divisor (d : ℕ) (hd : 0 < d) :
    scalarLambertTransform (fun h _ => if d ∣ h+1 then ((h+1 : ℕ) : K) else 0) =
      (d : K) • PowerSeries.map (Int.castRingHom K) (Product.lambert d) := by
  rw [← scalarLambertTransform_repetition_divisor d hd]
  ext n
  rw [map_smul, coeff_scalarLambertTransform_divisors, coeff_scalarLambertTransform_divisors,
    smul_eq_mul]
  have hf (p : ℕ × ℕ) (hp : p ∈ n.divisorsAntidiagonal) : p.1-1+1=p.1 ∧ p.2-1+1=p.2 := by
    obtain ⟨ha,hb⟩ := Nat.ne_zero_of_mem_divisorsAntidiagonal hp
    omega
  have h1 : (∑ p ∈ n.divisorsAntidiagonal,
      if d ∣ p.1-1+1 then ((p.1-1+1 : ℕ) : K) else 0) =
      ∑ p ∈ n.divisorsAntidiagonal, if d ∣ p.1 then (p.1 : K) else 0 := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [(hf p hp).1]
  have h2 : (∑ p ∈ n.divisorsAntidiagonal,
      if d ∣ p.1-1+1 then ((p.2-1+1 : ℕ) : K) else 0) =
      ∑ p ∈ n.divisorsAntidiagonal, if d ∣ p.1 then (p.2 : K) else 0 := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [(hf p hp).1, (hf p hp).2]
  rw [h1,h2]
  exact divisor_pair_height_exchange d n hd

end KanadeRussell.Representation
