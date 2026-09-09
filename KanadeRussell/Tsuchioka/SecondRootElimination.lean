import KanadeRussell.Tsuchioka.SecondRootCoefficient

/-! Pointwise elimination of the second-root modes by the concrete G2 relation.
All quadratic convolutions used here have proved finite support. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

variable {K : Type*} [Field K] [CharZero K]

theorem quadraticConvolution_mem (w : K) (h : PowerSeries K) (f : Space K)
    (a b : ℤ) (S : Submodule K (Space K))
    (hm : ∀ j : ℤ, mode w (a - j) (mode w (b + j) f) ∈ S) :
    quadraticConvolution w h f a b ∈ S := by
  classical
  rw [quadraticConvolution, finsum_eq_sum _
    (quadraticConvolution_finite w h f a b)]
  exact S.sum_mem (fun j hj => S.smul_mem _ (hm j))

/-- For each input vector, the second-root mode is a finite linear combination
of words of length at most two with the same total index. -/
theorem secondRootMode_mem_of_quadratic (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (i : ℤ) (f : Space K) (S : Submodule K (Space K))
    (hsingle : mode w i f ∈ S) (hcentral : i = 0 → f ∈ S)
    (hpairs : ∀ a b : ℤ, a + b = i → mode w a (mode w b f) ∈ S) :
    secondRootMode w i f ∈ S := by
  obtain ⟨a, b, hab, hgap⟩ := Coefficients.second_indices i
  have hcoeff := Coefficients.second_coefficient_ne_zero w hw a b hgap
  apply (S.smul_mem_iff hcoeff).mp
  have hq₁ := quadraticConvolution_mem w (Scalar.G w 1) f a b S
    (fun j => hpairs (a - j) (b + j) (by omega))
  have hq₂ := quadraticConvolution_mem w (Scalar.G w 1) f b a S
    (fun j => hpairs (b - j) (a + j) (by omega))
  have hf := S.smul_mem
    (Scalar.aPrime w * (w ^ (-2 * a + 2 * b) + w ^ (2 * a - 2 * b)) / 12) hsingle
  have hz : (if i = 0 then (Scalar.cPrime w * (-1 : K) ^ a / 48) • f else 0) ∈ S := by
    split_ifs with hi
    · exact S.smul_mem _ (hcentral hi)
    · exact S.zero_mem
  have ht := S.smul_mem ((-1 : K) ^ i / 3) hsingle
  have he := G2_anticommutator w hw f a b
  rw [hab] at he
  convert S.sub_mem (S.sub_mem (S.sub_mem (S.add_mem hq₁ hq₂) hf) hz) ht using 1
  rw [he]
  module

/-- Stability under all first-root modes implies stability under every
second-root mode. This is a consequence of the constructed G2 identity. -/
theorem secondRootMode_mem_of_mode_stable (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (S : Submodule K (Space K))
    (hstable : ∀ j : ℤ, ∀ f ∈ S, mode w j f ∈ S)
    (i : ℤ) (f : Space K) (hf : f ∈ S) : secondRootMode w i f ∈ S :=
  secondRootMode_mem_of_quadratic w hw i f S (hstable i f hf) (fun _ => hf)
    (fun a b _ => hstable a _ (hstable b f hf))

/-- The elimination respects total mode index, not only the ungraded span. -/
theorem secondRootMode_mem_of_graded_mode_stable (w : K)
    (hw : w ^ 4 - w ^ 2 + 1 = 0) (S : ℤ → Submodule K (Space K))
    (hstable : ∀ i d : ℤ, ∀ f ∈ S d, mode w i f ∈ S (i + d))
    (i d : ℤ) (f : Space K) (hf : f ∈ S d) :
    secondRootMode w i f ∈ S (i + d) := by
  apply secondRootMode_mem_of_quadratic w hw i f (S (i + d)) (hstable i d f hf)
  · intro hi
    simpa only [hi, zero_add] using hf
  · intro a b hab
    have hh := hstable a (b + d) _ (hstable b d f hf)
    simpa only [← add_assoc, hab] using hh

end KanadeRussell.Tsuchioka.Fock
