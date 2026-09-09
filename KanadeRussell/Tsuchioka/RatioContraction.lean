import KanadeRussell.Tsuchioka.NormalProductSymmetry
import KanadeRussell.Tsuchioka.SourceEmbedding
import KanadeRussell.Tsuchioka.FourierSymmetry

/-!
Coefficient extraction for multiplication by an ordinary source series in
the field-variable ratio, and comparison of the two expansion orders.
-/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.FormalSeries

variable {A : Type*} [CommRing A]

theorem laurent_convolution_finite (f g : LaurentSeries A) (d : ℤ) :
    (Function.support (fun i => f.coeff i * g.coeff (d - i))).Finite := by
  apply (Set.finite_Icc f.order (d - g.order)).subset
  intro i hi
  have hf : f.coeff i ≠ 0 := by
    intro hz
    exact hi (by simp [hz])
  have hg : g.coeff (d - i) ≠ 0 := by
    intro hz
    exact hi (by simp [hz])
  have hfl := HahnSeries.order_le_of_coeff_ne_zero hf
  have hgl := HahnSeries.order_le_of_coeff_ne_zero hg
  exact ⟨hfl, by omega⟩

theorem coeff_finsum (f : ℤ → LaurentSeries A) (hf : Function.HasFiniteSupport f) (a : ℤ) :
    (∑ᶠ i : ℤ, f i).coeff a = ∑ᶠ i : ℤ, (f i).coeff a :=
  (HahnSeries.coeff.addMonoidHom a).map_finsum hf

end KanadeRussell.Tsuchioka.FormalSeries

namespace KanadeRussell.Tsuchioka.Fock

open FormalSeries

variable {K : Type*} [Field K] [CharZero K]

theorem laurent_ratioEmbedding_coeff (h : PowerSeries K) (n : ℤ) :
    ((ratioEmbedding h : PowerSeries (LaurentSeries (Space K))) :
      LaurentSeries (LaurentSeries (Space K))).coeff n =
      HahnSeries.single (-n) (MvPolynomial.C (positive h n)) := by
  by_cases hn : n < 0
  · rw [PowerSeries.coeff_coe, if_pos hn]
    simp [positive, show ¬ 0 ≤ n by omega]
  · lift n to ℕ using (by omega : 0 ≤ n)
    rw [LaurentSeries.coeff_coe_powerSeries, coeff_ratioEmbedding, positive_nat]

/-- Exact coefficient extraction of the ratio-series product. Its finiteness
comes from the actual Laurent convolution, not a chosen truncation. -/
theorem ratio_product_coeff (h : PowerSeries K) (f : LaurentSeries (LaurentSeries (Space K)))
    (a b : ℤ) :
    (((ratioEmbedding h : LaurentSeries (LaurentSeries (Space K))) * f).coeff b).coeff a =
      contract (fun n => MvPolynomial.C (positive h n)) f a b := by
  rw [laurent_coeff_mul_finsum,
    coeff_finsum _ (laurent_convolution_finite (ratioEmbedding h) f b)]
  unfold contract
  apply finsum_congr
  intro n
  rw [laurent_ratioEmbedding_coeff, HahnSeries.coeff_single_mul]
  simp only [sub_neg_eq_add]

/-- Ratio-series contraction has finite support even before imposing the
stronger separate bounds available for a normal product. -/
theorem ratio_contraction_finite (h : PowerSeries K)
    (f : LaurentSeries (LaurentSeries (Space K))) (a b : ℤ) :
    (Function.support (fun n => MvPolynomial.C (positive h n) *
      (f.coeff (b - n)).coeff (a + n))).Finite := by
  have hf := laurent_convolution_finite
    (ratioEmbedding h : LaurentSeries (LaurentSeries (Space K))) f b
  apply hf.subset
  intro n hn
  change (ratioEmbedding h : LaurentSeries (LaurentSeries (Space K))).coeff n *
    f.coeff (b - n) ≠ 0
  intro hz
  have ha := congrArg (fun z : LaurentSeries (Space K) => z.coeff a) hz
  rw [laurent_ratioEmbedding_coeff, HahnSeries.coeff_single_mul] at ha
  exact hn (by simpa only [sub_neg_eq_add, HahnSeries.coeff_zero] using ha)

/-- The reversed expansion uses the reflected scalar sequence against the
same normal product. The normal product itself has proved exchange symmetry. -/
theorem normalProduct_contract_swapped (w : K) (s t : Fin 3) (f : Space K)
    (c : ℤ → Space K) (a b : ℤ) :
    contract c (normalProduct w t s f) b a =
      contract (reflect c) (normalProduct w s t f) a b := by
  unfold contract
  apply finsum_eq_of_bijective (fun n : ℤ => -n)
    (Function.Involutive.bijective (fun n : ℤ => neg_neg n))
  intro n
  rw [normalProduct_swapped]
  simp only [reflect, neg_neg, sub_neg_eq_add, sub_eq_add_neg]

/-- Sum of the forward and reversed scalar expansions, before substituting
the explicit Fourier identity for the scalar kernel. -/
theorem normalProduct_symmetric_expansions (w : K) (s t : Fin 3) (f : Space K)
    (h : PowerSeries K) (a b : ℤ) :
    (((ratioEmbedding h : LaurentSeries (LaurentSeries (Space K))) *
        normalProduct w s t f).coeff b).coeff a +
      (((ratioEmbedding h : LaurentSeries (LaurentSeries (Space K))) *
        normalProduct w t s f).coeff a).coeff b =
      contract (fun n => MvPolynomial.C (Scalar.symmetricFourier h n))
        (normalProduct w s t f) a b := by
  obtain ⟨l, r, hb⟩ := normalProduct_bounded w s t f
  rw [ratio_product_coeff, ratio_product_coeff,
    normalProduct_contract_swapped w s t f (fun n => MvPolynomial.C (positive h n)) a b]
  have hc : (fun n => (MvPolynomial.C (Scalar.symmetricFourier h n) : Space K)) =
      (fun n => MvPolynomial.C (positive h n)) +
        reflect (fun n => MvPolynomial.C (positive h n)) := by
    funext n
    simp [Scalar.symmetricFourier, reflect]
  rw [hc, contract_add hb]

/-- Difference of the two expansion orders, with the source's antisymmetric
Fourier kernel retained as a coefficient function. -/
theorem normalProduct_antisymmetric_expansions (w : K) (s t : Fin 3) (f : Space K)
    (h : PowerSeries K) (a b : ℤ) :
    (((ratioEmbedding h : LaurentSeries (LaurentSeries (Space K))) *
        normalProduct w s t f).coeff b).coeff a -
      (((ratioEmbedding h : LaurentSeries (LaurentSeries (Space K))) *
        normalProduct w t s f).coeff a).coeff b =
      contract (fun n => MvPolynomial.C (Scalar.antisymmetricFourier h n))
        (normalProduct w s t f) a b := by
  obtain ⟨l, r, hb⟩ := normalProduct_bounded w s t f
  rw [ratio_product_coeff, ratio_product_coeff,
    normalProduct_contract_swapped w s t f (fun n => MvPolynomial.C (positive h n)) a b]
  have hc : (fun n => (MvPolynomial.C (Scalar.antisymmetricFourier h n) : Space K)) =
      (fun n => MvPolynomial.C (positive h n)) -
        reflect (fun n => MvPolynomial.C (positive h n)) := by
    funext n
    simp [Scalar.antisymmetricFourier, reflect]
  rw [hc, contract_sub hb]

end KanadeRussell.Tsuchioka.Fock
