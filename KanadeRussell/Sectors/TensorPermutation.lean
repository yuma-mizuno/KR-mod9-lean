import KanadeRussell.Tsuchioka.TwoFields
import KanadeRussell.Tsuchioka.FockGrading
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Permutations of the three tensor factors commute with the concrete Z modes. -/
namespace KanadeRussell.Sectors
open Tsuchioka Tsuchioka.Fock PowerSeries
variable {K : Type*} [Field K] [CharZero K]

noncomputable def permute (σ : Equiv.Perm (Fin 3)) : Space K →ₐ[K] Space K :=
  MvPolynomial.rename (fun s : Fin 3 × Mode => (σ s.1,s.2))

omit [CharZero K] in
@[simp] theorem permute_C (σ : Equiv.Perm (Fin 3)) (c : K) :
    permute σ (MvPolynomial.C c) = MvPolynomial.C c := MvPolynomial.rename_C _ _

omit [CharZero K] in
@[simp] theorem permute_X (σ : Equiv.Perm (Fin 3)) (s : Fin 3 × Mode) :
    permute σ (MvPolynomial.X s : Space K) = MvPolynomial.X (σ s.1,s.2) := MvPolynomial.rename_X _ _

omit [CharZero K] in
theorem tensorExponent_permute (σ : Equiv.Perm (Fin 3)) (i j : Fin 3) :
    tensorExponent (K := K) (σ i) (σ j) = tensorExponent i j := by
  simp [tensorExponent, Fin.val_inj, σ.injective.eq_iff]

omit [CharZero K] in
theorem permute_creationLog (σ : Equiv.Perm (Fin 3)) (j : Fin 3) :
    PowerSeries.map (permute (K := K) σ).toRingHom (creationLog j) = creationLog (σ j) := by
  ext n : 1
  simp only [coeff_map, creationLog, coeff_mk]
  by_cases hn : IsMode n
  · simp only [dif_pos hn, map_sum, map_mul, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      permute_C, permute_X]
    simpa only [tensorExponent_permute] using
      Equiv.sum_comp σ (fun i : Fin 3 => MvPolynomial.C (-4*tensorExponent i (σ j)/(n:K)) *
        MvPolynomial.X (i,(⟨n,hn⟩ : Mode)))
  · simp only [dif_neg hn, map_zero]

theorem permute_creation (σ : Equiv.Perm (Fin 3)) (j : Fin 3) :
    PowerSeries.map (permute (K := K) σ).toRingHom (creation j) = creation (σ j) := by
  rw [creation, FormalSeries.map_exponential _ (constantCoeff_creationLog j), permute_creationLog]
  rfl

omit [CharZero K] in
theorem permute_annihilation (σ : Equiv.Perm (Fin 3)) (w : K) (j : Fin 3) (p : Space K) :
    FormalSeries.mapLaurent (permute σ).toRingHom (annihilation w j p) =
      annihilation w (σ j) (permute σ p) := by
  have he : (FormalSeries.mapLaurent (permute σ).toRingHom).comp (annihilation w j) =
      (annihilation w (σ j)).comp (permute σ).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [annihilation]
    · intro s
      simp only [RingHom.comp_apply, annihilation, MvPolynomial.eval₂Hom_X',
        map_add, FormalSeries.mapLaurent_C, FormalSeries.mapLaurent_single,
        AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, permute_X, permute_C,
        tensorExponent_permute]
  exact DFunLike.congr_fun he p

theorem permute_summand (σ : Equiv.Perm (Fin 3)) (w : K) (j : Fin 3) (p : Space K) :
    FormalSeries.mapLaurent (permute σ).toRingHom (summand w j p) =
      summand w (σ j) (permute σ p) := by
  simp only [summand, LinearMap.coe_mk, AddHom.coe_mk]
  rw [map_mul, FormalSeries.mapLaurent_powerSeries, permute_creation, permute_annihilation]

theorem permute_field (σ : Equiv.Perm (Fin 3)) (w : K) (p : Space K) :
    FormalSeries.mapLaurent (permute σ).toRingHom (field w p) = field w (permute σ p) := by
  change FormalSeries.mapLaurent (permute σ).toRingHom
    ((1/12:K) • ∑ j : Fin 3, summand w j p) = (1/12:K) • ∑ j : Fin 3, summand w j (permute σ p)
  have hscalar (c : K) (f : LaurentSeries (Space K)) :
      FormalSeries.mapLaurent (permute σ).toRingHom (c • f) =
        c • FormalSeries.mapLaurent (permute σ).toRingHom f := by
    apply HahnSeries.ext
    funext n
    simp only [FormalSeries.coeff_mapLaurent, HahnSeries.coeff_smul,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, map_smul]
  rw [hscalar, map_sum]
  simp only [permute_summand]
  exact congrArg (fun f : LaurentSeries (Space K) => (1/12:K) • f)
    (Equiv.sum_comp σ (fun j : Fin 3 => summand w j (permute σ p)))

theorem permute_mode (σ : Equiv.Perm (Fin 3)) (w : K) (i : ℤ) (p : Space K) :
    permute σ (mode w i p) = mode w i (permute σ p) := by
  have h := congrArg (fun f : LaurentSeries (Space K) => f.coeff (-i)) (permute_field σ w p)
  exact h

end KanadeRussell.Sectors
