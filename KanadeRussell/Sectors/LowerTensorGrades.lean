import KanadeRussell.Sectors.SkewSeed
import KanadeRussell.Tsuchioka.AlternatingGrading
import KanadeRussell.Representation.AffineCyclicity

/-! Tensor-factor symmetry supplies the exact lower degrees of the actual cyclic sectors. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace KanadeRussell.Sectors
open Tsuchioka Tsuchioka.Fock PowerSeries
variable {K : Type*} [Field K] [CharZero K]

theorem permute_tensorRootCreationLog (σ : Equiv.Perm (Fin 3)) (w : K)
    (beta : RootData.Lattice) (j : Fin 3) :
    PowerSeries.map (permute (K := K) σ).toRingHom (tensorRootCreationLog w beta j) =
      tensorRootCreationLog w beta (σ j) := by
  ext n : 1
  simp only [coeff_map, tensorRootCreationLog, coeff_mk]
  by_cases hn : IsMode n
  · simp [hn]
  · simp [hn]

theorem permute_tensorRootCreation (σ : Equiv.Perm (Fin 3)) (w : K)
    (beta : RootData.Lattice) (j : Fin 3) :
    PowerSeries.map (permute (K := K) σ).toRingHom (tensorRootCreation w beta j) =
      tensorRootCreation w beta (σ j) := by
  rw [tensorRootCreation, FormalSeries.map_exponential _ (constantCoeff_tensorRootCreationLog w beta j),
    permute_tensorRootCreationLog]
  rfl

theorem permute_tensorRootAnnihilation (σ : Equiv.Perm (Fin 3)) (w : K)
    (beta : RootData.Lattice) (j : Fin 3) (p : Space K) :
    FormalSeries.mapLaurent (permute σ).toRingHom (tensorRootAnnihilation w beta j p) =
      tensorRootAnnihilation w beta (σ j) (permute σ p) := by
  have he : (FormalSeries.mapLaurent (permute σ).toRingHom).comp (tensorRootAnnihilation w beta j) =
      (tensorRootAnnihilation w beta (σ j)).comp (permute σ).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [tensorRootAnnihilation]
    · intro s
      simp only [RingHom.comp_apply, tensorRootAnnihilation, MvPolynomial.eval₂Hom_X',
        map_add, FormalSeries.mapLaurent_C, FormalSeries.mapLaurent_single,
        AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, permute_X, permute_C,
        σ.injective.eq_iff]
  exact DFunLike.congr_fun he p

theorem permute_tensorRootSummand (σ : Equiv.Perm (Fin 3)) (w : K)
    (beta : RootData.Lattice) (j : Fin 3) (p : Space K) :
    FormalSeries.mapLaurent (permute σ).toRingHom (tensorRootSummand w beta j p) =
      tensorRootSummand w beta (σ j) (permute σ p) := by
  simp only [tensorRootSummand, LinearMap.coe_mk, AddHom.coe_mk]
  rw [map_mul, FormalSeries.mapLaurent_powerSeries,
    permute_tensorRootCreation, permute_tensorRootAnnihilation]

theorem permute_tensorRootField (σ : Equiv.Perm (Fin 3)) (w : K)
    (beta : RootData.Lattice) (p : Space K) :
    FormalSeries.mapLaurent (permute σ).toRingHom (tensorRootField w beta p) =
      tensorRootField w beta (permute σ p) := by
  change FormalSeries.mapLaurent (permute σ).toRingHom
    ((1/12:K) • ∑ j : Fin 3, tensorRootSummand w beta j p) =
      (1/12:K) • ∑ j : Fin 3, tensorRootSummand w beta j (permute σ p)
  have hscalar (c : K) (f : LaurentSeries (Space K)) :
      FormalSeries.mapLaurent (permute σ).toRingHom (c • f) =
        c • FormalSeries.mapLaurent (permute σ).toRingHom f := by
    apply HahnSeries.ext
    funext n
    simp only [FormalSeries.coeff_mapLaurent, HahnSeries.coeff_smul,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, map_smul]
  rw [hscalar, map_sum]
  simp only [permute_tensorRootSummand]
  exact congrArg (fun f : LaurentSeries (Space K) => (1/12:K) • f)
    (Equiv.sum_comp σ (fun j : Fin 3 => tensorRootSummand w beta j (permute σ p)))

theorem permute_tensorRootMode (σ : Equiv.Perm (Fin 3)) (w : K)
    (beta : RootData.Lattice) (i : ℤ) (p : Space K) :
    permute σ (tensorRootMode w beta i p) = tensorRootMode w beta i (permute σ p) := by
  exact congrArg (fun f : LaurentSeries (Space K) => f.coeff (-i))
    (permute_tensorRootField σ w beta p)

theorem permute_diagonalDerivative (σ : Equiv.Perm (Fin 3)) (n : Mode) (p : Space K) :
    permute σ (diagonalDerivative n p) = diagonalDerivative n (permute σ p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add,hp,hq]
  | mul_X p s hp =>
    simp only [Derivation.leibniz, map_add, map_mul, permute_X, diagonalDerivative_X, hp,
      smul_eq_mul]
    split_ifs <;> simp

theorem permute_diagonalCoordinate (σ : Equiv.Perm (Fin 3)) (n : Mode) :
    permute σ (diagonalCoordinate (K := K) n) = diagonalCoordinate n := by
  simp only [diagonalCoordinate, map_sum, permute_X]
  exact Equiv.sum_comp σ (fun j : Fin 3 => MvPolynomial.X (j,n))

theorem permute_heisenbergMode (σ : Equiv.Perm (Fin 3)) (w : K) (i : ℤ) (p : Space K) :
    permute σ (heisenbergMode w i p) = heisenbergMode w i (permute σ p) := by
  unfold heisenbergMode
  split
  · split
    · simp only [heisenbergPositive_apply, map_smul, permute_diagonalDerivative]
    · simp only [heisenbergNegative_apply, map_mul, permute_diagonalCoordinate]
  · simp

theorem permute_tensorModeEvaluate (σ : Equiv.Perm (Fin 3)) (w : K) (i : ℤ)
    (c : Fin 4 → K) (p : Space K) :
    permute σ (tensorModeEvaluate w i c p) = tensorModeEvaluate w i c (permute σ p) := by
  simp only [tensorModeEvaluate_apply, LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.one_apply, map_add, map_smul, permute_tensorRootMode, permute_heisenbergMode]

theorem permute_chevalleyOperatorAlgebra (σ : Equiv.Perm (Fin 3)) (w : K)
    (a : Module.End K (Space K)) (ha : a ∈ chevalleyOperatorAlgebra w) :
    ∀ p, permute σ (a p) = a (permute σ p) := by
  induction ha using Algebra.adjoin_induction with
  | mem a ha =>
    rcases ha with ⟨i,rfl⟩ | ⟨i,rfl⟩ | ⟨i,rfl⟩
    all_goals exact fun p => permute_tensorModeEvaluate σ w _ _ p
  | algebraMap c => intro p; exact map_smul (permute σ) c p
  | add a b ha hb hia hib => intro p; simp only [LinearMap.add_apply,map_add,hia,hib]
  | mul a b ha hb hia hib => intro p; simp only [Module.End.mul_apply,hia,hib]

/-- Every vector of a cyclic sector retains the seed's tensor-transposition sign. -/
theorem tensorCyclicSpan_permute_neg (σ : Equiv.Perm (Fin 3)) (w : K)
    (hw : w^4-w^2+1=0) (seed : Space K) (d : ℤ) (hd : seed ∈ grade d)
    (hs : permute σ seed = -seed) (p : Space K) (hp : p ∈ tensorCyclicSpan w seed) :
    permute σ p = -p := by
  rw [← chevalleyCyclicSpan_eq_tensor w hw seed d hd] at hp
  let S : Submodule K (Space K) := LinearMap.ker ((permute σ).toLinearMap + LinearMap.id)
  have hle : chevalleyCyclicSpan w seed ≤ S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a,ha,rfl⟩
    change permute σ (a seed) + a seed = 0
    rw [permute_chevalleyOperatorAlgebra σ w a ha, hs, map_neg, neg_add_cancel]
  have hx := hle hp
  change permute σ p + p = 0 at hx
  exact add_eq_zero_iff_eq_neg.mp hx

theorem tensorCyclicSpan_le_skewSpace (w : K) (hw : w^4-w^2+1=0) :
    tensorCyclicSpan w (skewSeed : Space K) ≤ skewSpace := by
  intro p hp
  rw [mem_skewSpace]
  exact tensorCyclicSpan_permute_neg swap01 w hw skewSeed 1 skewSeed_grade
    ((mem_skewSpace skewSeed).mp skewSeed_mem) p hp

theorem tensorCyclicSpan_le_alternatingSpace (w : K) (hw : w^4-w^2+1=0) :
    tensorCyclicSpan w (alternatingSeed : Space K) ≤ alternatingSpace := by
  intro p hp a b hab
  exact tensorCyclicSpan_permute_neg (Equiv.swap a b) w hw alternatingSeed 3 alternatingSeed_grade
    (alternatingSeed_mem a b hab) p hp

theorem tensor_skew_grade_below_one (w : K) (hw : w^4-w^2+1=0) (e : ℤ) (he : e < 1) :
    tensorCyclicSpan w (skewSeed : Space K) ⊓ grade e = ⊥ := by
  apply le_antisymm _ bot_le
  intro p hp
  rw [Submodule.mem_bot]
  let v : skewSpace (K := K) := ⟨p,tensorCyclicSpan_le_skewSpace w hw hp.1⟩
  have hv : v ∈ skewGrade (e-1) := by
    change p ∈ grade (e-1+1)
    simpa using hp.2
  rw [skewGrade_negative (e-1) (by omega), Submodule.mem_bot] at hv
  exact congrArg Subtype.val hv

theorem tensor_alternating_grade_below_three (w : K) (hw : w^4-w^2+1=0)
    (e : ℤ) (he : e < 3) : tensorCyclicSpan w (alternatingSeed : Space K) ⊓ grade e = ⊥ := by
  apply le_antisymm _ bot_le
  intro p hp
  rw [Submodule.mem_bot]
  exact alternating_grade_lt_three e he p (tensorCyclicSpan_le_alternatingSpace w hw hp.1) hp.2

theorem tensor_vacuum_grade_below_zero (w : K) (e : ℤ) (he : e < 0) :
    tensorCyclicSpan w (1 : Space K) ⊓ grade e = ⊥ := by
  rw [grade_negative e he, inf_bot_eq]

end KanadeRussell.Sectors
