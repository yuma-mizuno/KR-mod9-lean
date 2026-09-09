import KanadeRussell.Representation.WeightIndependence
import KanadeRussell.Representation.VacuumIntegrability
import KanadeRussell.Representation.FiniteGrades

/-! Principal polynomial grades form an internal direct sum of every homogeneous-seed tensor cyclic module. -/
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Tsuchioka.Fock
open KanadeRussell.Representation KanadeRussell.Heisenberg
variable {K : Type*} [Field K] [CharZero K]

theorem chevalleyF_mem_grade (w : K) (i : Fin 3) (d : ℤ) (p : Space K)
    (hp : p ∈ grade d) : chevalleyF w i p ∈ grade (d+1) := by
  have hc : chevalleyFCoordinates w i 3 = 0 := by
    fin_cases i <;> norm_num [chevalleyFCoordinates, Matrix.cons_val_two, Matrix.cons_val_three]
  have hh : heisenbergMode w (-1) p ∈ grade (d+1) := by
    rw [show (-1:ℤ) = -(firstMode.val:ℤ) from rfl, heisenbergMode_negative]
    have hg := (diagonalCoordinate_mem_grade (K := K) firstMode).mul hp
    change diagonalCoordinate firstMode * p ∈ grade (1+d) at hg
    simpa only [heisenbergNegative_apply, add_comm] using hg
  have hr (beta : RootData.Lattice) : tensorRootMode w beta (-1) p ∈ grade (d+1) := by
    simpa using tensorRootMode_mem_grade w beta (-1) d p hp
  simp only [chevalleyF, tensorModeEvaluate_apply, LinearMap.add_apply, LinearMap.smul_apply,
    hc, zero_smul, add_zero]
  exact (grade (d+1)).add_mem
    ((grade (d+1)).add_mem ((grade (d+1)).smul_mem _ (hr _)) ((grade (d+1)).smul_mem _ (hr _)))
    ((grade (d+1)).smul_mem _ hh)

theorem chevalleyH_mem_grade (w : K) (i : Fin 3) (d : ℤ) (p : Space K)
    (hp : p ∈ grade d) : chevalleyH w i p ∈ grade d := by
  have hr (beta : RootData.Lattice) : tensorRootMode w beta 0 p ∈ grade d := by
    simpa using tensorRootMode_mem_grade w beta 0 d p hp
  simp only [chevalleyH, tensorModeEvaluate_apply, LinearMap.add_apply, LinearMap.smul_apply,
    heisenbergMode_zero, LinearMap.zero_apply, smul_zero, add_zero, Module.End.one_apply]
  exact (grade d).add_mem
    ((grade d).add_mem ((grade d).smul_mem _ (hr _)) ((grade d).smul_mem _ (hr _)))
    ((grade d).smul_mem _ hp)

noncomputable def principalGradeSpan (S : Submodule K (Space K)) : Submodule K (Space K) :=
  ⨆ d : ℤ, S ⊓ grade d

theorem principalGradeSpan_le (S : Submodule K (Space K)) : principalGradeSpan S ≤ S :=
  iSup_le fun _ => inf_le_left

theorem principalGradeSpan_stable_of_shift (S : Submodule K (Space K))
    (a : Module.End K (Space K)) (ha : ∀ p ∈ S, a p ∈ S) (shift : ℤ → ℤ)
    (hshift : ∀ d p, p ∈ grade d → a p ∈ grade (shift d)) :
    ∀ p ∈ principalGradeSpan S, a p ∈ principalGradeSpan S := by
  intro p hp
  refine Submodule.iSup_induction (fun d => S ⊓ grade d)
    (motive := fun p => a p ∈ principalGradeSpan S) hp ?_ ?_ ?_
  · intro d p hp
    exact Submodule.mem_iSup_of_mem (shift d) ⟨ha p hp.1,hshift d p hp.2⟩
  · simp
  · intro p q hp hq
    simpa only [map_add] using (principalGradeSpan S).add_mem hp hq

theorem principalGradeSpan_chevalley_algebra_stable (w : K) (seed : Space K)
    (a : Module.End K (Space K)) (ha : a ∈ chevalleyOperatorAlgebra w) :
    ∀ p ∈ principalGradeSpan (chevalleyCyclicSpan w seed),
      a p ∈ principalGradeSpan (chevalleyCyclicSpan w seed) := by
  induction ha using Algebra.adjoin_induction with
  | mem a ha =>
    rcases ha with ⟨i,rfl⟩ | ⟨i,rfl⟩ | ⟨i,rfl⟩
    · exact principalGradeSpan_stable_of_shift _ _
        (chevalleyCyclicSpan_algebra_mem w seed _ (chevalleyE_mem_algebra w i))
        (fun d => d-1) (chevalleyE_mem_grade w i)
    · exact principalGradeSpan_stable_of_shift _ _
        (chevalleyCyclicSpan_algebra_mem w seed _ (chevalleyF_mem_algebra w i))
        (fun d => d+1) (chevalleyF_mem_grade w i)
    · exact principalGradeSpan_stable_of_shift _ _
        (chevalleyCyclicSpan_algebra_mem w seed _ (chevalleyH_mem_algebra w i))
        id (chevalleyH_mem_grade w i)
  | algebraMap c => intro p hp; exact (principalGradeSpan _).smul_mem c hp
  | add a b ha hb hia hib => intro p hp; exact (principalGradeSpan _).add_mem (hia p hp) (hib p hp)
  | mul a b ha hb hia hib => intro p hp; exact hia _ (hib p hp)

theorem chevalleyCyclicSpan_eq_iSup_grade (w : K) (seed : Space K) (d : ℤ)
    (hd : seed ∈ grade d) :
    chevalleyCyclicSpan w seed = ⨆ e : ℤ, chevalleyCyclicSpan w seed ⊓ grade e := by
  apply le_antisymm _ (principalGradeSpan_le _)
  apply Submodule.span_le.mpr
  rintro _ ⟨a,ha,rfl⟩
  apply principalGradeSpan_chevalley_algebra_stable w seed a ha seed
  exact Submodule.mem_iSup_of_mem d ⟨chevalleyCyclicSpan_seed w seed,hd⟩

theorem tensorCyclicSpan_eq_iSup_grade (w : K) (hw : w^4-w^2+1=0)
    (seed : Space K) (d : ℤ) (hd : seed ∈ grade d) :
    tensorCyclicSpan w seed = ⨆ e : ℤ, tensorCyclicSpan w seed ⊓ grade e := by
  rw [← chevalleyCyclicSpan_eq_tensor w hw seed d hd]
  exact chevalleyCyclicSpan_eq_iSup_grade w seed d hd

theorem grade_iSupIndep : iSupIndep (grade (K := K)) := by
  letI : DirectSum.Decomposition (MvPolynomial.weightedHomogeneousSubmodule K variableWeight) :=
    MvPolynomial.weightedDecomposition K variableWeight
  exact (DirectSum.Decomposition.isInternal
    (MvPolynomial.weightedHomogeneousSubmodule K variableWeight)).submodule_iSupIndep

theorem principalGrade_isInternal (S : Submodule K (Space K))
    (hS : S = ⨆ d : ℤ, S ⊓ grade d) :
    DirectSum.IsInternal (fun d : ℤ => (grade d).comap S.subtype) := by
  classical
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (iSupIndep_comap_subtype grade_iSupIndep S)
  apply Submodule.map_injective_of_injective S.subtype_injective
  rw [Submodule.map_iSup, Submodule.map_top, Submodule.range_subtype]
  simpa only [Submodule.map_comap_subtype] using hS.symm

theorem tensorCyclicSpan_grade_isInternal (w : K) (hw : w^4-w^2+1=0)
    (seed : Space K) (d : ℤ) (hd : seed ∈ grade d) :
    DirectSum.IsInternal (fun e : ℤ => (grade e).comap (tensorCyclicSpan w seed).subtype) :=
  principalGrade_isInternal _ (tensorCyclicSpan_eq_iSup_grade w hw seed d hd)

/-- Relabeling absolute degrees by the degree of the seed preserves the actual internal sum. -/
theorem tensorCyclicSpan_shiftedGrade_isInternal (w : K) (hw : w^4-w^2+1=0)
    (seed : Space K) (d : ℤ) (hd : seed ∈ grade d) :
    DirectSum.IsInternal (fun n : ℤ => (grade (n+d)).comap (tensorCyclicSpan w seed).subtype) := by
  classical
  have h := tensorCyclicSpan_grade_isInternal w hw seed d hd
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (h.submodule_iSupIndep.comp (fun a b hab => by omega))
  have hs : Function.Surjective (fun n : ℤ => n+d) := fun e => ⟨e-d,by simp⟩
  exact (hs.iSup_comp (fun e => (grade e).comap (tensorCyclicSpan w seed).subtype)).trans
    h.submodule_iSup_eq_top

/-- The degree slice of any actual polynomial submodule is finite-dimensional. -/
theorem principalGrade_finite (S : Submodule K (Space K)) (d : ℤ) :
    Module.Finite K ((grade d).comap S.subtype) := by
  letI := grade_finite (K := K) d
  let f : ((grade d).comap S.subtype) →ₗ[K] grade d :=
    { toFun p := ⟨p.val.val,p.property⟩
      map_add' p q := by apply Subtype.ext; rfl
      map_smul' c p := by apply Subtype.ext; rfl }
  apply Module.Finite.of_injective f
  intro p q hp
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun v : grade d => v.val) hp

theorem tensorCyclicSpan_grade_finite (w : K) (seed : Space K) (d : ℤ) :
    Module.Finite K ((grade d).comap (tensorCyclicSpan w seed).subtype) :=
  principalGrade_finite _ d

theorem tensorCyclicSpan_shiftedGrade_finite (w : K) (seed : Space K) (d n : ℤ) :
    Module.Finite K ((grade (n+d)).comap (tensorCyclicSpan w seed).subtype) :=
  tensorCyclicSpan_grade_finite w seed (n+d)

end KanadeRussell.Tsuchioka.Fock
