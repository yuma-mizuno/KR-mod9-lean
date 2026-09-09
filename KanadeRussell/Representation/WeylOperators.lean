import KanadeRussell.Representation.FiniteRootOrbit
import KanadeRussell.Representation.FiniteNilpotence
import KanadeRussell.Representation.LocallyNilpotentExponential
import KanadeRussell.Representation.NilpotentWeylWeight

/-! Global simple-root Weyl automorphisms and their action on full Cartan weights.
The weight calculation takes place on the actual finite stable root orbit and
is transported to the global locally nilpotent exponentials. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
namespace KanadeRussell.Representation
attribute [local instance] LieRing.ofAssociativeRing
variable {K V W : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

local instance : Algebra ℚ (Module.End K V) := Algebra.restrictScalars ℚ K _

omit [CharZero K] in
private theorem restriction_lie (S : Submodule K V) (A B C : Module.End K V)
    (hA : ∀x∈S,A x∈S) (hB : ∀x∈S,B x∈S) (hC : ∀x∈S,C x∈S)
    (h : ⁅A,B⁆ = C) : ⁅A.restrict hA,B.restrict hB⁆ = C.restrict hC := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  have hh := congrArg (fun a : Module.End K V => a (x:V)) h
  simpa only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply,
    LinearMap.restrict_apply, Submodule.coe_sub] using hh

omit [CharZero K] in
private theorem restriction_lie_smul (S : Submodule K V) (A B : Module.End K V) (c : K)
    (hA : ∀x∈S,A x∈S) (hB : ∀x∈S,B x∈S)
    (h : ⁅A,B⁆ = c • B) : ⁅A.restrict hA,B.restrict hB⁆ = c • B.restrict hB := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  have hh := congrArg (fun a : Module.End K V => a (x:V)) h
  simpa only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply,
    LinearMap.restrict_apply, Submodule.coe_sub, Submodule.coe_smul, LinearMap.smul_apply] using hh

omit [CharZero K] in
private theorem restriction_nilpotent (S : Submodule K V) [Module.Finite K S]
    (A : Module.End K V) (hs : ∀x∈S,A x∈S)
    (hA : ∀v:V,∃n:ℕ,(A^n) v=0) : IsNilpotent (A.restrict hs) := by
  apply isNilpotent_of_locallyNilpotent
  intro x
  obtain ⟨n,hn⟩ := hA x
  refine ⟨n, ?_⟩
  apply Subtype.ext
  change S.subtype (((A.restrict hs)^n) x) = 0
  rw [intertwiner_pow_apply (A.restrict hs) A S.subtype (fun _ => rfl)]
  exact hn

namespace PrincipalHighestWeightModule
variable (M : PrincipalHighestWeightModule K V)

noncomputable def simpleWeyl (i : Fin 3) : V ≃ₗ[K] V :=
  ((locallyNilpotentExp (M.action.E i) (M.E_locally_nilpotent i)).trans
    (locallyNilpotentExp (-M.action.F i) (locallyNilpotent_neg _ (M.F_locally_nilpotent i)))).trans
      (locallyNilpotentExp (M.action.E i) (M.E_locally_nilpotent i))

private theorem simpleWeyl_restrict (i : Fin 3) (S : Submodule K V)
    (hE : ∀x∈S,M.action.E i x∈S) (hF : ∀x∈S,M.action.F i x∈S)
    (hnE : IsNilpotent ((M.action.E i).restrict hE))
    (hnF : IsNilpotent ((M.action.F i).restrict hF)) (x : S) :
    S.subtype (nilpotentWeylEquiv ((M.action.E i).restrict hE)
      ((M.action.F i).restrict hF) hnE hnF x) = M.simpleWeyl i (S.subtype x) := by
  simp only [nilpotentWeylEquiv_apply, nilpotentWeyl, Module.End.mul_apply,
    simpleWeyl, LinearEquiv.trans_apply]
  rw [uniformExp_intertwine_locallyNilpotent _ _ hnE (M.E_locally_nilpotent i)
      S.subtype (fun _ => rfl),
    uniformExp_intertwine_locallyNilpotent _ _ hnF.neg (locallyNilpotent_neg _ (M.F_locally_nilpotent i))
      S.subtype (fun _ => rfl),
    uniformExp_intertwine_locallyNilpotent _ _ hnE (M.E_locally_nilpotent i)
      S.subtype (fun _ => rfl)]
  rfl

theorem simpleWeyl_weight (i : Fin 3) (mu : Fin 4 → K) (v : V)
    (hv : v ∈ M.extendedWeightSpace mu) (j : Fin 4) :
    M.extendedCartan j (M.simpleWeyl i v) =
      (mu j - (rootCartanCoefficient i j : K)*mu i.succ) • M.simpleWeyl i v := by
  let S := M.simpleRootOrbit i v
  letI : Module.Finite K S := M.simpleRootOrbit_finite i v mu hv
  let he := M.simpleRootOrbit_E_stable i v mu hv
  let hf := M.simpleRootOrbit_F_stable i v
  let hh := M.simpleRootOrbit_Cartan_stable i v mu hv i.succ
  let hb := M.simpleRootOrbit_Cartan_stable i v mu hv j
  let E := (M.action.E i).restrict he
  let F := (M.action.F i).restrict hf
  let H := (M.action.H i).restrict hh
  let B := (M.extendedCartan j).restrict hb
  have hE : IsNilpotent E := restriction_nilpotent S _ he (M.E_locally_nilpotent i)
  have hF : IsNilpotent F := restriction_nilpotent S _ hf (M.F_locally_nilpotent i)
  have hef : E*F-F*E=H := restriction_lie S _ _ _ he hf hh (M.simpleRoot_EF i)
  have hhe : H*E-E*H=(2:ℚ) • E := by
    rw [← Rat.cast_smul_eq_qsmul K]
    simpa only [Rat.cast_ofNat, Ring.lie_def, H, E, extendedCartan, Fin.cases_succ] using restriction_lie_smul S _ _ 2 hh he (M.simpleRoot_HE i)
  have hhf : H*F-F*H=(-2:ℚ) • F := by
    rw [← Rat.cast_smul_eq_qsmul K]
    simpa only [Rat.cast_neg, Rat.cast_ofNat, Ring.lie_def, H, F, extendedCartan, Fin.cases_succ] using restriction_lie_smul S _ _ (-2) hh hf (M.simpleRoot_HF i)
  have hbe : B*E-E*B=(rootCartanCoefficient i j : ℚ) • E := by
    rw [← Rat.cast_smul_eq_qsmul K, Rat.cast_intCast]
    exact restriction_lie_smul S _ _ _ hb he (M.extendedCartan_E i j)
  have hbf : B*F-F*B=(-(rootCartanCoefficient i j : ℚ)) • F := by
    rw [← Rat.cast_smul_eq_qsmul K, Rat.cast_neg, Rat.cast_intCast]
    exact restriction_lie_smul S _ _ _ hb hf (M.extendedCartan_F i j)
  let x : S := ⟨v,M.self_mem_simpleRootOrbit i v⟩
  have hxH : H x = mu i.succ • x := by
    apply Subtype.ext
    exact (M.mem_extendedWeightSpace mu v).mp hv i.succ
  have hxB : B x = mu j • x := by
    apply Subtype.ext
    exact (M.mem_extendedWeightSpace mu v).mp hv j
  have hw := nilpotentWeyl_weight hE hF hef hhe hhf (rootCartanCoefficient i j : ℚ)
    hbe hbf x (mu i.succ) (mu j) hxH hxB
  have hval := congrArg S.subtype hw
  change M.extendedCartan j (S.subtype (nilpotentWeylEquiv E F hE hF x)) =
    (mu j - ((rootCartanCoefficient i j : ℚ):K)*mu i.succ) •
      S.subtype (nilpotentWeylEquiv E F hE hF x) at hval
  rw [M.simpleWeyl_restrict i S he hf hE hF x, Rat.cast_intCast] at hval
  exact hval

private theorem simpleWeyl_symm_restrict (i : Fin 3) (S : Submodule K V)
    (hE : ∀x∈S,M.action.E i x∈S) (hF : ∀x∈S,M.action.F i x∈S)
    (hnE : IsNilpotent ((M.action.E i).restrict hE))
    (hnF : IsNilpotent ((M.action.F i).restrict hF)) (x : S) :
    S.subtype (nilpotentWeylInv ((M.action.E i).restrict hE)
      ((M.action.F i).restrict hF) x) = (M.simpleWeyl i).symm (S.subtype x) := by
  have heq (y : S) : S.subtype (IsNilpotent.exp (-((M.action.E i).restrict hE)) y) =
      locallyNilpotentExpLinear (-M.action.E i) (locallyNilpotent_neg _ (M.E_locally_nilpotent i)) (S.subtype y) :=
    uniformExp_intertwine_locallyNilpotent _ _ hnE.neg (locallyNilpotent_neg _ (M.E_locally_nilpotent i))
      S.subtype (fun _ => rfl) y
  have hfq (y : S) : S.subtype (IsNilpotent.exp ((M.action.F i).restrict hF) y) =
      locallyNilpotentExpLinear (M.action.F i) (M.F_locally_nilpotent i) (S.subtype y) :=
    uniformExp_intertwine_locallyNilpotent _ _ hnF (M.F_locally_nilpotent i)
      S.subtype (fun _ => rfl) y
  simp only [nilpotentWeylInv, Module.End.mul_apply, heq, hfq]
  simp only [simpleWeyl, LinearEquiv.symm_trans_apply, locallyNilpotentExp_symm, neg_neg]
  rfl

theorem simpleWeyl_symm_weight (i : Fin 3) (mu : Fin 4 → K) (v : V)
    (hv : v ∈ M.extendedWeightSpace mu) (j : Fin 4) :
    M.extendedCartan j ((M.simpleWeyl i).symm v) =
      (mu j - (rootCartanCoefficient i j : K)*mu i.succ) • (M.simpleWeyl i).symm v := by
  let S := M.simpleRootOrbit i v
  letI : Module.Finite K S := M.simpleRootOrbit_finite i v mu hv
  let he := M.simpleRootOrbit_E_stable i v mu hv
  let hf := M.simpleRootOrbit_F_stable i v
  let hh := M.simpleRootOrbit_Cartan_stable i v mu hv i.succ
  let hb := M.simpleRootOrbit_Cartan_stable i v mu hv j
  let E := (M.action.E i).restrict he
  let F := (M.action.F i).restrict hf
  let H := (M.action.H i).restrict hh
  let B := (M.extendedCartan j).restrict hb
  have hE : IsNilpotent E := restriction_nilpotent S _ he (M.E_locally_nilpotent i)
  have hF : IsNilpotent F := restriction_nilpotent S _ hf (M.F_locally_nilpotent i)
  have hef : E*F-F*E=H := restriction_lie S _ _ _ he hf hh (M.simpleRoot_EF i)
  have hhe : H*E-E*H=(2:ℚ) • E := by
    rw [← Rat.cast_smul_eq_qsmul K]
    simpa only [Rat.cast_ofNat, Ring.lie_def, H, E, extendedCartan, Fin.cases_succ] using restriction_lie_smul S _ _ 2 hh he (M.simpleRoot_HE i)
  have hhf : H*F-F*H=(-2:ℚ) • F := by
    rw [← Rat.cast_smul_eq_qsmul K]
    simpa only [Rat.cast_neg, Rat.cast_ofNat, Ring.lie_def, H, F, extendedCartan, Fin.cases_succ] using restriction_lie_smul S _ _ (-2) hh hf (M.simpleRoot_HF i)
  have hbe : B*E-E*B=(rootCartanCoefficient i j : ℚ) • E := by
    rw [← Rat.cast_smul_eq_qsmul K, Rat.cast_intCast]
    exact restriction_lie_smul S _ _ _ hb he (M.extendedCartan_E i j)
  have hbf : B*F-F*B=(-(rootCartanCoefficient i j : ℚ)) • F := by
    rw [← Rat.cast_smul_eq_qsmul K, Rat.cast_neg, Rat.cast_intCast]
    exact restriction_lie_smul S _ _ _ hb hf (M.extendedCartan_F i j)
  let x : S := ⟨v,M.self_mem_simpleRootOrbit i v⟩
  have hxH : H x = mu i.succ • x := by
    apply Subtype.ext
    exact (M.mem_extendedWeightSpace mu v).mp hv i.succ
  have hxB : B x = mu j • x := by
    apply Subtype.ext
    exact (M.mem_extendedWeightSpace mu v).mp hv j
  have hw := nilpotentWeylInv_weight hE hF hef hhe hhf (rootCartanCoefficient i j : ℚ)
    hbe hbf x (mu i.succ) (mu j) hxH hxB
  have hval := congrArg S.subtype hw
  change M.extendedCartan j (S.subtype (nilpotentWeylInv E F x)) =
    (mu j - ((rootCartanCoefficient i j : ℚ):K)*mu i.succ) •
      S.subtype (nilpotentWeylInv E F x) at hval
  rw [M.simpleWeyl_symm_restrict i S he hf hE hF x, Rat.cast_intCast] at hval
  exact hval

end PrincipalHighestWeightModule
end KanadeRussell.Representation
