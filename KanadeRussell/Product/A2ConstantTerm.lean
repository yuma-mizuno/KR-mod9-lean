import KanadeRussell.Infra.JacobiTrisection
import KanadeRussell.Product.LaurentSubstitution
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-! Constant-term proof of the shifted A2 product. The auxiliary Laurent
variable is projected out by a continuous linear map, not by evaluation at zero. -/
open MvLaurentSeries PowerSeries PowerSeries.WithPiTopology
open scoped DiscreteUniformity QTheory
namespace KanadeRussell.Product.A2ConstantTerm
open Infra.ThetaAddition
abbrev L := MvLaurentSeries Unit ℤ
abbrev LZ := MvLaurentSeries Bool ℤ

def inclusion : Unit ↪ Bool := ⟨fun _ => false, by intro a b _; cases a; cases b; rfl⟩
noncomputable def lift : L →+* LZ := mapVar ℤ inclusion
noncomputable def liftUnit : Lˣ →* LZˣ := Units.map lift.toMonoidHom
noncomputable def ct : LZ →ₗ[ℤ] L := comapVar ℤ inclusion 0
noncomputable def t (n : ℤ) : Lˣ := xPowUnits () n
noncomputable def z : LZˣ := xPowUnits true 1
noncomputable def eta (d : ℤ) : L := (xPow () d; xPow () d)_∞

private theorem liftUnit_neg_one : liftUnit (-1) = (-1 : LZˣ) := by
  apply Units.ext
  simp [liftUnit]

private theorem t_eq_zpow (n : ℤ) : t n = (t 1)^n := by
  simp only [t, xPowUnits_zpow, one_mul]

private theorem z_zpow (n : ℤ) : ((z^n : LZˣ) : LZ) = xPow true n := by
  simp only [z, xPowUnits_zpow, one_mul]
  rfl

private theorem liftUnit_val (u : Lˣ) : ((liftUnit u : LZˣ) : LZ) = lift (u : L) := rfl

private theorem jacobiTerm_lift (p u : Lˣ) (n : ℤ) :
    jacobiTerm (liftUnit p) (liftUnit u * z) n =
      lift (jacobiTerm p u n) * xPow true n := by
  have he : ((-1 : LZˣ)^n * (liftUnit u * z)^n) * (liftUnit p)^(n*(n-1)) =
      liftUnit (((-1 : Lˣ)^n * u^n) * p^(n*(n-1))) * z^n := by
    simp only [map_mul, map_zpow, liftUnit_neg_one, mul_zpow]
    apply Additive.ofMul.injective
    simp only [ofMul_mul]
    abel
  unfold jacobiTerm
  rw [he, Units.val_mul, liftUnit_val, z_zpow]

private theorem ct_monomial (b : L) (n : ℤ) :
    ct (lift b * xPow true n) = if n = 0 then b else 0 := by
  have hi : true ∉ Set.range inclusion := by simp [inclusion]
  simpa only [ct, lift, Finsupp.single_zero, map_zero, eq_comm] using
    comapVar_mapVar_mul_xPow_eq_ite inclusion true hi 0 n b

private theorem ct_factor_term (b : L) (p u : Lˣ) (n : ℤ) :
    ct (lift b * jacobiTerm (liftUnit p) (liftUnit u*z) n) =
      if n = 0 then b else 0 := by
  rw [jacobiTerm_lift, ← mul_assoc, ← map_mul, ct_monomial]
  split_ifs with hn
  · subst n
    simp [jacobiTerm]
  · rfl

private theorem base_terms (r s : ℤ) :
    jacobiTerm (t 3) (t 0) (-r-s) * jacobiTerm (t 3) (t 2) r *
      jacobiTerm (t 3) (t 4) s = xPow () (6*(r^2+r*s+s^2)+2*r+4*s) := by
  change _ = ((t (6*(r^2+r*s+s^2)+2*r+4*s) : Lˣ) : L)
  unfold jacobiTerm
  rw [← Units.val_mul, ← Units.val_mul]
  congr 1
  rw [t_eq_zpow 0, t_eq_zpow 2, t_eq_zpow 3, t_eq_zpow 4,
    t_eq_zpow (6*(r^2+r*s+s^2)+2*r+4*s)]
  simp only [← zpow_mul]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow]
  module

private theorem ct_factor_triple (b : L) (n0 n1 n2 : ℤ) :
    ct (lift b * (jacobiTerm (liftUnit (t 3)) (liftUnit (t 0)*z) n0 *
      jacobiTerm (liftUnit (t 3)) (liftUnit (t 2)*z) n1 *
      jacobiTerm (liftUnit (t 3)) (liftUnit (t 4)*z) n2)) =
      if n0+n1+n2 = 0 then b*xPow () (6*(n1^2+n1*n2+n2^2)+2*n1+4*n2) else 0 := by
  have he : lift b * (jacobiTerm (liftUnit (t 3)) (liftUnit (t 0)*z) n0 *
      jacobiTerm (liftUnit (t 3)) (liftUnit (t 2)*z) n1 *
      jacobiTerm (liftUnit (t 3)) (liftUnit (t 4)*z) n2) =
      lift (b * (jacobiTerm (t 3) (t 0) n0 * jacobiTerm (t 3) (t 2) n1 *
        jacobiTerm (t 3) (t 4) n2)) * xPow true (n0+n1+n2) := by
    simp only [jacobiTerm_lift, map_mul, xPow_add]
    ring
  rw [he, ct_monomial]
  split_ifs with hn
  · have he0 : n0 = -n1-n2 := by omega
    rw [he0, base_terms]
  · rfl

private theorem nilpotent_lift_t (d : ℤ) (hd : 0 < d) :
    IsTopologicallyNilpotent ((liftUnit (t d) : LZˣ) : LZ) := by
  change IsTopologicallyNilpotent (lift (xPow () d))
  exact ((isTopologicallyNilpotent_xPow_iff () d).mpr hd).map (mapVar_continuous inclusion)

noncomputable def triple : LZ :=
  jacobi (liftUnit (t 3)) (liftUnit (t 0)*z) *
    jacobi (liftUnit (t 3)) (liftUnit (t 2)*z) *
    jacobi (liftUnit (t 3)) (liftUnit (t 4)*z)

private theorem hasSum_projected (b : L) :
    HasSum (fun ns : (ℤ × ℤ) × ℤ => ct (lift b *
      (jacobiTerm (liftUnit (t 3)) (liftUnit (t 0)*z) ns.1.1 *
       jacobiTerm (liftUnit (t 3)) (liftUnit (t 2)*z) ns.1.2 *
       jacobiTerm (liftUnit (t 3)) (liftUnit (t 4)*z) ns.2)))
      (ct (lift b * triple)) := by
  have hp := nilpotent_lift_t 3 (by decide)
  exact ((((hasSum_jacobiTerm _ (liftUnit (t 0)*z) hp).mul_of_nonarchimedean'
    (hasSum_jacobiTerm _ (liftUnit (t 2)*z) hp)).mul_of_nonarchimedean'
    (hasSum_jacobiTerm _ (liftUnit (t 4)*z) hp)).mul_left (lift b)).map ct
      (comapVar_continuous inclusion 0)

private def lattice (rs : ℤ × ℤ) : (ℤ × ℤ) × ℤ := ((-rs.1-rs.2,rs.1),rs.2)

private theorem lattice_injective : Function.Injective lattice := by
  rintro ⟨r,s⟩ ⟨u,v⟩ h
  simp only [lattice, Prod.mk.injEq] at h ⊢
  omega

private theorem hasSum_core_mul (b : L) :
    HasSum (fun rs : ℤ × ℤ => b*xPow () (6*(rs.1^2+rs.1*rs.2+rs.2^2)+2*rs.1+4*rs.2))
      (ct (lift b * triple)) := by
  have hoff (ns : (ℤ × ℤ) × ℤ) (hn : ns ∉ Set.range lattice) :
      ct (lift b * (jacobiTerm (liftUnit (t 3)) (liftUnit (t 0)*z) ns.1.1 *
        jacobiTerm (liftUnit (t 3)) (liftUnit (t 2)*z) ns.1.2 *
        jacobiTerm (liftUnit (t 3)) (liftUnit (t 4)*z) ns.2)) = 0 := by
    rw [ct_factor_triple]
    have hsum : ns.1.1+ns.1.2+ns.2 ≠ 0 := by
      intro he
      apply hn
      refine ⟨(ns.1.2,ns.2), ?_⟩
      apply Prod.ext
      · apply Prod.ext
        · change -ns.1.2-ns.2 = ns.1.1
          omega
        · rfl
      · rfl
    rw [if_neg hsum]
  have h := (lattice_injective.hasSum_iff hoff).mpr (hasSum_projected b)
  apply h.congr_fun
  rintro ⟨r,s⟩
  dsimp only [Function.comp_def, lattice]
  rw [ct_factor_triple, if_pos (by omega)]

noncomputable def core : L :=
  ∑' rs : ℤ × ℤ, xPow () (6*(rs.1^2+rs.1*rs.2+rs.2^2)+2*rs.1+4*rs.2)

theorem summable_core :
    Summable (fun rs : ℤ × ℤ => (xPow () (6*(rs.1^2+rs.1*rs.2+rs.2^2)+2*rs.1+4*rs.2) : L)) := by
  simpa only [one_mul] using (hasSum_core_mul 1).summable

theorem ct_triple (b : L) : ct (lift b * triple) = b*core :=
  (hasSum_core_mul b).unique (summable_core.hasSum.mul_left b)

private theorem ct_jacobi (b : L) (p u : Lˣ) (hp : IsTopologicallyNilpotent (p : L)) :
    ct (lift b * jacobi (liftUnit p) (liftUnit u*z)) = b := by
  have hp' : IsTopologicallyNilpotent ((liftUnit p : LZˣ) : LZ) :=
    hp.map (mapVar_continuous inclusion)
  have h := ((hasSum_jacobiTerm (liftUnit p) (liftUnit u*z) hp').mul_left (lift b)).map ct
    (comapVar_continuous inclusion 0)
  have h' : HasSum (fun n : ℤ => if n = 0 then b else 0)
      (ct (lift b * jacobi (liftUnit p) (liftUnit u*z))) :=
    h.congr_fun (fun n => (ct_factor_term b p u n).symm)
  simpa using h'.tsum_eq.symm

private theorem lift_eta (d : ℤ) (hd : 0 < d) :
    lift (eta d) = (xPow false d; xPow false d)_∞ := by
  rw [eta, map_qPochhammerInf lift (mapVar_continuous inclusion) _
    ((isTopologicallyNilpotent_xPow_iff () d).mpr hd)]
  simp only [lift, mapVar_xPow]
  rfl

private theorem lift_t_pow (k : ℕ) : (liftUnit (t 1))^k = liftUnit (t (k : ℤ)) := by
  rw [← map_pow]
  congr 1
  simp only [t, ← zpow_natCast, xPowUnits_zpow, one_mul]

private theorem lift_t_val_pow (k : ℕ) :
    (((liftUnit (t 1) : LZˣ) : LZ))^k = xPow false (k : ℤ) := by
  have hv : ((liftUnit (t 1) : LZˣ) : LZ) = xPow false 1 := by
    change lift (xPow () 1) = _
    simp only [lift, mapVar_xPow]
    rfl
  rw [hv, xPow_pow, one_mul]

private theorem t_zero : t 0 = 1 := by
  apply Units.ext
  exact xPow_zero ()

private theorem product_identity :
    lift (eta 2) * triple = lift ((eta 6)^3) *
      jacobi (liftUnit (t 1)) (liftUnit (t 0)*z) := by
  have h := jacobi_trisection_product (liftUnit (t 1)) z (nilpotent_lift_t 1 (by decide))
  rw [lift_t_pow 3, lift_t_pow 2, lift_t_pow 4,
    lift_t_val_pow 2, lift_t_val_pow 6] at h
  norm_num only [Nat.cast_ofNat] at h
  rw [← lift_eta 2 (by decide), ← lift_eta 6 (by decide), ← map_pow] at h
  simpa only [triple, t_zero, map_one, one_mul, mul_assoc,
    mul_comm z (liftUnit (t 2)), mul_comm z (liftUnit (t 4))] using h

/-- The shifted A2 product, proved by the continuous constant-term operation. -/
theorem core_product : eta 2 * core = (eta 6)^3 := by
  have h := congrArg ct product_identity
  rw [ct_triple, ct_jacobi] at h
  · exact h
  · change IsTopologicallyNilpotent (xPow () 1 : L)
    exact (isTopologicallyNilpotent_xPow_iff () 1).mpr (by decide)

end KanadeRussell.Product.A2ConstantTerm
