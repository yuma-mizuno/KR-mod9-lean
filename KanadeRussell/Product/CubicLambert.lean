import KanadeRussell.Product.CubicFrame
import KanadeRussell.Infra.CyclotomicLambert
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-! Convergent Lambert normalization for the cubic square identity. -/
open PowerSeries PowerSeries.WithPiTopology
open scoped DiscreteUniformity
namespace KanadeRussell.Product.CubicLambert
open Infra.JacobiJets Infra.JacobiParameter
variable {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
  [CompleteSpace R] [StrongNonarchimedeanRing R] [T2Space R]

theorem intEval_lambert_tail (x : R) (hx : IsTopologicallyNilpotent x)
    (d : ℕ) (hd : 0 < d) : intEval x (lambert d) = lambertTail (x^d) (x^d) := by
  have hs := (summable_lambert d hd).hasSum
  have hz : lambertTerm (d*0) = 0 := by simp [lambertTerm]
  have he : lambert d = ∑' k : ℕ, lambertTerm (d*(k+1)) := by
    rw [lambert, hs.summable.tsum_eq_zero_add, hz, zero_add]
  rw [he]
  have hm := ((summable_nat_add_iff 1).mpr hs.summable).hasSum.map (intEval x) (by fun_prop)
  apply hm.unique
  apply (summable_lambertTail _ _ (hx.pow hd.ne') (hx.pow hd.ne')).hasSum.congr_fun
  intro k
  dsimp only [Function.comp_def]
  have hk : 0 < d*(k+1) := Nat.mul_pos hd (by omega)
  have hu : IsUnit (1-q^(d*(k+1))) :=
    (show IsTopologicallyNilpotent (q^(d*(k+1))) by simp [q, hk.ne']).isUnit_one_sub
  simp only [lambertTerm, if_neg hk.ne', map_mul, map_pow, hu.map_bInv (intEval x),
    map_sub, map_one, show intEval x q = x from intEval_X hx]
  have hpow : x^(d*(k+1)) = x^d*(x^d)^k := by rw [pow_mul, pow_succ]; ring
  rw [hpow]

theorem tail_trisection (x : R) (hx : IsTopologicallyNilpotent x) :
    lambertTail x x = lambertTail x (x^3)+lambertTail (x^2) (x^3)+lambertTail (x^3) (x^3) := by
  let f : ℕ → R := fun n => x*x^n*bInv (1-x*x^n)^2
  let E : Fin 3 × ℕ ≃ ℕ := (Equiv.prodComm (Fin 3) ℕ).trans (Nat.divModEquiv 3).symm
  have hs := (summable_lambertTail x x hx hx).hasSum
  have hr : HasSum (fun k : Fin 3 × ℕ => f (E k)) (lambertTail x x) := E.hasSum_iff.mpr hs
  have hf : ∀ r : Fin 3, HasSum (fun k : ℕ => f (E (r,k))) (lambertTail (x^(r.val+1)) (x^3)) := by
    intro r
    apply (summable_lambertTail _ _ (hx.pow (by omega)) (hx.pow (by decide : 3 ≠ 0))).hasSum.congr_fun
    intro k
    have he : x*x^(k*3+r.val) = x^(r.val+1)*(x^3)^k := by
      simp only [← pow_mul, ← pow_succ', ← pow_add]
      congr 1
      omega
    change x*x^(k*3+r.val)*bInv (1-x*x^(k*3+r.val))^2 = _
    rw [he]
  have hh := (hr.prod_fiberwise hf).tsum_eq
  rw [tsum_fintype] at hh
  norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, Nat.reduceAdd,
    pow_one, Finset.sum_empty, add_zero] at hh
  linear_combination -hh

theorem root_tail_pair (w x : R) (hw : w^2+w+1 = 0) (hx : IsTopologicallyNilpotent x) :
    lambertTail (w*x) x+lambertTail (w^2*x) x =
      -lambertTail x x+9*lambertTail (x^3) (x^3) := by
  have hw3 : w^3 = 1 := by linear_combination (w-1)*hw
  have hw23 : (w^2)^3 = 1 := by rw [← pow_mul, Nat.mul_comm, pow_mul, hw3, one_pow]
  have hwx := root_mul_nilpotent w x (by decide : 3 ≠ 0) hw3 hx
  have hw2x := root_mul_nilpotent (w^2) x (by decide : 3 ≠ 0) hw23 hx
  have hs := (summable_lambertTail _ _ hwx hx).hasSum.add (summable_lambertTail _ _ hw2x hx).hasSum
  have ht := (summable_lambertTail x x hx hx).hasSum.neg.add
    ((summable_lambertTail (x^3) (x^3) (hx.pow (by decide)) (hx.pow (by decide))).hasSum.mul_left 9)
  apply hs.unique
  apply ht.congr_fun
  intro n
  have hn := hx.mul_pow hx (n:=n)
  have hwn := root_mul_nilpotent w (x*x^n) (by decide : 3 ≠ 0) hw3 hn
  have hw2n := root_mul_nilpotent (w^2) (x*x^n) (by decide : 3 ≠ 0) hw23 hn
  have hh := Infra.CyclotomicLambert.pair w (x*x^n) hw hn.isUnit_one_sub
    (hn.pow (by decide : 3 ≠ 0)).isUnit_one_sub hwn.isUnit_one_sub hw2n.isUnit_one_sub
  have he : (x*x^n)^3 = x^3*(x^3)^n := by rw [mul_pow, ← pow_mul, Nat.mul_comm, pow_mul]
  simp only [he, ← mul_assoc] at hh
  simpa only [neg_mul, mul_assoc] using hh

omit [UniformSpace R] [IsUniformAddGroup R] [CompleteSpace R]
  [StrongNonarchimedeanRing R] [T2Space R] in
theorem root_initial (w : R) (hw : w^2+w+1 = 0) (hu : IsUnit (1-w)) :
    3*w*bInv (1-w)^2 = -1 := by
  have hd : (1-w)^2 = -3*w := by linear_combination hw
  have hi : (1-w)^2*bInv (1-w)^2 = 1 := by rw [← mul_pow, hu.mul_bInv_cancel, one_pow]
  rw [hd] at hi
  linear_combination -hi

theorem elliptic_level_three (p : Rˣ) (hp : IsTopologicallyNilpotent (p:R)) :
    ellipticLambert (p^3) (p^2) = intEval ((p:R)^2) (lambert 1-lambert 3) := by
  have hp2 := hp.pow (by decide : 2 ≠ 0)
  rw [ellipticLambert, CubicFrame.level_complement]
  simp only [Units.val_pow_eq_pow_val, ← pow_mul, Nat.reduceMul]
  rw [map_sub, intEval_lambert_tail _ hp2 1 (by decide), intEval_lambert_tail _ hp2 3 (by decide)]
  simp only [pow_one, ← pow_mul, Nat.reduceMul]
  have hh := tail_trisection ((p:R)^2) hp2
  simp only [← pow_mul, Nat.reduceMul] at hh
  linear_combination -hh

theorem elliptic_root (p v : Rˣ) (hp : IsTopologicallyNilpotent (p:R))
    (hw : (v:R)^2+(v:R)+1 = 0) (hu : IsUnit (1-(v:R))) :
    3*ellipticLambert p v = -1-3*intEval ((p:R)^2) (lambert 1)+27*intEval ((p:R)^2) (lambert 3) := by
  have hw3 : (v:R)^3 = 1 := by linear_combination ((v:R)-1)*hw
  have hv3 : v^3 = 1 := Units.ext (by simpa only [Units.val_pow_eq_pow_val, Units.val_one] using hw3)
  have hi : v⁻¹ = v^2 := by
    apply mul_left_cancel (a:=v)
    rw [mul_inv_cancel, ← pow_succ', hv3]
  have hp2 := hp.pow (by decide : 2 ≠ 0)
  have hroot := root_mul_nilpotent (v:R) ((p:R)^2) (by decide : 3 ≠ 0) hw3 hp2
  have hs := lambertTail_split (v:R) ((p:R)^2) hp2 hroot
  have ht := root_tail_pair (v:R) ((p:R)^2) hw hp2
  have h0 := root_initial (v:R) hw hu
  rw [ellipticLambert, div_eq_mul_inv, hi]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val]
  rw [mul_comm ((p:R)^2) ((v:R)^2), hs,
    intEval_lambert_tail _ hp2 1 (by decide), intEval_lambert_tail _ hp2 3 (by decide)]
  simp only [pow_one]
  linear_combination 3*ht+h0

end KanadeRussell.Product.CubicLambert
