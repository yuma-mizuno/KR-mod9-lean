import KanadeRussell.Tsuchioka.TensorSecondRootCommutator
import KanadeRussell.Tsuchioka.TensorMixedRootCommutator
import KanadeRussell.Tsuchioka.TensorFirstRootCommutator
import KanadeRussell.Tsuchioka.TensorGrading

/-! Endomorphism Lie brackets for the complete concrete tensor mode
families, including the all-integer Heisenberg convention. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

attribute [local instance] LieRing.ofAssociativeRing

open RootData (Lattice simpleRoot rootWeight)

variable {K : Type*} [Field K] [CharZero K]

theorem tensorFirstRoot_lie (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) (a b : ℤ) :
    ⁅tensorRootMode w (simpleRoot 0) a, tensorRootMode w (simpleRoot 0) b⁆ =
      (Coefficients.pCoeff w * (w ^ (-2 * a + 2 * b) - w ^ (2 * a - 2 * b)) / 12) •
        tensorRootMode w (simpleRoot 0) (a + b) +
      (Scalar.rootSecondResidue w * (w ^ (4 * a + 9 * b) - w ^ (9 * a + 4 * b)) / 12) •
        tensorRootMode w (simpleRoot 1) (a + b) -
      (Scalar.cPrime w * (-1 : K) ^ a / 6) • heisenbergMode w (a + b) +
      (if a + b = 0 then (Scalar.cPrime w * (a : K) * (-1 : K) ^ a / 24) •
        (1 : Module.End K (Space K)) else 0) := by
  apply LinearMap.ext
  intro f
  by_cases hab : a + b = 0 <;>
    simpa only [hab, if_true, if_false, Ring.lie_def, Module.End.mul_apply, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
    LinearMap.zero_apply, ite_apply] using tensorFirstRoot_commutator w hw f a b

theorem tensorMixedRoot_lie (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) (a b : ℤ) :
    ⁅tensorRootMode w (simpleRoot 0) a, tensorRootMode w (simpleRoot 1) b⁆ =
      (Coefficients.pCoeff (-w) * (w ^ (a + 3 * b) - w ^ (-a + 8 * b)) / 12) •
        tensorRootMode w (simpleRoot 0) (a + b) +
      (Coefficients.pCoeff w * (w ^ (-6 * a + 5 * b) - w ^ (7 * a + 7 * b)) / 12) •
        tensorRootMode w (simpleRoot 1) (a + b) := by
  apply LinearMap.ext
  intro f
  simpa only [Ring.lie_def, Module.End.mul_apply, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.smul_apply] using tensorMixedRoot_commutator w hw f a b

theorem tensorSecondRoot_lie (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) (a b : ℤ) :
    ⁅tensorRootMode w (simpleRoot 1) a, tensorRootMode w (simpleRoot 1) b⁆ =
      (Coefficients.pCoeff (-w) * (w ^ (-2 * a + 2 * b) - w ^ (2 * a - 2 * b)) / 12) •
        tensorRootMode w (simpleRoot 1) (a + b) +
      (Scalar.rootSecondResidue (-w) * (w ^ (-6 * a + 5 * b) - w ^ (5 * a + 6 * b)) / 12) •
        tensorRootMode w (simpleRoot 0) (a + b) -
      (Scalar.cPrime (-w) * (-1 : K) ^ a * rootWeight (w ^ (a + b)) (simpleRoot 1) / 6) •
        heisenbergMode w (a + b) +
      (if a + b = 0 then (Scalar.cPrime (-w) * (a : K) * (-1 : K) ^ a / 24) •
        (1 : Module.End K (Space K)) else 0) := by
  apply LinearMap.ext
  intro f
  by_cases hab : a + b = 0 <;>
    simpa only [hab, if_true, if_false, Ring.lie_def, Module.End.mul_apply, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
    LinearMap.zero_apply, ite_apply] using tensorSecondRoot_commutator w hw f a b

theorem heisenbergMode_tensorRootMode_lie (w : K) (beta : Lattice) (i j : ℤ) :
    ⁅heisenbergMode w i, tensorRootMode w beta j⁆ =
      (if IsMode i.natAbs then
        contraction w i.natAbs * rootWeight (w ^ (-i)) beta else 0) •
          tensorRootMode w beta (j + i) := by
  by_cases hm : IsMode i.natAbs
  · let n : Mode := ⟨i.natAbs, hm⟩
    by_cases hi : 0 < i
    · have hn : (n.val : ℤ) = i := by
        change (i.natAbs : ℤ) = i
        rw [Int.natCast_natAbs, abs_of_pos hi]
      have h := heisenbergPositive_tensorRootMode_commutator w beta n j
      rw [hn] at h
      simpa only [heisenbergMode, dif_pos hm, if_pos hm, if_pos hi, Ring.lie_def,
        Module.End.mul_eq_comp, n] using h
    · have hn : (n.val : ℤ) = -i := by
        change (i.natAbs : ℤ) = -i
        rw [Int.natCast_natAbs, abs_of_nonpos (le_of_not_gt hi)]
      have h := heisenbergNegative_tensorRootMode_commutator w beta n j
      rw [hn, sub_neg_eq_add] at h
      simpa only [heisenbergMode, dif_pos hm, if_pos hm, if_neg hi, Ring.lie_def,
        Module.End.mul_eq_comp, n] using h
  · simp [heisenbergMode, hm, Ring.lie_def]

theorem principalDerivation_heisenbergMode_lie (w : K) (i : ℤ) :
    ⁅principalDerivation (K := K), heisenbergMode w i⁆ = (i : K) • heisenbergMode w i := by
  by_cases hm : IsMode i.natAbs
  · let n : Mode := ⟨i.natAbs, hm⟩
    by_cases hi : 0 < i
    · have hn : (n.val : ℤ) = i := by
        change (i.natAbs : ℤ) = i
        rw [Int.natCast_natAbs, abs_of_pos hi]
      have h := principalDerivation_heisenbergPositive_commutator w n
      have hk : (n.val : K) = (i : K) := by exact_mod_cast hn
      rw [hk] at h
      simpa only [heisenbergMode, dif_pos hm, if_pos hm, if_pos hi, Ring.lie_def,
        Module.End.mul_eq_comp, n] using h
    · have hn : (n.val : ℤ) = -i := by
        change (i.natAbs : ℤ) = -i
        rw [Int.natCast_natAbs, abs_of_nonpos (le_of_not_gt hi)]
      have h := principalDerivation_heisenbergNegative_commutator (K := K) n
      have hk : -(n.val : K) = (i : K) := by
        have hz : -(n.val : ℤ) = i := by simpa only [neg_neg] using congrArg Neg.neg hn
        exact_mod_cast hz
      rw [hk] at h
      simpa only [heisenbergMode, dif_pos hm, if_pos hm, if_neg hi, Ring.lie_def,
        Module.End.mul_eq_comp, n] using h
  · simp [heisenbergMode, hm, Ring.lie_def]

theorem principalDerivation_tensorRootMode_lie (w : K) (beta : Lattice) (i : ℤ) :
    ⁅principalDerivation (K := K), tensorRootMode w beta i⁆ =
      (i : K) • tensorRootMode w beta i :=
  principalDerivation_tensorRootMode_commutator w beta i

theorem heisenbergPositive_lie (w : K) (n m : Mode) :
    ⁅heisenbergPositive w n, heisenbergPositive w m⁆ = 0 := by
  apply LinearMap.ext
  intro f
  change heisenbergPositive w n (heisenbergPositive w m f) -
    heisenbergPositive w m (heisenbergPositive w n f) = 0
  rw [heisenbergPositive_commute w n m, sub_self]

theorem heisenbergNegative_lie (n m : Mode) :
    ⁅heisenbergNegative (K := K) n, heisenbergNegative (K := K) m⁆ = 0 := by
  apply LinearMap.ext
  intro f
  change heisenbergNegative n (heisenbergNegative m f) -
    heisenbergNegative m (heisenbergNegative n f) = 0
  rw [heisenbergNegative_commute (K := K) n m, sub_self]

theorem heisenbergPositive_negative_lie (w : K) (n m : Mode) :
    ⁅heisenbergPositive w n, heisenbergNegative m⁆ =
      if m = n then (n.val * contraction w n.val / 4 : K) •
        (1 : Module.End K (Space K)) else 0 := by
  apply LinearMap.ext
  intro f
  by_cases hmn : m = n
  · have h := heisenberg_mixed_commutator w n m f
    simp only [if_pos hmn, smul_smul] at h
    simp only [if_pos hmn, Ring.lie_def, Module.End.mul_apply,
      LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    rw [h]
    congr 1
    ring
  · simpa only [if_neg hmn, Ring.lie_def, Module.End.mul_apply,
      LinearMap.sub_apply, LinearMap.zero_apply] using heisenberg_mixed_commutator w n m f

set_option maxHeartbeats 800000 in
/-- The central Heisenberg bracket, with the absent principal degrees made explicit. -/
theorem heisenbergMode_lie (w : K) (i j : ℤ) :
    ⁅heisenbergMode w i, heisenbergMode w j⁆ =
      (if IsMode i.natAbs ∧ i + j = 0 then
        (i : K) * contraction w i.natAbs / 4 else 0) •
          (1 : Module.End K (Space K)) := by
  by_cases hi : IsMode i.natAbs
  · by_cases hj : IsMode j.natAbs
    · let n : Mode := ⟨i.natAbs, hi⟩
      let m : Mode := ⟨j.natAbs, hj⟩
      have hin : i.natAbs ≠ 0 := Nat.ne_of_gt (mode_pos n)
      have hjn : j.natAbs ≠ 0 := Nat.ne_of_gt (mode_pos m)
      have ine : i ≠ 0 := by omega
      have jne : j ≠ 0 := by omega
      by_cases hip : 0 < i <;> by_cases hjp : 0 < j
      · have hz : i + j ≠ 0 := by omega
        simp only [heisenbergMode, dif_pos hi, dif_pos hj, if_pos hip, if_pos hjp,
          heisenbergPositive_lie, hz, and_false, if_false, zero_smul]
      · have hn : (n.val : ℤ) = i := by
          change (i.natAbs : ℤ) = i
          rw [Int.natCast_natAbs, abs_of_pos hip]
        have hm : (m.val : ℤ) = -j := by
          change (j.natAbs : ℤ) = -j
          rw [Int.natCast_natAbs, abs_of_nonpos (le_of_not_gt hjp)]
        have heq : m = n ↔ i + j = 0 := by
          constructor
          · intro h; have := congrArg (fun q : Mode => (q.val : ℤ)) h; omega
          · intro h
            apply Subtype.ext
            have hz : (m.val : ℤ) = n.val := by omega
            exact_mod_cast hz
        have hk : (n.val : K) = (i : K) := by exact_mod_cast hn
        have hi' : heisenbergMode w i = heisenbergPositive w n := by
          rw [← hn, heisenbergMode_positive]
        have hj' : heisenbergMode w j = heisenbergNegative m := by
          rw [show j = -(m.val : ℤ) by omega, heisenbergMode_negative]
        rw [hi', hj', heisenbergPositive_negative_lie]
        simp only [heq, hi, true_and]
        split_ifs <;> simp [hk, n]
      · have hn : (n.val : ℤ) = -i := by
          change (i.natAbs : ℤ) = -i
          rw [Int.natCast_natAbs, abs_of_nonpos (le_of_not_gt hip)]
        have hm : (m.val : ℤ) = j := by
          change (j.natAbs : ℤ) = j
          rw [Int.natCast_natAbs, abs_of_pos hjp]
        have heq : n = m ↔ i + j = 0 := by
          constructor
          · intro h; have := congrArg (fun q : Mode => (q.val : ℤ)) h; omega
          · intro h
            apply Subtype.ext
            have hz : (n.val : ℤ) = m.val := by omega
            exact_mod_cast hz
        have hi' : heisenbergMode w i = heisenbergNegative n := by
          rw [show i = -(n.val : ℤ) by omega, heisenbergMode_negative]
        have hj' : heisenbergMode w j = heisenbergPositive w m := by
          rw [← hm, heisenbergMode_positive]
        rw [hi', hj', ← lie_skew (heisenbergNegative (K := K) n),
          heisenbergPositive_negative_lie]
        simp only [heq, hi, true_and]
        by_cases hz : i + j = 0
        · have he := heq.mpr hz
          have hmk : (m.val : K) = -(i : K) := by
            have hz' : (m.val : ℤ) = -i := by omega
            exact_mod_cast hz'
          simp only [if_pos hz, hmk]
          rw [← he]
          change -((- (i : K) * contraction w i.natAbs / 4) • _) = _
          module
        · simp [hz]
      · have hz : i + j ≠ 0 := by omega
        simp only [heisenbergMode, dif_pos hi, dif_pos hj, if_neg hip, if_neg hjp,
          heisenbergNegative_lie, hz, and_false, if_false, zero_smul]
    · have hz : i + j ≠ 0 := by
        intro hz
        have he : i = -j := by omega
        apply hj
        simpa only [he, Int.natAbs_neg] using hi
      simp [heisenbergMode_not_mode w j hj, hz, Ring.lie_def]
  · simp [heisenbergMode_not_mode w i hi, hi, Ring.lie_def]

end KanadeRussell.Tsuchioka.Fock
