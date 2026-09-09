import KanadeRussell.Straightening.EmbeddedPairs
import KanadeRussell.Sectors.SkewSeed
import KanadeRussell.Tsuchioka.AlternatingInitialReduction

/-! All six local reductions and admissible spanning in both non-vacuum sectors. -/
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Straightening
open Tsuchioka Tsuchioka.Fock Sectors
variable {K : Type*} [Field K] [CharZero K]

noncomputable def skewPolynomialAction (w : K) : PolynomialAction w :=
  PolynomialAction.ofEmbedding w (skewHighestWeightAction w) skewSpace.subtype (fun _ _ => rfl)

theorem skew_forbiddenPairs (w : K) (hw : w^4-w^2+1=0) :
    ∀ a b, ForbiddenPair a b → (skewHighestWeightAction w).LocalReduction [a,b] := by
  intro a b h
  exact localReduction_of_embedding w (skewHighestWeightAction w) skewSpace.subtype
    Subtype.val_injective (fun _ _ => rfl) [a,b]
    (PolynomialAction.forbiddenPairs w (skewPolynomialAction w) hw a b h)

theorem skew_forbiddenTriples (w : K) (hw : w^4-w^2+1=0) :
    ∀ a b c, ForbiddenTriple a b c → (skewHighestWeightAction w).LocalReduction [a,b,c] := by
  intro a b c h
  exact localReduction_of_embedding w (skewHighestWeightAction w) skewSpace.subtype
    Subtype.val_injective (fun _ _ => rfl) [a,b,c]
    (PolynomialAction.fock_forbiddenTriples w (skewPolynomialAction w) hw a b c h)

theorem skew_cyclicGrade_eq_span_normal (w : K) (hw : w^4-w^2+1=0) (n : ℕ) :
    Partitions.cyclicGrade (skewHighestWeightAction w) n = Submodule.span K
      (Set.range (fun u : Partitions.NormalWords 1 n => (skewHighestWeightAction w).wordValue u.val)) :=
  Partitions.cyclicGrade_eq_span_normal _ 1 n
    (skew_forbiddenPairs w hw) (skew_forbiddenTriples w hw) (skew_initial_reduction w)

theorem skew_cyclicGrade_finite (w : K) (hw : w^4-w^2+1=0) (n : ℕ) :
    Module.Finite K (Partitions.cyclicGrade (skewHighestWeightAction w) n) :=
  Partitions.cyclicGrade_finite _ 1 n (by omega)
    (skew_forbiddenPairs w hw) (skew_forbiddenTriples w hw) (skew_initial_reduction w)

theorem skew_finrank_le_count (w : K) (hw : w^4-w^2+1=0) (n : ℕ) :
    Module.finrank K (Partitions.cyclicGrade (skewHighestWeightAction w) n) ≤ Partitions.count 1 n :=
  Partitions.finrank_cyclicGrade_le_count _ 1 n (by omega)
    (skew_forbiddenPairs w hw) (skew_forbiddenTriples w hw) (skew_initial_reduction w)

noncomputable def alternatingPolynomialAction (w : K) : PolynomialAction w :=
  PolynomialAction.ofEmbedding w (alternatingHighestWeightAction w) alternatingSpace.subtype (fun _ _ => rfl)

theorem alternating_forbiddenPairs (w : K) (hw : w^4-w^2+1=0) :
    ∀ a b, ForbiddenPair a b → (alternatingHighestWeightAction w).LocalReduction [a,b] := by
  intro a b h
  exact localReduction_of_embedding w (alternatingHighestWeightAction w) alternatingSpace.subtype
    Subtype.val_injective (fun _ _ => rfl) [a,b]
    (PolynomialAction.forbiddenPairs w (alternatingPolynomialAction w) hw a b h)

theorem alternating_forbiddenTriples (w : K) (hw : w^4-w^2+1=0) :
    ∀ a b c, ForbiddenTriple a b c → (alternatingHighestWeightAction w).LocalReduction [a,b,c] := by
  intro a b c h
  exact localReduction_of_embedding w (alternatingHighestWeightAction w) alternatingSpace.subtype
    Subtype.val_injective (fun _ _ => rfl) [a,b,c]
    (PolynomialAction.fock_forbiddenTriples w (alternatingPolynomialAction w) hw a b c h)

theorem alternating_cyclicGrade_eq_span_normal (w : K) (hw : w^4-w^2+1=0) (n : ℕ) :
    Partitions.cyclicGrade (alternatingHighestWeightAction w) n = Submodule.span K
      (Set.range (fun u : Partitions.NormalWords 3 n => (alternatingHighestWeightAction w).wordValue u.val)) :=
  Partitions.cyclicGrade_eq_span_normal _ 3 n
    (alternating_forbiddenPairs w hw) (alternating_forbiddenTriples w hw) (alternating_initial_reduction w hw)

theorem alternating_cyclicGrade_finite (w : K) (hw : w^4-w^2+1=0) (n : ℕ) :
    Module.Finite K (Partitions.cyclicGrade (alternatingHighestWeightAction w) n) :=
  Partitions.cyclicGrade_finite _ 3 n (by omega)
    (alternating_forbiddenPairs w hw) (alternating_forbiddenTriples w hw) (alternating_initial_reduction w hw)

theorem alternating_finrank_le_count (w : K) (hw : w^4-w^2+1=0) (n : ℕ) :
    Module.finrank K (Partitions.cyclicGrade (alternatingHighestWeightAction w) n) ≤ Partitions.count 3 n :=
  Partitions.finrank_cyclicGrade_le_count _ 3 n (by omega)
    (alternating_forbiddenPairs w hw) (alternating_forbiddenTriples w hw) (alternating_initial_reduction w hw)

/-- Source F1, including the exceptional residue class. -/
theorem skew_f1 (w : K) (hw : w^4-w^2+1=0) (a b : ℤ) (hab : b < a) :
    (skewHighestWeightAction w).LocalReduction [a,b] :=
  skew_forbiddenPairs w hw a b (Or.inl hab)

/-- Source F2. -/
theorem skew_f2 (w : K) (hw : w^4-w^2+1=0) (a : ℤ) (ha : a%3 ≠ 0) :
    (skewHighestWeightAction w).LocalReduction [a,a] :=
  skew_forbiddenPairs w hw a a (Or.inr (Or.inl ⟨rfl, by omega⟩))

/-- Source F3. -/
theorem skew_f3 (w : K) (hw : w^4-w^2+1=0) (a : ℤ) (ha : (2*a+1)%3 ≠ 0) :
    (skewHighestWeightAction w).LocalReduction [a,a+1] :=
  skew_forbiddenPairs w hw a (a+1) (Or.inr (Or.inr ⟨rfl, ha⟩))

/-- Source F4. -/
theorem skew_f4 (w : K) (hw : w^4-w^2+1=0) (a : ℤ) (ha : a%3 = 0) :
    (skewHighestWeightAction w).LocalReduction [a,a,a] :=
  skew_forbiddenTriples w hw a a a (Or.inl ⟨rfl, rfl, ha⟩)

/-- Source F5. -/
theorem skew_f5 (w : K) (hw : w^4-w^2+1=0) (a : ℤ) (ha : a%3 = 0) :
    (skewHighestWeightAction w).LocalReduction [a,a,a+2] :=
  skew_forbiddenTriples w hw a a (a+2) (Or.inr (Or.inl ⟨rfl, rfl, ha⟩))

/-- Source F6. -/
theorem skew_f6 (w : K) (hw : w^4-w^2+1=0) (a : ℤ) (ha : a%3 = 0) :
    (skewHighestWeightAction w).LocalReduction [a-2,a,a] :=
  skew_forbiddenTriples w hw (a-2) a a (Or.inr (Or.inr ⟨rfl, by omega, ha⟩))

/-- Source F1, including the exceptional residue class. -/
theorem alternating_f1 (w : K) (hw : w^4-w^2+1=0) (a b : ℤ) (hab : b < a) :
    (alternatingHighestWeightAction w).LocalReduction [a,b] :=
  alternating_forbiddenPairs w hw a b (Or.inl hab)

/-- Source F2. -/
theorem alternating_f2 (w : K) (hw : w^4-w^2+1=0) (a : ℤ) (ha : a%3 ≠ 0) :
    (alternatingHighestWeightAction w).LocalReduction [a,a] :=
  alternating_forbiddenPairs w hw a a (Or.inr (Or.inl ⟨rfl, by omega⟩))

/-- Source F3. -/
theorem alternating_f3 (w : K) (hw : w^4-w^2+1=0) (a : ℤ) (ha : (2*a+1)%3 ≠ 0) :
    (alternatingHighestWeightAction w).LocalReduction [a,a+1] :=
  alternating_forbiddenPairs w hw a (a+1) (Or.inr (Or.inr ⟨rfl, ha⟩))

/-- Source F4. -/
theorem alternating_f4 (w : K) (hw : w^4-w^2+1=0) (a : ℤ) (ha : a%3 = 0) :
    (alternatingHighestWeightAction w).LocalReduction [a,a,a] :=
  alternating_forbiddenTriples w hw a a a (Or.inl ⟨rfl, rfl, ha⟩)

/-- Source F5. -/
theorem alternating_f5 (w : K) (hw : w^4-w^2+1=0) (a : ℤ) (ha : a%3 = 0) :
    (alternatingHighestWeightAction w).LocalReduction [a,a,a+2] :=
  alternating_forbiddenTriples w hw a a (a+2) (Or.inr (Or.inl ⟨rfl, rfl, ha⟩))

/-- Source F6. -/
theorem alternating_f6 (w : K) (hw : w^4-w^2+1=0) (a : ℤ) (ha : a%3 = 0) :
    (alternatingHighestWeightAction w).LocalReduction [a-2,a,a] :=
  alternating_forbiddenTriples w hw (a-2) a a (Or.inr (Or.inr ⟨rfl, by omega, ha⟩))

end KanadeRussell.Straightening
