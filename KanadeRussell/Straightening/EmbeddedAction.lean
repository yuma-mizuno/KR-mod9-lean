import KanadeRussell.Straightening.FockPairs

/-! Fock actions with an arbitrary graded seed, and faithful transport. -/
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Straightening
open Tsuchioka
variable {K : Type*} [Field K] [CharZero K]

structure PolynomialAction (w : K) where
  grade : ℤ → Submodule K (Fock.Space K)
  negative : ∀ n, n < 0 → grade n = ⊥
  mode_mem : ∀ i n v, v ∈ grade n → Fock.mode w i v ∈ grade (n-i)
  vacuum : Fock.Space K
  vacuum_mem : vacuum ∈ grade 0

noncomputable def PolynomialAction.action {w : K} (B : PolynomialAction w) :
    HighestWeightAction K (Fock.Space K) where
  grade := B.grade
  negative := B.negative
  mode := Fock.mode w
  mode_mem := B.mode_mem
  vacuum := B.vacuum
  vacuum_mem := B.vacuum_mem

variable {V : Type*} [AddCommGroup V] [Module K V]

noncomputable def PolynomialAction.ofEmbedding (w : K) (A : HighestWeightAction K V)
    (e : V →ₗ[K] Fock.Space K)
    (he : ∀ i v, e (A.mode i v) = Fock.mode w i (e v)) : PolynomialAction w where
  grade n := (A.grade n).map e
  negative n hn := by rw [A.negative n hn, Submodule.map_bot]
  mode_mem i n v hv := by
    obtain ⟨x,hx,rfl⟩ := hv
    exact ⟨A.mode i x, A.mode_mem i n x hx, he i x⟩
  vacuum := e A.vacuum
  vacuum_mem := ⟨A.vacuum, A.vacuum_mem, rfl⟩

theorem PolynomialAction.wordValue_ofEmbedding (w : K) (A : HighestWeightAction K V)
    (e : V →ₗ[K] Fock.Space K) (he : ∀ i v, e (A.mode i v) = Fock.mode w i (e v))
    (u : Word) : (PolynomialAction.ofEmbedding w A e he).action.wordValue u = e (A.wordValue u) := by
  induction u with
  | nil => rfl
  | cons i u ih =>
    change Fock.mode w i ((PolynomialAction.ofEmbedding w A e he).action.wordValue u) = e (A.mode i (A.wordValue u))
    rw [ih, he]

theorem localReduction_of_embedding (w : K) (A : HighestWeightAction K V)
    (e : V →ₗ[K] Fock.Space K) (hinj : Function.Injective e)
    (he : ∀ i v, e (A.mode i v) = Fock.mode w i (e v)) (u : Word)
    (h : (PolynomialAction.ofEmbedding w A e he).action.LocalReduction u) : A.LocalReduction u := by
  intro t
  have ht := h t
  simp only [PolynomialAction.wordValue_ofEmbedding] at ht
  have hm : higherSpan (K := K) (fun v => e (A.wordValue (v ++ t))) u =
      (higherSpan (K := K) (fun v => A.wordValue (v ++ t)) u).map e := by
    rw [higherSpan, higherSpan, Submodule.map_span, Set.image_image]
  rw [hm] at ht
  obtain ⟨x,hx,hxe⟩ := ht
  exact (hinj hxe) ▸ hx

end KanadeRussell.Straightening
