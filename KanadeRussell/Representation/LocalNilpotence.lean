import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic

/-! Local nilpotence propagates across an operator with nilpotent adjoint orbit. -/
namespace KanadeRussell.Representation
attribute [local instance 100] LieRing.ofAssociativeRing
variable {K V : Type*} [CommRing K] [AddCommGroup V] [Module K V]

/-- A finite commutator bound and a finite vector bound imply a vector bound
for the image. No finite-dimensionality or spanning hypothesis is used. -/
theorem pow_apply_eq_zero_of_ad_pow_eq_zero
    (f g : Module.End K V) (v : V) (r s : ℕ)
    (hg : ((LieAlgebra.ad K (Module.End K V) f)^r) g = 0)
    (hv : (f^s) v = 0) : (f^(r+s)) (g v) = 0 := by
  induction r generalizing g s v with
  | zero =>
    have hg' : g = 0 := by simpa using hg
    simp [hg']
  | succ r ih =>
    induction s generalizing v with
    | zero =>
      have hv' : v = 0 := by simpa using hv
      simp [hv']
    | succ s ihs =>
      have hg' : ((LieAlgebra.ad K (Module.End K V) f)^r)
          ((LieAlgebra.ad K (Module.End K V) f) g) = 0 := by
        simpa only [pow_succ, Module.End.mul_apply] using hg
      have h₁ := ih ((LieAlgebra.ad K (Module.End K V) f) g) v (s+1) hg' hv
      have hv' : (f^s) (f v) = 0 := by
        simpa only [pow_succ, Module.End.mul_apply] using hv
      have h₂ := ihs (f v) hv'
      have he : f (g v) = ((LieAlgebra.ad K (Module.End K V) f) g) v + g (f v) := by
        simp [LieAlgebra.ad_apply, Ring.lie_def, Module.End.mul_apply]
      rw [show r+1+(s+1) = (r+(s+1))+1 by omega, pow_succ, Module.End.mul_apply, he, map_add, h₁]
      have hn : r + (s+1) = r+1+s := by omega
      rw [hn, h₂, add_zero]

/-- The existential form used to propagate local nilpotence along generator words. -/
theorem locally_nilpotent_apply_of_ad
    (f g : Module.End K V) (v : V)
    (hg : ∃ r : ℕ, ((LieAlgebra.ad K (Module.End K V) f)^r) g = 0)
    (hv : ∃ s : ℕ, (f^s) v = 0) : ∃ n : ℕ, (f^n) (g v) = 0 := by
  obtain ⟨r, hr⟩ := hg
  obtain ⟨s, hs⟩ := hv
  exact ⟨r+s, pow_apply_eq_zero_of_ad_pow_eq_zero f g v r s hr hs⟩

end KanadeRussell.Representation
