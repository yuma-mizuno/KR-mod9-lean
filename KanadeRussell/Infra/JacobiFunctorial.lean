import KanadeRussell.Infra.JacobiTrisection
import KanadeRussell.Infra.JacobiKernelParameter
set_option backward.isDefEq.respectTransparency false

/-! Functoriality of convergent Jacobi series and their constant coefficients. -/
open PowerSeries PowerSeries.WithPiTopology
open scoped DiscreteUniformity
namespace KanadeRussell.Infra.ThetaAddition
variable {R S : Type*} [CommRing R] [CommRing S]

theorem map_jacobiTerm (f : R →+* S) (p u : Rˣ) (n : ℤ) :
    f (jacobiTerm p u n) =
      jacobiTerm (Units.map f.toMonoidHom p) (Units.map f.toMonoidHom u) n := by
  have hn : Units.map f.toMonoidHom (-1:Rˣ) = (-1:Sˣ) := by
    apply Units.ext
    simp
  change ((Units.map f.toMonoidHom (((-1:Rˣ)^n*u^n)*p^(n*(n-1))) : Sˣ):S) = _
  simp only [map_mul, map_zpow, hn, jacobiTerm]

variable [UniformSpace R] [IsUniformAddGroup R] [CompleteSpace R]
  [StrongNonarchimedeanRing R] [T2Space R]
  [UniformSpace S] [IsUniformAddGroup S] [CompleteSpace S]
  [StrongNonarchimedeanRing S] [T2Space S]

omit [T2Space R] in
theorem map_jacobi (f : R →+* S) (hf : Continuous f) (p u : Rˣ)
    (hp : IsTopologicallyNilpotent (p:R)) :
    f (jacobi p u) = jacobi (Units.map f.toMonoidHom p) (Units.map f.toMonoidHom u) := by
  have hh := (hasSum_jacobiTerm p u hp).map f hf
  apply hh.unique
  apply (hasSum_jacobiTerm (Units.map f.toMonoidHom p) (Units.map f.toMonoidHom u)
    (hp.map hf)).congr_fun
  intro n
  exact map_jacobiTerm f p u n

end KanadeRussell.Infra.ThetaAddition

namespace KanadeRussell.Infra.JacobiParameter
open JacobiJets
variable {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
  [CompleteSpace R] [StrongNonarchimedeanRing R] [T2Space R]

theorem jacobi_argument_constant (p u : Rˣ) (Z : (PowerSeries R)ˣ)
    (hp : IsTopologicallyNilpotent (p:R)) (hZ : constantCoeff (Z:PowerSeries R) = 1) :
    constantCoeff (ThetaAddition.jacobi (unitC p) (unitC u*Z)) = ThetaAddition.jacobi p u := by
  have hp' : IsTopologicallyNilpotent ((unitC p:(PowerSeries R)ˣ):PowerSeries R) := hp.map continuous_C
  have hh := ThetaAddition.map_jacobi constantCoeff (continuous_constantCoeff R)
    (unitC p) (unitC u*Z) hp'
  have h1 : Units.map constantCoeff.toMonoidHom (unitC p) = p := by
    apply Units.ext
    simp [unitC]
  have h2 : Units.map constantCoeff.toMonoidHom (unitC u*Z) = u := by
    apply Units.ext
    simp [unitC, hZ]
  rw [h1,h2] at hh
  exact hh

theorem intEval_C (x : R) (hx : IsTopologicallyNilpotent x) (f : PowerSeries ℤ) :
    intEval (PowerSeries.C x) f = PowerSeries.C (intEval x f) := by
  have hh := eq_intEval (PowerSeries.C.comp (intEval x)) (continuous_C.comp (by fun_prop))
  simp only [RingHom.comp_apply, intEval_X hx] at hh
  exact congrArg (fun g : PowerSeries ℤ →+* PowerSeries R => g f) hh.symm

end KanadeRussell.Infra.JacobiParameter
