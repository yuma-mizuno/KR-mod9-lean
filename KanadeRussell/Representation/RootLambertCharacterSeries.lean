import KanadeRussell.Representation.RootLambertScalarIdentity
import KanadeRussell.Representation.RootLambertResidueArithmetic

/-! The two projected root moments as exact character Lambert series.
The coefficient definition includes the dilation in the root height. -/
set_option autoImplicit false
noncomputable section
namespace KanadeRussell.Representation
variable {K : Type*} [Field K]

/-- For positive d, the coefficient-finite series with summands chi(m) q^(d*m)/(1-q^(d*m)). -/
def residueCharacterLambert (chi : ℕ → ℤ) (d : ℕ) : PowerSeries K :=
  scalarLambertTransform fun h _ => if d ∣ h+1 then (chi ((h+1)/d) : K) else 0

theorem coeff_residueCharacterLambert (chi : ℕ → ℤ) (d n : ℕ) :
    PowerSeries.coeff n (residueCharacterLambert (K := K) chi d) =
      ∑ h ∈ Finset.range n, ∑ k ∈ Finset.range (n+1),
        if (k+1)*(h+1)=n then (if d ∣ h+1 then (chi ((h+1)/d) : K) else 0) else 0 :=
  coeff_scalarLambertTransform _ n

theorem principalScalarT_character : principalScalarT (K := K) =
    residueCharacterLambert residueCharacter4 1 + 3 • residueCharacterLambert residueCharacter4 3 := by
  unfold principalScalarT residueCharacterLambert
  rw [← map_nsmul, ← map_add]
  congr 1
  ext h k
  have hh := congrArg (Int.castRingHom K) (principalRootMomentT_character h)
  simpa using hh

theorem principalScalarU_character : principalScalarU (K := K) =
    residueCharacterLambert residueCharacter3 1 + residueCharacterLambert residueCharacter3 2 -
      2 • residueCharacterLambert residueCharacter3 4 := by
  unfold principalScalarU residueCharacterLambert
  rw [← map_nsmul, ← map_add, ← map_sub]
  congr 1
  ext h k
  have hh := congrArg (Int.castRingHom K) (principalRootMomentU_character h)
  simpa using hh

end KanadeRussell.Representation
