import KanadeRussell.Tsuchioka.SourceCoefficients
import KanadeRussell.Tsuchioka.PairReductions

/-! F2 and F3 with the actual source series.
The finite operator relations remain explicit hypotheses; coefficient identities do not. -/

namespace KanadeRussell.Tsuchioka

variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]

/-- Repeated-pair reduction using the source G2 and G3 coefficients. -/
theorem repeated_reduction_source_coefficients
    (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) (value : Word → V)
    (a : ℤ) (N M : ℕ)
    (hrel :
      symmetricSum value (fun n => PowerSeries.coeff n (Scalar.G w 1)) a a (N + 1) -
        (Coefficients.tCoeff w / Coefficients.mCoeff w) •
          symmetricSum value (fun n => PowerSeries.coeff n (Scalar.G w 2)) a a (M + 1) ∈
            higherSpan (K := K) value [a, a]) :
    value [a, a] ∈ higherSpan (K := K) value [a, a] := by
  exact repeated_reduction_of_combined_relation w hw value _ _
    (Scalar.coeff_zero_G w 1) (Scalar.coeff_zero_G w 2) a N M hrel

/-- Adjacent-pair reduction with the source G2, G3, and corrected G6.
Only the two finite operator relations still need to be established. -/
theorem adjacent_reduction_source_coefficients
    (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) (value : Word → V)
    (a : ℤ) (N M L : ℕ)
    (h₂₃ :
      symmetricSum value (fun n => PowerSeries.coeff n (Scalar.G w 1)) a (a + 1) (N + 2) -
        (Coefficients.tCoeff w / Coefficients.mCoeff w) •
          symmetricSum value (fun n => PowerSeries.coeff n (Scalar.G w 2))
            a (a + 1) (M + 2) ∈ higherSpan (K := K) value [a, a + 1])
    (h₆ : skewSum value (fun n => PowerSeries.coeff n (Scalar.G6 w))
      a (a + 1) (L + 2) ∈ higherSpan (K := K) value [a, a + 1]) :
    value [a, a + 1] ∈ higherSpan (K := K) value [a, a + 1] := by
  exact adjacent_reduction_of_combined_relations w hw value _ _ _
    (Scalar.coeff_zero_G w 1) (Scalar.coeff_zero_G w 2)
    (Scalar.coeff_one_G2 w hw) (Scalar.coeff_one_G3 w hw)
    (Scalar.coeff_zero_G6 w) (Scalar.coeff_one_G6 w hw)
    a N M L h₂₃ h₆

end KanadeRussell.Tsuchioka
