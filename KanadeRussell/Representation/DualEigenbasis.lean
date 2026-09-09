import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! A coordinate eigenbasis transports to the dual negative modes through an
invariant pairing matrix. The pairing itself is allowed to be singular. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Representation
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

/-- The rows of the inverse coordinate matrix are left eigenvectors. -/
theorem inverse_coordinates_left_eigen (H P Q L : Matrix I I K)
    (hPQ : P * Q = 1) (hHP : H * P = P * L) : Q * H = L * Q := by
  have hQP : Q * P = 1 := mul_eq_one_comm.mp hPQ
  calc
    Q * H = (Q * H) * (P * Q) := by rw [hPQ, mul_one]
    _ = Q * (H * P) * Q := by simp only [mul_assoc]
    _ = Q * (P * L) * Q := by rw [hHP]
    _ = L * Q := by rw [← mul_assoc Q P L, hQP, one_mul]

/-- Pairing adjointness changes a positive eigenbasis into a negative one.
No inverse or nondegeneracy condition is imposed on the pairing matrix G. -/
theorem dualEigenbasis_matrix (Hplus Hminus G P Q L : Matrix I I K)
    (hPQ : P * Q = 1) (hpositive : Hplus * P = P * L)
    (hpairing : Hminus * G + G * Hplus.transpose = 0)
    (hL : L.transpose = L) :
    Hminus * (G * Q.transpose) = -(G * Q.transpose) * L := by
  have hleft := inverse_coordinates_left_eigen Hplus P Q L hPQ hpositive
  have htranspose := congrArg Matrix.transpose hleft
  simp only [Matrix.transpose_mul, hL] at htranspose
  have hadjoint : Hminus * G = -(G * Hplus.transpose) :=
    eq_neg_of_add_eq_zero_left hpairing
  calc
    Hminus * (G * Q.transpose) = (Hminus * G) * Q.transpose := by rw [mul_assoc]
    _ = -(G * Hplus.transpose) * Q.transpose := by rw [hadjoint]
    _ = -(G * (Hplus.transpose * Q.transpose)) := by rw [neg_mul, mul_assoc]
    _ = -(G * (Q.transpose * L)) := by rw [htranspose]
    _ = -(G * Q.transpose) * L := by rw [neg_mul, mul_assoc]

theorem dualEigenbasis_diagonal (Hplus Hminus G P Q : Matrix I I K) (lambda : I → K)
    (hPQ : P * Q = 1) (hpositive : Hplus * P = P * Matrix.diagonal lambda)
    (hpairing : Hminus * G + G * Hplus.transpose = 0) :
    Hminus * (G * Q.transpose) = -(G * Q.transpose) * Matrix.diagonal lambda :=
  dualEigenbasis_matrix Hplus Hminus G P Q (Matrix.diagonal lambda)
    hPQ hpositive hpairing (Matrix.diagonal_transpose lambda)

/-- Each column of G times transpose(Q) has the opposite eigenvalue. -/
theorem dualEigenbasis_column (Hplus Hminus G P Q : Matrix I I K) (lambda : I → K)
    (hPQ : P * Q = 1) (hpositive : Hplus * P = P * Matrix.diagonal lambda)
    (hpairing : Hminus * G + G * Hplus.transpose = 0) (s : I) :
    Hminus.mulVec (fun r => (G * Q.transpose) r s) =
      (-lambda s) • (fun r => (G * Q.transpose) r s) := by
  funext r
  change (Hminus * (G * Q.transpose)) r s = (-lambda s) * (G * Q.transpose) r s
  rw [dualEigenbasis_diagonal Hplus Hminus G P Q lambda hPQ hpositive hpairing,
    Matrix.mul_diagonal]
  simp only [Matrix.neg_apply]
  ring

/-- For a diagonal inverse pairing, the negative eigenvector is precisely
the corresponding inverse-coordinate row weighted by gInv. Zero entries of
gInv require no special case or nondegeneracy assumption. -/
theorem dualEigenbasis_weightedRow (Hplus Hminus P Q : Matrix I I K)
    (lambda gInv : I → K) (hPQ : P * Q = 1)
    (hpositive : Hplus * P = P * Matrix.diagonal lambda)
    (hpairing : Hminus * Matrix.diagonal gInv +
      Matrix.diagonal gInv * Hplus.transpose = 0) (s : I) :
    Hminus.mulVec (fun r => gInv r * Q s r) =
      (-lambda s) • (fun r => gInv r * Q s r) := by
  simpa only [Matrix.diagonal_mul, Matrix.transpose_apply] using
    dualEigenbasis_column Hplus Hminus (Matrix.diagonal gInv) P Q lambda
      hPQ hpositive hpairing s

end KanadeRussell.Representation
