import KanadeRussell.Tsuchioka.AffineChevalley

/-! The principal-mode pairing and the finite summands of the normal-ordered
Casimir operator. The inactive Heisenberg coordinate has pairing zero; its
inverse is zero as well. -/

namespace KanadeRussell.Tsuchioka.Fock

attribute [local instance] LieRing.ofAssociativeRing
open scoped BigOperators

variable {K : Type*} [Field K] [CharZero K]

noncomputable def principalMode (w : K) (n : ℤ) (r : Fin 3) :
    Module.End K (Space K) := tensorModeBasis w n r.castSucc

noncomputable def modePairingCoefficient (w : K) (n : ℤ) : Fin 3 → K :=
  ![Scalar.cPrime w * (-1 : K) ^ n / 18,
    Scalar.cPrime (-w) * (-1 : K) ^ n / 18,
    tensorHeisenbergPairing w n / 3]

noncomputable def normalOrderedMode (w : K) (n : ℤ) : Module.End K (Space K) :=
  ∑ r : Fin 3, (modePairingCoefficient w n r)⁻¹ •
    (principalMode w (-n) r * principalMode w n r)

noncomputable def modeCasimirLower (w : K) (n : ℤ) (i : Fin 3) :
    Module.End K (Space K) :=
  ∑ r : Fin 3, (modePairingCoefficient w n r)⁻¹ •
    (principalMode w (-n) r * ⁅principalMode w n r, chevalleyF w i⁆)

noncomputable def modeCasimirUpper (w : K) (n : ℤ) (i : Fin 3) :
    Module.End K (Space K) :=
  ∑ r : Fin 3, (modePairingCoefficient w n r)⁻¹ •
    (⁅principalMode w (-n) r, chevalleyF w i⁆ * principalMode w n r)

end KanadeRussell.Tsuchioka.Fock
