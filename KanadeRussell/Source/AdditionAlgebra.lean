import Mathlib

/-! Polynomial certificates for the addition theorem (paper `eq:app-bilinear-certificate`). -/

namespace KanadeRussell.Source

variable {R : Type*} [CommRing R]

/-- The bilinear addition expression solves the scalar equation whenever its two
factors satisfy the source difference systems. All relations are polynomial. -/
theorem addition_polynomial
    (q x a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ p₀ p₁ p₂ p₃ p₄ : R)
    (ha₁ : a₁ = a₀ - q * x * b₁)
    (ha₂ : a₂ = a₁ - q ^ 2 * x * b₂)
    (ha₃ : a₃ = a₂ - q ^ 3 * x * b₃)
    (hb₂ : b₂ = x * b₀ + b₁ - x * a₁)
    (hb₃ : b₃ = q * x * b₁ + b₂ - q * x * a₂)
    (hp₀ : p₀ = (1 - q * x) * p₁ + q * x * (1 + q + q ^ 2 * x ^ 2) * p₂ + q ^ 4 * x ^ 2 * p₃)
    (hp₁ : p₁ = (1 - q ^ 2 * x) * p₂ + q ^ 2 * x * (1 + q + q ^ 4 * x ^ 2) * p₃ + q ^ 6 * x ^ 2 * p₄) :
    q * (a₀ * (p₀ + q * x * p₁) + q * x ^ 2 * b₀ * p₁) -
    (1 + q + q ^ 2 * x ^ 2) * (a₁ * (p₁ + q ^ 2 * x * p₂) + q ^ 3 * x ^ 2 * b₁ * p₂) +
    (1 - q ^ 2 * x) * (a₂ * (p₂ + q ^ 3 * x * p₃) + q ^ 5 * x ^ 2 * b₂ * p₃) +
    q ^ 2 * x * (a₃ * (p₃ + q ^ 4 * x * p₄) + q ^ 7 * x ^ 2 * b₃ * p₄) = 0 := by
  rw [ha₃, hb₃, ha₂, hb₂, ha₁, hp₀, hp₁]
  ring

/-- Polynomial elimination giving the third addition formula. -/
theorem addition_minus_polynomial
    (q x a₀ a₁ b₀ b₁ b₂ p₀ p₁ p₂ p₃ : R)
    (ha₁ : a₁ = a₀ - q * x * b₁)
    (hb₂ : b₂ = x * b₀ + b₁ - x * a₁)
    (hp₀ : p₀ = (1 - q * x) * p₁ + q * x * (1 + q + q ^ 2 * x ^ 2) * p₂ + q ^ 4 * x ^ 2 * p₃) :
    (a₀ * (p₀ + q * x * p₁) + q * x ^ 2 * b₀ * p₁) -
      (a₀ * (p₁ + q ^ 2 * x * p₂) - q * x * b₁ * p₁) -
      q * x * (a₁ * (p₂ + q ^ 3 * x * p₃) - q ^ 2 * x * b₂ * p₂) =
      q * x * (x * b₀ * (p₁ + q ^ 2 * x * p₂) + b₁ * (p₀ + q * x * p₁)) := by
  rw [hb₂, ha₁, hp₀]
  ring

end KanadeRussell.Source
