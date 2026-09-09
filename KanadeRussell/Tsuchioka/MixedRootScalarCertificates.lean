import KanadeRussell.Tsuchioka.ScalarPhases

/-! Exact polynomial certificates for both mixed-root rational expansions.
The hypotheses are only the cyclotomic equation and geometric denominators. -/

set_option maxRecDepth 4096

namespace KanadeRussell.Tsuchioka.Scalar.Certificates

variable {A : Type*} [CommRing A]

theorem mixed_first_second (w x g0 g2 g9 g11 : A)
    (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (hg0 : g0 * (1 - (1) * x) = 1)
    (hg2 : g2 * (1 - (1 - w ^ 2) * x) = 1)
    (hg9 : g9 * (1 - (w ^ 3) * x) = 1)
    (hg11 : g11 * (1 - (w) * x) = 1)
    : (1 + (6 * w ^ 3 + 8 * w ^ 2 - 4) * g0 + (6 * w ^ 3 - 8 * w ^ 2 + 4) * g2 + (-6 * w ^ 3 + 8 * w ^ 2 - 4) * g9 + (-6 * w ^ 3 - 8 * w ^ 2 + 4) * g11) * ((1 - (1) * x) * (1 - (1 - w ^ 2) * x) * (1 - (w ^ 3) * x) * (1 - (w) * x)) = (1 - (-w ^ 3) * x) * (1 - (-w) * x) * (1 - (-1) * x) * (1 - (w ^ 2 - 1) * x) := by
  have hb : (1 - (1) * x) * (1 - (1 - w ^ 2) * x) * (1 - (w ^ 3) * x) * (1 - (w) * x) + (6 * w ^ 3 + 8 * w ^ 2 - 4) * ((1 - (1 - w ^ 2) * x) * (1 - (w ^ 3) * x) * (1 - (w) * x)) + (6 * w ^ 3 - 8 * w ^ 2 + 4) * ((1 - (1) * x) * (1 - (w ^ 3) * x) * (1 - (w) * x)) + (-6 * w ^ 3 + 8 * w ^ 2 - 4) * ((1 - (1) * x) * (1 - (1 - w ^ 2) * x) * (1 - (w) * x)) + (-6 * w ^ 3 - 8 * w ^ 2 + 4) * ((1 - (1) * x) * (1 - (1 - w ^ 2) * x) * (1 - (w ^ 3) * x)) = (1 - (-w ^ 3) * x) * (1 - (-w) * x) * (1 - (-1) * x) * (1 - (w ^ 2 - 1) * x) := by
    linear_combination (6 * w ^ 5 * x ^ 3 + 2 * w ^ 4 * x ^ 3 + w ^ 3 * (-14 * x ^ 3 + 12 * x ^ 2) - 6 * w ^ 2 * x + w * (2 * x ^ 3 - 8 * x ^ 2 + 2 * x) - 4 * x) * hw
  linear_combination hb +
    (6 * w ^ 3 + 8 * w ^ 2 - 4) * ((1 - (1 - w ^ 2) * x) * (1 - (w ^ 3) * x) * (1 - (w) * x)) * hg0 +
    (6 * w ^ 3 - 8 * w ^ 2 + 4) * ((1 - (1) * x) * (1 - (w ^ 3) * x) * (1 - (w) * x)) * hg2 +
    (-6 * w ^ 3 + 8 * w ^ 2 - 4) * ((1 - (1) * x) * (1 - (1 - w ^ 2) * x) * (1 - (w) * x)) * hg9 +
    (-6 * w ^ 3 - 8 * w ^ 2 + 4) * ((1 - (1) * x) * (1 - (1 - w ^ 2) * x) * (1 - (w ^ 3) * x)) * hg11

theorem mixed_second_first (w x g0 g1 g3 g10 : A)
    (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (hg0 : g0 * (1 - (1) * x) = 1)
    (hg1 : g1 * (1 - (-w ^ 3 + w) * x) = 1)
    (hg3 : g3 * (1 - (-w ^ 3) * x) = 1)
    (hg10 : g10 * (1 - (w ^ 2) * x) = 1)
    : (1 + (-6 * w ^ 3 - 8 * w ^ 2 + 4) * g0 + (6 * w ^ 3 + 8 * w ^ 2 - 4) * g1 + (6 * w ^ 3 - 8 * w ^ 2 + 4) * g3 + (-6 * w ^ 3 + 8 * w ^ 2 - 4) * g10) * ((1 - (1) * x) * (1 - (-w ^ 3 + w) * x) * (1 - (-w ^ 3) * x) * (1 - (w ^ 2) * x)) = (1 - (-w ^ 2) * x) * (1 - (-1) * x) * (1 - (w ^ 3 - w) * x) * (1 - (w ^ 3) * x) := by
  have hb : (1 - (1) * x) * (1 - (-w ^ 3 + w) * x) * (1 - (-w ^ 3) * x) * (1 - (w ^ 2) * x) + (-6 * w ^ 3 - 8 * w ^ 2 + 4) * ((1 - (-w ^ 3 + w) * x) * (1 - (-w ^ 3) * x) * (1 - (w ^ 2) * x)) + (6 * w ^ 3 + 8 * w ^ 2 - 4) * ((1 - (1) * x) * (1 - (-w ^ 3) * x) * (1 - (w ^ 2) * x)) + (6 * w ^ 3 - 8 * w ^ 2 + 4) * ((1 - (1) * x) * (1 - (-w ^ 3 + w) * x) * (1 - (w ^ 2) * x)) + (-6 * w ^ 3 + 8 * w ^ 2 - 4) * ((1 - (1) * x) * (1 - (-w ^ 3 + w) * x) * (1 - (-w ^ 3) * x)) = (1 - (-w ^ 2) * x) * (1 - (-1) * x) * (1 - (w ^ 3 - w) * x) * (1 - (w ^ 3) * x) := by
    linear_combination (6 * w ^ 7 * x ^ 3 + 8 * w ^ 6 * x ^ 3 + w ^ 5 * (6 * x ^ 3 - 12 * x ^ 2) - 2 * w ^ 4 * x ^ 3 + w ^ 3 * (-6 * x ^ 3 + 16 * x ^ 2) - 12 * w ^ 2 * x - 6 * w * x + 2 * x) * hw
  linear_combination hb +
    (-6 * w ^ 3 - 8 * w ^ 2 + 4) * ((1 - (-w ^ 3 + w) * x) * (1 - (-w ^ 3) * x) * (1 - (w ^ 2) * x)) * hg0 +
    (6 * w ^ 3 + 8 * w ^ 2 - 4) * ((1 - (1) * x) * (1 - (-w ^ 3) * x) * (1 - (w ^ 2) * x)) * hg1 +
    (6 * w ^ 3 - 8 * w ^ 2 + 4) * ((1 - (1) * x) * (1 - (-w ^ 3 + w) * x) * (1 - (w ^ 2) * x)) * hg3 +
    (-6 * w ^ 3 + 8 * w ^ 2 - 4) * ((1 - (1) * x) * (1 - (-w ^ 3 + w) * x) * (1 - (-w ^ 3) * x)) * hg10

end KanadeRussell.Tsuchioka.Scalar.Certificates
