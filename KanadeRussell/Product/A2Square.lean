import KanadeRussell.Product.CubicLambert
import KanadeRussell.Product.CubicScalarExtension
import KanadeRussell.Product.A2Trisection
set_option backward.isDefEq.respectTransparency false

/-! The unconditional A₂ Lambert square identity and the product norm. -/
open PowerSeries PowerSeries.WithPiTopology
open scoped DiscreteUniformity
namespace KanadeRussell.Product

theorem a2_square : a^2 = 1+12*lambert 1-36*lambert 3 := by
  let v : CubicScalarExtension.Lˣ := CubicScalarExtension.isUnit_w.unit
  have hv : (v:CubicScalarExtension.L) = CubicScalarExtension.w := IsUnit.unit_spec _
  have hw : (v:CubicScalarExtension.L)^2+(v:CubicScalarExtension.L)+1 = 0 := by
    rw [hv]
    exact CubicScalarExtension.w_relation
  have hu : IsUnit (1-(v:CubicScalarExtension.L)) := by
    rw [hv]
    exact CubicScalarExtension.isUnit_one_sub_w
  have hh := CubicFrame.square_elliptic CubicScalarExtension.p v
    CubicScalarExtension.p_nilpotent hw CubicScalarExtension.isUnit_six hu
  have hL := CubicLambert.elliptic_level_three CubicScalarExtension.p CubicScalarExtension.p_nilpotent
  have hW := CubicLambert.elliptic_root CubicScalarExtension.p v CubicScalarExtension.p_nilpotent hw hu
  rw [hL, map_sub] at hh
  apply CubicScalarExtension.eval_injective
  simp only [map_pow, map_sub, map_add, map_one, map_mul, map_ofNat]
  simp only [CubicScalarExtension.eval]
  linear_combination hh-hW

end KanadeRussell.Product

namespace KanadeRussell

/-- The product norm is proved from convergent Jacobi identities over integer power series. -/
theorem productNorm : ProductNorm := Product.productNorm_of_square Product.a2_square

end KanadeRussell
