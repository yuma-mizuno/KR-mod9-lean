import KanadeRussell.Infra.LaurentTorsionAddition
import KanadeRussell.Infra.LaurentTorsionInversion
import KanadeRussell.Infra.TorsionAdditionCertificate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Infra.LaurentTorsionCertificate
open LaurentTorsionCombinations LaurentTorsionAddition LaurentTorsionInversion
open Product.CubicScalarExtension (L)

theorem mixed_square (w a : ℂˣ)
    (hw : (w:ℂ)^4-(w:ℂ)^2+1=0) (ha : a^2=w) :
    3*((centeredZ w 1+centeredZ w 5)^2+
      (-centeredZ w 1+2*centeredZ w 2+centeredZ w 5)^2) =
      centeredP w 1+9*centeredP w 2-2*centeredP w 3+
      centeredP w 4+centeredP w 5+3*centeredP w 6 := by
  have z6 := centeredZ_six w hw
  have z7 : centeredZ w 7 = -centeredZ w 5 := by
    simpa using centeredZ_reflection w hw 5 (by decide) (by decide)
  have z8 : centeredZ w 8 = -centeredZ w 4 := by
    simpa using centeredZ_reflection w hw 4 (by decide) (by decide)
  have p7 : centeredP w 7 = centeredP w 5 := by
    simpa using centeredP_reflection w hw 5 (by decide) (by decide)
  have p8 : centeredP w 8 = centeredP w 4 := by
    simpa using centeredP_reflection w hw 4 (by decide) (by decide)
  have h11 := centered_pair w a hw ha 1 1 (by decide) (by decide) (by decide)
  have h12 := centered_pair w a hw ha 1 2 (by decide) (by decide) (by decide)
  have h13 := centered_pair w a hw ha 1 3 (by decide) (by decide) (by decide)
  have h14 := centered_pair w a hw ha 1 4 (by decide) (by decide) (by decide)
  have h15 := centered_pair w a hw ha 1 5 (by decide) (by decide) (by decide)
  have h22 := centered_pair w a hw ha 2 2 (by decide) (by decide) (by decide)
  have h23 := centered_pair w a hw ha 2 3 (by decide) (by decide) (by decide)
  have h24 := centered_pair w a hw ha 2 4 (by decide) (by decide) (by decide)
  have h25 := centered_pair w a hw ha 2 5 (by decide) (by decide) (by decide)
  have h33 := centered_pair w a hw ha 3 3 (by decide) (by decide) (by decide)
  have h34 := centered_pair w a hw ha 3 4 (by decide) (by decide) (by decide)
  have h44 := centered_pair w a hw ha 4 4 (by decide) (by decide) (by decide)
  norm_num only [Nat.reduceAdd] at h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h44
  simp only [z6,z7,z8,p7,p8,sub_zero,sub_neg_eq_add] at h15 h24 h25 h33 h34 h44
  apply TorsionAdditionCertificate.mixed_square_of_isUnit_six
    (centeredZ w 1) (centeredZ w 2) (centeredZ w 3) (centeredZ w 4) (centeredZ w 5)
    (centeredP w 1) (centeredP w 2) (centeredP w 3) (centeredP w 4) (centeredP w 5) (centeredP w 6)
  · linear_combination h11
  · exact h12
  · exact h13
  · exact h14
  · exact h15
  · linear_combination h22
  · exact h23
  · exact h24
  · linear_combination h25
  · linear_combination h33
  · exact h34
  · linear_combination h44
  · exact Product.CubicScalarExtension.isUnit_six
end KanadeRussell.Infra.LaurentTorsionCertificate
