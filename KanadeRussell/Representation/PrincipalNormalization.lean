import KanadeRussell.Representation.AffineCyclicity

/-! The concrete regular cyclic element required by the principal-picture
character formula. Nonvanishing is checked on every D4 root. -/
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Tsuchioka.Fock
open RootData
variable {K : Type*} [Field K] [CharZero K]

/-- Rescaling the three simple positive generators by nonzero constants makes
their sum the actual degree-one principal Heisenberg element. -/
theorem principal_cyclic_element (w : K) (hw : w^4-w^2+1=0) :
    (1/4:K) • chevalleyE w 0 + (1/2:K) • chevalleyE w 1 +
      (1/4:K) • chevalleyE w 2 = heisenbergMode w 1 := by
  simpa [chevalleyEInverse,Fin.sum_univ_succ,tensorModeBasis,add_assoc] using
    chevalleyE_inverse w hw 2

/-- The Coxeter eigenfunctional is nonzero on every finite root, not just
on the two orbit representatives. -/
theorem rootWeight_root_ne_zero (w : K) (hw : w^4-w^2+1=0) (β : Root) :
    rootWeight w β.val ≠ 0 := by
  have h0 : w ≠ 0 := by intro h; rw [h] at hw; norm_num at hw
  have h1 : w ≠ 1 := by intro h; rw [h] at hw; norm_num at hw
  have hs : w^3-w^2 ≠ 0 := by
    rw [show w^3-w^2 = w^2*(w-1) by ring]
    exact mul_ne_zero (pow_ne_zero 2 h0) (sub_ne_zero.mpr h1)
  obtain ⟨r,p,hp⟩ := isRoot_mem_orbits β.val β.property
  rw [hp,orbitRoot,rootWeight_iterate w hw]
  apply mul_ne_zero (pow_ne_zero _ h0)
  fin_cases r
  · simp [orbitRepresentative]
  · simpa [orbitRepresentative] using hs

theorem rootWeight_inverse_root_ne_zero (w : K) (hw : w^4-w^2+1=0) (β : Root) :
    rootWeight (w ^ (-1:ℤ)) β.val ≠ 0 := by
  have h0 : w ≠ 0 := by intro h; rw [h] at hw; norm_num at hw
  have hi : (w⁻¹)^4-(w⁻¹)^2+1=0 := by
    field_simp
    linear_combination hw
  simpa using rootWeight_root_ne_zero w⁻¹ hi β

end KanadeRussell.Tsuchioka.Fock
