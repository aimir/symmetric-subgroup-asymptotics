import Mathlib.Algebra.Group.Subgroup.Basic

/-! Exact short recovery for a (2,3) generating pair. For a=x*y and
u=x*a*x^-1, the original pair is x=a^-1*u^-1*a^-1, y=a^-1*u^-1.
No simplicity, finiteness, or accepted-image capacity is required. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.InvolutionTernaryProductShortRecovery

variable {G : Type*} [Group G]

theorem conjugate_product_eq_reverse (x y : G) (hx : x^2=1) :
    x*(x*y)*x⁻¹ = y*x := by
  have hxx : x*x=1 := by simpa only [pow_two] using hx
  have hi : x⁻¹=x := inv_eq_of_mul_eq_one_right hxx
  rw [←mul_assoc,hxx,one_mul,hi]

theorem recover_second (x y : G) (hx : x^2=1) (hy : y^3=1) :
    (x*y)⁻¹*(x*(x*y)*x⁻¹)⁻¹ = y := by
  have hxx : x*x=1 := by simpa only [pow_two] using hx
  have hi : x⁻¹=x := inv_eq_of_mul_eq_one_right hxx
  have hyy : y⁻¹*y⁻¹=y := by
    have hc : y^2*y=1 := by simpa only [←pow_succ] using hy
    simpa only [pow_two,mul_inv_rev] using inv_eq_of_mul_eq_one_right hc
  calc
    (x*y)⁻¹*(x*(x*y)*x⁻¹)⁻¹ = y⁻¹*x*(x*y⁻¹) := by
      rw [conjugate_product_eq_reverse x y hx]
      simp only [mul_inv_rev,hi]
    _ = y⁻¹*(x*x)*y⁻¹ := by simp only [mul_assoc]
    _ = y := by rw [hxx,mul_one,hyy]

theorem recover_first (x y : G) (hx : x^2=1) (hy : y^3=1) :
    (x*y)⁻¹*(x*(x*y)*x⁻¹)⁻¹*(x*y)⁻¹ = x := by
  have hi : x⁻¹=x := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hx)
  rw [recover_second x y hx hy,mul_inv_rev,←mul_assoc,mul_inv_cancel,one_mul,hi]

theorem closure_product_conjugate_eq_top (x y : G) (hx : x^2=1) (hy : y^3=1)
    (hgen : Subgroup.closure ({x,y} : Set G) = ⊤) :
    Subgroup.closure ({x*y,x*(x*y)*x⁻¹} : Set G) = ⊤ := by
  let R := Subgroup.closure ({x*y,x*(x*y)*x⁻¹} : Set G)
  have ha : x*y ∈ R := Subgroup.subset_closure (Or.inl rfl)
  have hu : x*(x*y)*x⁻¹ ∈ R := Subgroup.subset_closure (Or.inr rfl)
  have hyR : y ∈ R := by
    rw [←recover_second x y hx hy]
    exact R.mul_mem (R.inv_mem ha) (R.inv_mem hu)
  have hxR : x ∈ R := by
    rw [←recover_first x y hx hy]
    exact R.mul_mem (R.mul_mem (R.inv_mem ha) (R.inv_mem hu)) (R.inv_mem ha)
  apply top_unique
  rw [←hgen]
  apply (Subgroup.closure_le R).mpr
  rintro z (rfl|rfl)
  · exact hxR
  · exact hyR

end SymmetricSubgroupAsymptotics.InvolutionTernaryProductShortRecovery
