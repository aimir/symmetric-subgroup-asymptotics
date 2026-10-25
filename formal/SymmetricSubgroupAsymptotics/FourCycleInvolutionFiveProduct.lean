import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.Tactic.Group

/-! A constant rank-one word yields an actual order-five candidate in
the derived subgroup. The calculation is purely group-theoretic and
assumes neither a finite group order nor a rank-one recognition theorem. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.FourCycleInvolutionFiveProduct
variable {G : Type*} [Group G]

theorem shift_of_constant_word (y w : G) (hy : y^4 = 1) (hw : w^2 = 1)
    (hword : w = y^2 * (w*y*w⁻¹) * y^3) :
    y*w*y⁻¹ = w*y^2*w := by
  have hwI : w⁻¹ = w := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hw)
  have hwy : w*y = y^2*w*y*w := by
    calc
      _ = (y^2 * (w*y*w⁻¹) * y^3)*y := by rw [← hword]
      _ = (y^2*w*y*w⁻¹)*(y^3*y) := by group
      _ = y^2*w*y*w⁻¹ := by rw [← pow_succ, hy, mul_one]
      _ = _ := by rw [hwI]
  calc
    _ = y*w⁻¹*y⁻¹ := by rw [hwI]
    _ = w⁻¹*(w*y)*w⁻¹*y⁻¹ := by group
    _ = w⁻¹*(y^2*w*y*w)*w⁻¹*y⁻¹ := by rw [hwy]
    _ = w⁻¹*y^2*w := by group
    _ = _ := by rw [hwI]

theorem conjugate_product (y w : G) (hshift : y*w*y⁻¹ = w*y^2*w) :
    y*(w*y^2)*y⁻¹ = (w*y^2)^2 := by
  calc
    _ = (y*w*y⁻¹)*y^2 := by group
    _ = (w*y^2*w)*y^2 := by rw [hshift]
    _ = _ := by simp only [pow_two, mul_assoc]

theorem product_pow_five (y w : G) (hy : y^4 = 1) (hw : w^2 = 1)
    (hshift : y*w*y⁻¹ = w*y^2*w) : (w*y^2)^5 = 1 := by
  have hwI : w⁻¹ = w := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hw)
  have hyI : (y^2)⁻¹ = y^2 := inv_eq_of_mul_eq_one_left (by
    calc
      y^2*y^2 = y^4 := by group
      _ = 1 := hy)
  have hc := conjugate_product y w hshift
  have hd : y^2*(w*y^2)*(y^2)⁻¹ = (w*y^2)^4 := by
    calc
      _ = y*(y*(w*y^2)*y⁻¹)*y⁻¹ := by simp only [pow_two]; group
      _ = y*(w*y^2)^2*y⁻¹ := by rw [hc]
      _ = (y*(w*y^2)*y⁻¹)^2 := by simp only [pow_two]; group
      _ = ((w*y^2)^2)^2 := by rw [hc]
      _ = _ := by group
  have hi : y^2*(w*y^2)*(y^2)⁻¹ = (w*y^2)⁻¹ := by
    calc
      _ = y^2*w := by group
      _ = (y^2)⁻¹*w⁻¹ := by rw [hyI, hwI]
      _ = _ := by rw [mul_inv_rev]
  have he : (w*y^2)^4 = (w*y^2)⁻¹ := hd.symm.trans hi
  calc
    _ = (w*y^2)^4*(w*y^2) := by rw [pow_succ]
    _ = (w*y^2)⁻¹*(w*y^2) := by rw [he]
    _ = 1 := inv_mul_cancel _

theorem product_mem_commutator (y w : G) (hshift : y*w*y⁻¹ = w*y^2*w) :
    w*y^2 ∈ commutator G := by
  let f : G →* Abelianization G := Abelianization.of
  have he : f w = f w*(f y)^2*f w := by
    calc
      _ = f y*f w*(f y)⁻¹ := by
        rw [mul_comm (f y) (f w), mul_assoc, mul_inv_cancel, mul_one]
      _ = _ := by
        simpa only [map_mul, map_inv, map_pow] using congrArg f hshift
  have hr : f (w*y^2) = 1 := by
    calc
      _ = f w*(f y)^2 := by rw [map_mul, map_pow]
      _ = (f y)^2*f w := mul_comm _ _
      _ = (f w)⁻¹*(f w*(f y)^2*f w) := by group
      _ = (f w)⁻¹*f w := by rw [← he]
      _ = 1 := inv_mul_cancel _
  have hk : w*y^2 ∈ (Abelianization.of : G →* Abelianization G).ker := hr
  rwa [Abelianization.ker_of] at hk

end SymmetricSubgroupAsymptotics.FourCycleInvolutionFiveProduct
