import SymmetricSubgroupAsymptotics.CFSGCommutingQuadraticExponentials
import Mathlib.Algebra.Algebra.Subalgebra.Lattice

/-! The commuting quadratic-exponential calculation in a genuinely
noncommutative algebra, by restricting to the ACTUAL subalgebra generated
by the given commuting pair. No ambient commutativity is introduced. -/
set_option autoImplicit false
set_option Elab.async false
open scoped IsMulCommutative
namespace SymmetricSubgroupAsymptotics.CFSGPairSubalgebraQuadraticExponentials
open CFSGCommutingQuadraticExponentials
variable {B : Type*} [Ring B] [Algebra ℚ B]

theorem product_difference_of_commute (x y : B) (hc : Commute x y)
    (hx : x^3=0) (hy : y^3=0) (hsum : (x+y)^3=0) (a : ℚ) :
    (1+a • (x+y)+(a^2/2) • (x+y)^2)*(1+a • (-x)+(a^2/2) • (-x)^2)=
      1+a • y+(a^2/2) • y^2 := by
  let S := Algebra.adjoin ℚ ({x,y} : Set B)
  letI : IsMulCommutative S := Algebra.isMulCommutative_adjoin ℚ (by
    intro u hu v hv
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hu hv
    rcases hu with rfl|rfl <;> rcases hv with rfl|rfl
    · rfl
    · exact hc.eq
    · exact hc.eq.symm
    · rfl)
  let X : S := ⟨x,Algebra.subset_adjoin (by simp)⟩
  let Y : S := ⟨y,Algebra.subset_adjoin (by simp)⟩
  have hX : X^3=0 := Subtype.ext hx
  have hY : Y^3=0 := Subtype.ext hy
  have hsum' : (X+Y)^3=0 := Subtype.ext hsum
  have hh := product_difference X Y hX hY hsum' a
  have hv := congrArg S.val hh
  simpa only [exponential,map_mul,map_add,map_one,map_smul,map_pow,map_neg] using hv

end SymmetricSubgroupAsymptotics.CFSGPairSubalgebraQuadraticExponentials
