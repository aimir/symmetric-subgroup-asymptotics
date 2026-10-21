import SymmetricSubgroupAsymptotics.BinarySquareActionStructure
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.CharP.Two

/-! Point-separating binary coordinate functions with constant original
translation differences force squares to act trivially on the same points. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
variable {G X I : Type} [Group G] [MulAction G X]

theorem squaresActTrivially_of_pointSeparating_constant_displacements
    (f : I → X → ZMod 2) (hinj : Function.Injective (fun x i => f i x))
    (hconstant : ∀ (g : G) (i : I) (x y : X), f i (g • x) - f i x = f i (g • y) - f i y) :
    BinarySquareActionStructure.SquaresActTrivially (G := G) (X := X) := by
  intro g x
  apply hinj
  funext i
  rw [pow_two, mul_smul]
  have h := hconstant g i (g • x) x
  simp only [CharTwo.sub_eq_add] at h
  calc
    f i (g • g • x) = (f i (g • g • x) + f i (g • x)) + f i (g • x) := by
      rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    _ = (f i (g • x) + f i x) + f i (g • x) := congrArg (fun z => z + f i (g • x)) h
    _ = f i x := by rw [add_comm (f i (g • x)) (f i x), add_assoc,
      CharTwo.add_self_eq_zero, add_zero]

end SymmetricSubgroupAsymptotics
