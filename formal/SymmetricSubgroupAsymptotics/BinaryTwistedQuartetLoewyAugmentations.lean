import SymmetricSubgroupAsymptotics.BinaryTwistedQuartetLoewyCoordinates

/-! Actual V4 augmentation operators on the radical land in its cubic
socle. Their common kernel is exactly the constant-plane socle. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.BinaryTwistedQuartetLoewyAugmentations
open BinaryTwistedQuartetPolynomial (Bit Plane)
open BinaryTwistedQuartetLoewyCoordinates

def secondFlip (v : Space) : Space := ![v 2,v 3,v 0,v 1]

private theorem flip_formula (v : Space) : v+flipAction v=
    ![v 0+v 3,(v 0+v 3)+sumBlocks v,(v 0+v 3)+sumBlocks v,v 0+v 3] := by
  funext i j
  fin_cases i <;> fin_cases j <;> simp [flipAction,sumBlocks] <;> ring_nf <;>
    simp only [show (2 : Bit)=0 by decide,mul_zero,add_zero,zero_add]

private theorem second_formula (v : Space) : v+secondFlip v=
    ![v 0+v 2,(v 0+v 2)+sumBlocks v,v 0+v 2,(v 0+v 2)+sumBlocks v] := by
  funext i j
  fin_cases i <;> fin_cases j <;> simp [secondFlip,sumBlocks] <;> ring_nf <;>
    simp only [show (2 : Bit)=0 by decide,mul_zero,add_zero,zero_add]

theorem flip_radical (v : Space) (hv : sumBlocks v=0) :
    v+flipAction v=constant (v 0+v 3) := by
  rw [flip_formula,hv]
  funext i
  fin_cases i <;> simp [constant]

theorem second_radical (v : Space) (hv : sumBlocks v=0) :
    v+secondFlip v=constant (v 0+v 2) := by
  rw [second_formula,hv]
  funext i
  fin_cases i <;> simp [constant]

/-- The two V4 involutions have no extra common fixed vectors. -/
theorem common_fixed_constant (v : Space)
    (hfirst : flipAction v=v) (hsecond : secondFlip v=v) : v=constant (v 0) := by
  have h3 : v 3=v 0 := congrArg (fun w : Space => w 0) hfirst
  have h2 : v 2=v 0 := congrArg (fun w : Space => w 0) hsecond
  have h1 : v 1=v 2 := congrArg (fun w : Space => w 2) hfirst
  funext i
  fin_cases i
  · rfl
  · exact h1.trans h2
  · exact h2
  · exact h3

end SymmetricSubgroupAsymptotics.BinaryTwistedQuartetLoewyAugmentations
