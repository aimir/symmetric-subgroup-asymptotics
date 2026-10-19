import SymmetricSubgroupAsymptotics.BinaryTwistedQuartetLoewyAugmentations

/-! The four actual augmentation/cycle words of a vector with nonzero
top span the ENTIRE middle layer. Only its two-coordinate nonzero top
is considered in the finite spanning fact. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.BinaryTwistedQuartetAugmentationMiddle
open BinaryTwistedQuartetPolynomial (Bit Plane cubic)
open BinaryTwistedQuartetLoewyCoordinates
open BinaryTwistedQuartetLoewyAugmentations

theorem middle_flip (v : Space) :
    middle (v+flipAction v)=
      (cubic (sumBlocks v),cubic (cubic (sumBlocks v))) := by
  apply Prod.ext <;> ext i <;> fin_cases i <;>
    simp [middle,flipAction,sumBlocks,cubic,Matrix.vecHead,Matrix.vecTail] <;>
    ring_nf <;>
    simp only [show (2 : Bit)=0 by decide,show (3 : Bit)=1 by decide,
      show (4 : Bit)=0 by decide,show (5 : Bit)=1 by decide,
      show (6 : Bit)=0 by decide,show (7 : Bit)=1 by decide,
      mul_zero,mul_one,add_zero,zero_add] <;> ring

theorem middle_second (v : Space) :
    middle (v+secondFlip v)=
      (cubic (cubic (sumBlocks v)),cubic (sumBlocks v)) := by
  apply Prod.ext <;> ext i <;> fin_cases i <;>
    simp [middle,secondFlip,sumBlocks,cubic,Matrix.vecHead,Matrix.vecTail] <;>
    ring_nf <;>
    simp only [show (2 : Bit)=0 by decide,show (3 : Bit)=1 by decide,
      show (4 : Bit)=0 by decide,show (5 : Bit)=1 by decide,
      show (6 : Bit)=0 by decide,show (7 : Bit)=1 by decide,
      mul_zero,mul_one,add_zero,zero_add] <;> ring

/-- The top has four possible values; a nonzero one yields these four
binary middle generators, with no subspace enumeration. -/
theorem middle_span : ∀ u p q : Plane, u≠0 → ∃ a b c d : Bit,
    (p,q)=a • (cubic u,cubic (cubic u))+
      b • (cubic (cubic u),cubic u)+c • (cubic u,cubic u)+
      d • (cubic (cubic u),u) := by decide +kernel

end SymmetricSubgroupAsymptotics.BinaryTwistedQuartetAugmentationMiddle
