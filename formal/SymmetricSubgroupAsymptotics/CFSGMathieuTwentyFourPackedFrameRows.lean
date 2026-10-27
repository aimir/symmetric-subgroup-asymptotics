import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourTwoPointTailCover
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourSwapFibreOuterReduction
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourPackedFrameRows
open CFSGMathieuTwentyFourTwoPointTailCover
open CFSGMathieuTwentyFourPresentationWords
open CFSGMathieuTwentyFourSwapFibreOuterReduction
open CFSGMathieuTwentyFourActualRepresentation

def packedGet (row p : ℕ) : ℕ := row / 2^(5*p) % 32

def xRow : ℕ := 378577756234503423923776693813855407

def xInverseRow : ℕ := 378577756234503423923776693813855407

def frameRow : ℕ := 347418233530201897943447781848915365

def frameInverseRow : ℕ := 682286916999211180009083166104241379

def productRow : ℕ := 387131862487254146160449033921224211

def productInverseRow : ℕ := 97727003354209774580861688826971599

theorem x_point_binding : ∀ p : Fin 24,
    packedGet xRow p.val=(x.val p).val ∧
    packedGet xInverseRow p.val=((x.val).symm p).val := by
  rw [x_coe_eq]
  decide +kernel

theorem frame_point_binding : ∀ p : Fin 24,
    packedGet frameRow p.val=(transport.val p).val ∧
    packedGet frameInverseRow p.val=((transport.val).symm p).val := by
  unfold transport CFSGMathieuTwentyFourTwoPointTailCover.frameFirst
  decide +kernel

theorem product_point_binding : ∀ p : Fin 24,
    packedGet productRow p.val=(permutationRepresentation product p).val ∧
    packedGet productInverseRow p.val=((permutationRepresentation product).symm p).val := by
  rw [product_image_eq]
  decide +kernel

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourPackedFrameRows
