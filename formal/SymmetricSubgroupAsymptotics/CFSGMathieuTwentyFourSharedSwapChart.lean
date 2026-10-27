import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourTailDecodeTransport
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourSwapFibreChart

/-! Same checked degree22 packed tail, extended by two fixed points and
framed in the actual degree24 action. No new82-row certificate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourSharedSwapChart
open CFSGMathieuTailPermutationExtension CFSGMathieuTwentyFourTailDecodeTransport
open CFSGMathieuTwentyFourTwoPointTailCover

def sharedSwapDecode (c : Code22) : Equiv.Perm (Fin 24) :=
  CFSGMathieuTwentyFourPresentationWords.x.val * transport.val *
    extend24 ((CFSGMathieuTwentyTwoFiveTransversalCover.decode c).val) * transport.val⁻¹

theorem sharedSwapDecode_has_cover (d : Code24) :
    ∃ c : Code22, sharedSwapDecode c=(swapDecode d).val := by
  obtain ⟨c,hc⟩ := decode_has_shared_code d
  refine ⟨c,?_⟩
  simp only [sharedSwapDecode,hc,swapDecode,Subgroup.coe_mul,Subgroup.coe_inv]

theorem swapFibre_image_has_shared_code
    (f : CFSGMathieuTwentyFourSwapFibreOuterReduction.SwapFibre) :
    ∃ c : Code22, sharedSwapDecode c=
      CFSGMathieuTwentyFourActualRepresentation.permutationRepresentation
        (f.val.val CFSGMathieuTwentyFourGoodSylowTwentyThree.pinnedX) := by
  obtain ⟨d,hd⟩ := CFSGMathieuTwentyFourSwapFibreChart.swapFibre_image_has_code f
  obtain ⟨c,hc⟩ := sharedSwapDecode_has_cover d
  exact ⟨c,hc.trans hd⟩

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourSharedSwapChart
