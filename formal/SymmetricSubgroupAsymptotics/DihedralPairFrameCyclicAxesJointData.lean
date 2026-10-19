import SymmetricSubgroupAsymptotics.DihedralPairFrameOriginalJointData
import SymmetricSubgroupAsymptotics.DihedralSixImageRecognition
import SymmetricSubgroupAsymptotics.TwoAxisAbelianizationCover

/-! Final physical consumer: actual original pair frame and six-cycle,
actual canonical dihedral image, and actual two original abelian axes.
No relative-head or generator-capacity premise is an input. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.DihedralPairFrameCyclicAxesJointData
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

 def jointData (T : DegreeTwoPairTopFiniteInterface 12)
    (F : BinaryPairFrame T.top (Fin 6)) (g : T.top)
    (hg : F.top g=SixPairCyclicSymmetricSocles.cycle)
    (himage : F.top.range=SixPairDihedralSocles.dihedralMap.range)
    (a b : T.top) {ι : Type} (generators : ι → T.top)
    (hgen : Subgroup.closure (Set.range generators)=⊤)
    (haxes : ∀ i, TwoAxisAbelianizationCover.q (generators i)∈
      TwoAxisAbelianizationCover.Left a ⊔ TwoAxisAbelianizationCover.Right b)
    (hnatural : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) T.top (Fin 12)) 2) :
    DegreeTwoTwelveJointFiniteRows.DegreeTwoTwelveJointFiniteRowData T 2 2 :=
  DihedralPairFrameOriginalJointData.jointData T F g hg
    (DihedralSixImageRecognition.topProjection F himage)
    (DihedralSixImageRecognition.topProjection_surjective F himage)
    (DihedralSixImageRecognition.top_card F himage)
    (DihedralSixImageRecognition.topProjection_kernel_card F himage)
    (TwoAxisAbelianizationCover.cover a b)
    (TwoAxisAbelianizationCover.cover_surjective a b generators hgen haxes) hnatural

end SymmetricSubgroupAsymptotics.DihedralPairFrameCyclicAxesJointData
