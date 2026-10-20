import SymmetricSubgroupAsymptotics.SixPairB6ElementaryCubic
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction025RegularOriginal
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction025LightPhysical

/-! One exact original-action pilot for the generic elementary-by-C3
source. Only the already checked actual top map and kernel exponent are
reused; no old scalar coordinates or nonzero-head witness are inputs. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace SixPairB6ElementaryCubicAction025
open PrimitiveAffineDegreeTwoSixPairAction025RegularPilot
open BinaryThreeQuartetCubicImageSocles
open LinearSemidirectCoprimeSocleBounds LinearSemidirectSubgroupKernelChart

abbrev actualTop : Original →* CyclicThree :=
  CubicAllNormalB6Transport.originalTop
    PrimitiveAffineDegreeTwoSixPairAction025RegularOriginal.originalEquiv (projection linear K)

theorem actualTop_surjective : Function.Surjective actualTop :=
  projection_surjective.comp
    PrimitiveAffineDegreeTwoSixPairAction025RegularOriginal.originalEquiv.surjective

theorem actualKernel_exponent (k : actualTop.ker) : k^2 = 1 := by
  let A := CubicRegularSubgroupKernelCoordinates.moduleRep K projection_surjective
  let E := CubicRegularSubgroupKernelCoordinates.originalKernelChart K projection_surjective
  let C := CubicAllNormalB6Transport.originalChart
    PrimitiveAffineDegreeTwoSixPairAction025RegularOriginal.originalEquiv
    (projection linear K) A E
  exact CubicKernelCoordinateEnvelope.kernel_exponent actualTop A C k

/-- Every original denominator of the literal action25 is covered by the
new class theorem, with its original six-pair frame retained. -/
def actionCertificate (hKP : KovacsPraegerAbelianizationBound) :
    Non2UnipotentPrefixFiniteMenu.PreE7B6ActionCertificate Original := by
  letI := PrimitiveAffineDegreeTwoSixPairAction025LightPhysical.transitive
  exact SixPairB6ElementaryCubic.actionCertificate
    PrimitiveAffineDegreeTwoSixPairAction025RegularOriginal.pairFrame
    actualTop actualTop_surjective actualKernel_exponent hKP

end SixPairB6ElementaryCubicAction025
end SymmetricSubgroupAsymptotics
end
