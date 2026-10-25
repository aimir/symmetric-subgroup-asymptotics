import SymmetricSubgroupAsymptotics.CFSGFFourBinaryLeviConjugationGraph

/-! The graph's actual normal radical is the original displayed
Heisenberg4 × central6 group. Its central-coordinate embedding is
faithful and equivariant for the SAME graph action. No split extension
or full native image is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourBinaryGraphCentralLayers
open CFSGFFourBinaryLeviConjugationGraph CFSGFFourBinaryActualNormalizerCoordinates
open CFSGFFourBinaryFixedRadicalEmbedding CFSGFFourBinaryRadicalCentralLayers
open CFSGFFourBinaryNativeCentralAction
local instance fFourGraphLayersRootsDecidableEq :
    DecidableEq (CFSGNormTwoRootPairing.Roots CartanMatrix.E₆) := Classical.decEq _
variable (K : Type) [Field K] [Finite K] [CharP K 2] (hK : Nat.card K=2)

def liftedRadical : Subgroup (Graph K hK) :=
  CFSGConjugationGraphNormalLift.normalLift
    (nativeCentralAction K hK) (centralHom K) (normalRadical K)

instance liftedRadical_normal : (liftedRadical K hK).Normal :=
  inferInstanceAs (CFSGConjugationGraphNormalLift.normalLift
    (nativeCentralAction K hK) (centralHom K) (normalRadical K)).Normal

def radicalEquiv : Radical K ≃* liftedRadical K hK :=
  (normalRadicalEquiv K).trans
    (CFSGConjugationGraphNormalLift.normalLiftEquiv
      (nativeCentralAction K hK) (centralHom K) (normalRadical K)
      (nativeCentralAction_injective K hK) (centralHom_injective K)
      (centralHom_commutes_normalRadical K))

theorem radicalEquiv_second (r : Radical K) :
    second K hK ((radicalEquiv K hK r).val) = radicalHom K r := rfl

def centralLift : CentralCoordinates K →* liftedRadical K hK :=
  (radicalEquiv K hK).toMonoidHom.comp (centralCoordinates K)

theorem centralLift_second (z : CentralCoordinates K) :
    second K hK ((centralLift K hK z).val) = centralHom K z := rfl

theorem centralLift_injective : Function.Injective (centralLift K hK) :=
  (radicalEquiv K hK).injective.comp (centralCoordinates_injective K)

theorem centralLift_covariance (p : Graph K hK) (z : CentralCoordinates K) :
    centralLift K hK (nativeCentralAction K hK (first K hK p) z) =
      MulAut.conjNormal p (centralLift K hK z) := by
  apply Subtype.ext
  apply second_injective K hK
  change centralHom K (nativeCentralAction K hK (first K hK p) z) =
    second K hK p * centralHom K z * (second K hK p)⁻¹
  exact ((mul_inv_eq_iff_eq_mul).mpr (p.property z)).symm

end SymmetricSubgroupAsymptotics.CFSGFFourBinaryGraphCentralLayers
