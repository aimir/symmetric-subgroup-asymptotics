import SymmetricSubgroupAsymptotics.CFSGTrialityBinaryMiddleNormalizer
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckGeneratedOriginalProjection

/-! The same middle radical as a normal subgroup of its actual
generated normalizer. The original projection is faithful on this
radical because it is faithful on the actual positive root part. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityBinaryMiddleSource
open CFSGTrialityBinaryMiddleNormalizer CFSGTrialityGeckMiddleFixedCommutators
open CFSGTrialityGeckGeneratedOriginalProjection CFSGTrialityGeckRootGeneratedPGroup
open CFSGTrialityGeckFixedPositiveRaw CFSGSerreOrdinaryTwists

def liftedMiddle (q : CFSG.PrimePower) : Subgroup (carrier q) :=
  (fixedMiddle q).subgroupOf (carrier q)

instance liftedMiddle_normal (q : CFSG.PrimePower) : (liftedMiddle q).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (middle_le_carrier q)).mpr inf_le_left

def middleEquiv (q : CFSG.PrimePower) : liftedMiddle q ≃* fixedMiddle q :=
  Subgroup.subgroupOfEquivOfLe (middle_le_carrier q)

theorem middleEquiv_val (q : CFSG.PrimePower) (u : liftedMiddle q) :
    (middleEquiv q u).val=u.val.val := rfl

def middleLift (q : CFSG.PrimePower) : fixedMiddle q →* carrier q :=
  Subgroup.inclusion (middle_le_carrier q)

theorem middleLift_val (q : CFSG.PrimePower) (u : fixedMiddle q) :
    (middleLift q u).val=u.val := rfl

def originalHom (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TrialityD4 q)] :
    carrier q →* CFSG.Models.TrialityD4 q :=
  (generatedToOriginal q).comp (Subgroup.inclusion inf_le_right)

theorem original_middle_injective (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] :
    Function.Injective ((originalHom q).comp (middleLift q)) := by
  intro u v huv
  let x : rootPart (q.Extension 3) (definingFieldAutomorphism q 3) false :=
    ⟨⟨u.val,(middle_le_carrier q u.property).2⟩,
      (mem_fixedPositiveRaw_iff q u.val).mp u.property.2⟩
  let y : rootPart (q.Extension 3) (definingFieldAutomorphism q 3) false :=
    ⟨⟨v.val,(middle_le_carrier q v.property).2⟩,
      (mem_fixedPositiveRaw_iff q v.val).mp v.property.2⟩
  have hxy : (generatedToOriginal q) x.val=(generatedToOriginal q) y.val := huv
  have he : x=y := rootPart_positive_original_injective q hxy
  exact Subtype.ext (congrArg (fun z : rootPart (q.Extension 3)
    (definingFieldAutomorphism q 3) false => z.val.val) he)

end SymmetricSubgroupAsymptotics.CFSGTrialityBinaryMiddleSource
