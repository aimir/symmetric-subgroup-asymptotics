import SymmetricSubgroupAsymptotics.CFSGTrialityGeckPositiveDerivedEquiv
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedPositiveRaw

/-! Exact raw-matrix coordinates of the SAME original derived-image
preimage. Its positive Sylow maps onto the entire genuine fixed U;
this is not surjectivity of the preimage onto the whole fixed group. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckPreimageRawCoordinates
open CFSGTrialityGeckDerivedSylowNormalizer CFSGTrialityGeckFixedDerivedMatrixLift
open CFSGTrialityGeckSourceWordAction CFSGTrialityGeckFixedPositiveImageSylow
open CFSGTrialityGeckShortCentralizerCardinality CFSGTrialityGeckFixedPositiveRaw
open CFSGTrialityGeckFixedPositiveGeneration CFSGTrialityGeckPositiveTwist
open CFSGTrialityGeckDiagramCovariance CFSGTrialityGeckMatrixGroupTwist
open CFSGTrialityGeckMatrixTwist CFSGSerreOrdinaryTwists
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) := Classical.decEq _

def preimageRawInclusion (q : CFSG.PrimePower) :
    naturalDerivedPreimage q→*(Matrix GeckIndex GeckIndex (q.Extension 3))ˣ :=
  ((MatrixGroup (q.Extension 3)).subtype.comp (FixedMatrixGroup q).subtype).comp
    (naturalDerivedPreimage q).subtype

theorem preimageRawInclusion_injective (q : CFSG.PrimePower) :
    Function.Injective (preimageRawInclusion q) :=
  Subtype.val_injective.comp (Subtype.val_injective.comp Subtype.val_injective)

theorem preimagePositiveEquiv_raw (q : CFSG.PrimePower) (u : preimageSylow q) :
    preimageRawInclusion q u.val=
      fixedPositiveInclusion (q.Extension 3) (definingFieldAutomorphism q 3)
        (preimagePositiveEquiv q u) := rfl

theorem preimageSylow_raw_image (q : CFSG.PrimePower) :
    (preimageSylow q : Subgroup (naturalDerivedPreimage q)).map (preimageRawInclusion q)=
      fixedPositiveRaw q := by
  ext x
  constructor
  · rintro ⟨u,hu,rfl⟩
    refine ⟨preimagePositiveEquiv q ⟨u,hu⟩,?_⟩
    exact (preimagePositiveEquiv_raw q ⟨u,hu⟩).symm
  · rintro ⟨u,rfl⟩
    let v := (preimagePositiveEquiv q).symm u
    refine ⟨v.val,v.property,?_⟩
    calc
      preimageRawInclusion q v.val=
          fixedPositiveInclusion (q.Extension 3) (definingFieldAutomorphism q 3)
            (preimagePositiveEquiv q v) := preimagePositiveEquiv_raw q v
      _=fixedPositiveInclusion (q.Extension 3) (definingFieldAutomorphism q 3) u :=
        congrArg (fixedPositiveInclusion (q.Extension 3) (definingFieldAutomorphism q 3))
          ((preimagePositiveEquiv q).apply_symm_apply u)

theorem preimageRawInclusion_mem_matrixGroup (q : CFSG.PrimePower) (g : naturalDerivedPreimage q) :
    preimageRawInclusion q g∈MatrixGroup (q.Extension 3) := g.val.val.property

theorem preimageRawInclusion_fixed (q : CFSG.PrimePower) (g : naturalDerivedPreimage q) :
    unitTwist (q.Extension 3) (definingFieldAutomorphism q 3) (preimageRawInclusion q g)=
      preimageRawInclusion q g := by
  have hh := congrArg (fun v : MatrixGroup (q.Extension 3)=>v.val) g.val.property
  dsimp only at hh
  change (matrixGroupTwist (q.Extension 3) (definingFieldAutomorphism q 3) g.val.val).val=
    g.val.val.val at hh
  rw [matrixGroupTwist_val] at hh
  exact hh

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckPreimageRawCoordinates
