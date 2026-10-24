import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleFixedQuotientCoordinates
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedHighestParameters
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootElementRange

/-! The actual highest-root parameter line in the literal fixed radical.
Its parameter field is proved from actual fixedness, and its image is
exactly the kernel of the constructed first-coordinate projection. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleFixedCentralParameters

open CFSGTrialityD4NormTwo CFSGTrialityD4PositiveRootOrbits
open CFSGTrialityGeckDiagramCovariance CFSGTrialityMiddleFixedTensorSpan
open CFSGTrialityGeckMiddleFixedCommutators CFSGTrialityGeckMiddleRadicalQuotient
open CFSGTrialityGeckMiddleFixedQuotientCoordinates CFSGTrialityGeckFixedPositiveRaw
open CFSGTrialityGeckFixedHighestParameters CFSGNormTwoCoordinateSelectedRootElement
open CFSGNormTwoCoordinateSelectedRootAdditive CFSGNormTwoCoordinateAllRootParameters
open CFSGNormTwoCoordinateRootElementRange CFSGSerreOrdinaryTwists

local notation "A" => CartanMatrix.D 4
local notation "hd" => CartanMatrix.D_diag 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite
local notation "ho" => CartanMatrix.D_off_diag_nonpos 4
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots A) := Classical.decEq _

private def rawCentral (q : CFSG.PrimePower) : Multiplicative (F q) →* Raw (K q) :=
  (selectedRootHom A hd hs hp ho (K q) (longRoot 2)).comp
    (CFSGTrialityFixedField.fixedField q).subtype.toAddMonoidHom.toMultiplicative

private theorem rawCentral_mem (q : CFSG.PrimePower) (t : Multiplicative (F q)) :
    rawCentral q t ∈ fixedMiddle q := by
  have hhigh : rawCentral q t ∈ highestLine (K q) :=
    (mem_rootSubgroup_iff_selected A hd hs hp ho (K q) (longRoot 2) _).mpr ⟨t.toAdd.val,rfl⟩
  have hmid := highest_le_middle (K q) hhigh
  refine ⟨hmid,(mem_fixedPositiveRaw_iff q _).mpr ⟨middle_le_positive _ hmid,?_⟩⟩
  change CFSGTrialityGeckMatrixTwist.unitTwist (K q) (definingFieldAutomorphism q 3)
    (selectedRootElement A hd hs hp ho (K q) (longRoot 2) t.toAdd.val) = _
  exact (highest_selected_twist q t.toAdd.val).trans
    (congrArg (selectedRootElement A hd hs hp ho (K q) (longRoot 2)) t.toAdd.property)

def central (q : CFSG.PrimePower) : Multiplicative (F q) →* fixedMiddle q :=
  (rawCentral q).codRestrict (fixedMiddle q) (rawCentral_mem q)

theorem central_val (q : CFSG.PrimePower) (t : Multiplicative (F q)) :
    (central q t).val = selectedRootElement A hd hs hp ho (K q) (longRoot 2) t.toAdd.val := rfl

theorem central_injective (q : CFSG.PrimePower) : Function.Injective (central q) := by
  intro s t he
  have hr := congrArg (fun z : fixedMiddle q => z.val) he
  have hp' : Multiplicative.ofAdd s.toAdd.val = Multiplicative.ofAdd t.toAdd.val :=
    selected_rootHom_injective A hd hs hp ho (K q) (longRoot 2) hr
  exact congrArg Multiplicative.ofAdd (Subtype.ext (congrArg Multiplicative.toAdd hp'))

theorem central_range (q : CFSG.PrimePower) : (central q).range = (projection q).ker := by
  ext u
  constructor
  · rintro ⟨t,rfl⟩
    apply (mem_projection_kernel_iff q _).mpr
    exact (mem_rootSubgroup_iff_selected A hd hs hp ho (K q) (longRoot 2) _).mpr
      ⟨t.toAdd.val,rfl⟩
  · intro hu
    have hhigh := (mem_projection_kernel_iff q u).mp hu
    obtain ⟨t,ht⟩ := (mem_rootSubgroup_iff_selected A hd hs hp ho (K q) (longRoot 2) u.val).mp hhigh
    have hfix := ((mem_fixedPositiveRaw_iff q u.val).mp u.property.2).2
    have htf := fixed_highest_parameter q t
      ((congrArg (CFSGTrialityGeckMatrixTwist.unitTwist (K q) (definingFieldAutomorphism q 3)) ht).trans
        (hfix.trans ht.symm))
    refine ⟨Multiplicative.ofAdd ⟨t,htf⟩,?_⟩
    exact Subtype.ext ht

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleFixedCentralParameters
