import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateCenterFirstLayer
import SymmetricSubgroupAsymptotics.CFSGExceptionalNormTwoBases

/-! The actual E6/E7/E8 positive-group centre has no height-one part,
over every field. The original finite Cartan tables discharge every
neighbor condition. This is a first-height exclusion, not yet the
highest-root centre theorem or a projective intrinsic-root theorem. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGExceptionalGeckCenterFirstLayer
open CFSGNormTwoRootPairing CFSGExceptionalCartanPositiveDefinite
open CFSGExceptionalNormTwoBases CFSGNormTwoGeckPositivePGroup
open CFSGNormTwoCoordinateCenterFirstLayer

local instance centerFirstE6DecEq : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _
local instance centerFirstE7DecEq : DecidableEq (Roots CartanMatrix.E₇) := Classical.decEq _
local instance centerFirstE8DecEq : DecidableEq (Roots CartanMatrix.E₈) := Classical.decEq _

theorem E6_center_le_derived (K : Type) [Field K] :
    Subgroup.center (rootGroup CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
      E6Base E6Index K false)≤
    commutator (rootGroup CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
      E6Base E6Index K false) :=
  center_le_derived CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
    E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K (by decide)

theorem E7_center_le_derived (K : Type) [Field K] :
    Subgroup.center (rootGroup CartanMatrix.E₇ CartanMatrix.E₇_transpose E7_positive_definite
      E7Base E7Index K false)≤
    commutator (rootGroup CartanMatrix.E₇ CartanMatrix.E₇_transpose E7_positive_definite
      E7Base E7Index K false) :=
  center_le_derived CartanMatrix.E₇ CartanMatrix.E₇_diag CartanMatrix.E₇_transpose
    E7_positive_definite CartanMatrix.E₇_off_diag_nonpos K (by decide)

theorem E8_center_le_derived (K : Type) [Field K] :
    Subgroup.center (rootGroup CartanMatrix.E₈ CartanMatrix.E₈_transpose E8_positive_definite
      E8Base E8Index K false)≤
    commutator (rootGroup CartanMatrix.E₈ CartanMatrix.E₈_transpose E8_positive_definite
      E8Base E8Index K false) :=
  center_le_derived CartanMatrix.E₈ CartanMatrix.E₈_diag CartanMatrix.E₈_transpose
    E8_positive_definite CartanMatrix.E₈_off_diag_nonpos K (by decide)

end SymmetricSubgroupAsymptotics.CFSGExceptionalGeckCenterFirstLayer
