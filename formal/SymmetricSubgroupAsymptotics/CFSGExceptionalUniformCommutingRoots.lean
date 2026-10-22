import SymmetricSubgroupAsymptotics.CFSGExceptionalOrthogonalA4Roots
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOrthogonalTransport
import SymmetricSubgroupAsymptotics.CFSGExceptionalNormTwoBases

/-! Ten actual positive roots centralize every lattice-labelled root
in each pinned E6/E7/E8 system. The explicit A4 witness is transported
by actual original reflection words and normalized only by root signs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGExceptionalUniformCommutingRoots
open CFSGNormTwoRootPairing CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGExceptionalOrthogonalA4Roots CFSGNormTwoCoordinateOrthogonalTransport
open CFSGNormTwoCoordinateRootCentralizerCardinality
local instance : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _
local instance : DecidableEq (Roots CartanMatrix.E₇) := Classical.decEq _
local instance : DecidableEq (Roots CartanMatrix.E₈) := Classical.decEq _

theorem E6_uniform_commuting (k : Roots CartanMatrix.E₆) :
    10≤(commutingPositiveRoots CartanMatrix.E₆ k).card := by
  obtain ⟨f,hf,horth⟩ := E6_ten_positive_orthogonal
  exact uniform_commuting_card_of_orthogonal_witness CartanMatrix.E₆ CartanMatrix.E₆_diag
    CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos
    (coordinateRoot CartanMatrix.E₆ CartanMatrix.E₆_diag 0) f hf horth k

theorem E7_uniform_commuting (k : Roots CartanMatrix.E₇) :
    10≤(commutingPositiveRoots CartanMatrix.E₇ k).card := by
  obtain ⟨f,hf,horth⟩ := E7_ten_positive_orthogonal
  exact uniform_commuting_card_of_orthogonal_witness CartanMatrix.E₇ CartanMatrix.E₇_diag
    CartanMatrix.E₇_transpose E7_positive_definite CartanMatrix.E₇_off_diag_nonpos
    (coordinateRoot CartanMatrix.E₇ CartanMatrix.E₇_diag 0) f hf horth k

theorem E8_uniform_commuting (k : Roots CartanMatrix.E₈) :
    10≤(commutingPositiveRoots CartanMatrix.E₈ k).card := by
  obtain ⟨f,hf,horth⟩ := E8_ten_positive_orthogonal
  exact uniform_commuting_card_of_orthogonal_witness CartanMatrix.E₈ CartanMatrix.E₈_diag
    CartanMatrix.E₈_transpose E8_positive_definite CartanMatrix.E₈_off_diag_nonpos
    (coordinateRoot CartanMatrix.E₈ CartanMatrix.E₈_diag 0) f hf horth k

end SymmetricSubgroupAsymptotics.CFSGExceptionalUniformCommutingRoots
