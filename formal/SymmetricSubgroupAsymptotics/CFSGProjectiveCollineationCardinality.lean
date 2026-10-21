import SymmetricSubgroupAsymptotics.CFSGProjectiveFrameOrbitCount
import SymmetricSubgroupAsymptotics.CFSGProjectiveFrameReindex

/-! The projective collineation count follows from actual PGL frame
alignment and the independently constructed field automorphism of the
frame stabilizer. No semilinear recognition theorem is a premise. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGProjectiveCollineationCardinality
open CFSGProjectiveFrameCoordinates CFSGProjectiveFrameOrbitCount
variable {F n : Type*} [Field F] [Fintype n] [DecidableEq n] [Finite F]

theorem collineation_card_le_projective_mul_ringAut (b i j : n)
    (hbi : b ≠ i) (hbj : b ≠ j) (hij : i ≠ j) :
    Nat.card (collineationGroup (F := F) (n := n)) ≤
      Nat.card (Matrix.ProjGenLinGroup n F) * Nat.card (F ≃+* F) :=
  (collineation_card_le_projective_mul_frame b).trans
    (Nat.mul_le_mul_left _ (frameStabilizer_card_le_of_three_coordinates b i j hbi hbj hij))

end SymmetricSubgroupAsymptotics.CFSGProjectiveCollineationCardinality
