import SymmetricSubgroupAsymptotics.CFSGExceptionalGeckIntegralData
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckModelEvenOrder

/-! Even order for the ORIGINAL simple pinned E6/E7/E8 projective models,
over every field. All lattice/base/sign conditions are proved internally. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGExceptionalGeckModelEvenOrder
open CFSG.Models.Chevalley CFSGNormTwoRootPairing CFSGExceptionalCartanPositiveDefinite
open CFSGExceptionalNormTwoBases CFSGExceptionalGeckIntegralData CFSGNormTwoGeckModelEvenOrder

local instance exceptionalGeckEvenE6DecEq : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _
local instance exceptionalGeckEvenE7DecEq : DecidableEq (Roots CartanMatrix.E₇) := Classical.decEq _
local instance exceptionalGeckEvenE8DecEq : DecidableEq (Roots CartanMatrix.E₈) := Classical.decEq _

theorem serreTypeE6_even_card (K : Type) [Field K] [IsSimpleGroup (Projective CartanMatrix.E₆ K)] :
    Even (Nat.card (Projective CartanMatrix.E₆ K)) :=
  original_even_card_of_cartan_eq CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
    E6Base E6Index E6_simple_sign K E6_cartan 0

theorem serreTypeE7_even_card (K : Type) [Field K] [IsSimpleGroup (Projective CartanMatrix.E₇ K)] :
    Even (Nat.card (Projective CartanMatrix.E₇ K)) :=
  original_even_card_of_cartan_eq CartanMatrix.E₇ CartanMatrix.E₇_transpose E7_positive_definite
    E7Base E7Index E7_simple_sign K E7_cartan 0

theorem serreTypeE8_even_card (K : Type) [Field K] [IsSimpleGroup (Projective CartanMatrix.E₈ K)] :
    Even (Nat.card (Projective CartanMatrix.E₈ K)) :=
  original_even_card_of_cartan_eq CartanMatrix.E₈ CartanMatrix.E₈_transpose E8_positive_definite
    E8Base E8Index E8_simple_sign K E8_cartan 0

theorem typeE6_even_card (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.E6 q)] :
    Even (Nat.card (CFSG.Models.E6 q)) := serreTypeE6_even_card q.Field
theorem typeE7_even_card (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.E7 q)] :
    Even (Nat.card (CFSG.Models.E7 q)) := serreTypeE7_even_card q.Field
theorem typeE8_even_card (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.E8 q)] :
    Even (Nat.card (CFSG.Models.E8 q)) := serreTypeE8_even_card q.Field

end SymmetricSubgroupAsymptotics.CFSGExceptionalGeckModelEvenOrder
