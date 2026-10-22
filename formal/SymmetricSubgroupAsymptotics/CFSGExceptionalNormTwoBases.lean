import SymmetricSubgroupAsymptotics.CFSGExceptionalNormTwoFinite
import SymmetricSubgroupAsymptotics.CFSGExceptionalCartanConnected
import SymmetricSubgroupAsymptotics.CFSGNormTwoRootPairingIrreducible
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateCartan
import SymmetricSubgroupAsymptotics.CFSGGeckSerreRepresentation

/-! Actual finite based reduced irreducible root pairings for the pinned E
tables, and their rational Serre representations. These definitions assert
no integral-image faithfulness or finite Chevalley-group recognition. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGExceptionalNormTwoBases
open CFSGNormTwoRootPairing CFSGExceptionalCartanPositiveDefinite
open CFSGExceptionalCartanConnected

instance rootsE6_fintype : Fintype (Roots CartanMatrix.E₆) := Fintype.ofFinite _
instance rootsE7_fintype : Fintype (Roots CartanMatrix.E₇) := Fintype.ofFinite _
instance rootsE8_fintype : Fintype (Roots CartanMatrix.E₈) := Fintype.ofFinite _
local instance rootsE6_decidableEq : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _
local instance rootsE7_decidableEq : DecidableEq (Roots CartanMatrix.E₇) := Classical.decEq _
local instance rootsE8_decidableEq : DecidableEq (Roots CartanMatrix.E₈) := Classical.decEq _

abbrev E6Pairing := rootPairing CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
abbrev E7Pairing := rootPairing CartanMatrix.E₇ CartanMatrix.E₇_transpose E7_positive_definite
abbrev E8Pairing := rootPairing CartanMatrix.E₈ CartanMatrix.E₈_transpose E8_positive_definite

instance E6_irreducible : E6Pairing.IsIrreducible :=
  rootPairing_isIrreducible_of_connected CartanMatrix.E₆ CartanMatrix.E₆_diag
    CartanMatrix.E₆_transpose E6_positive_definite E6_connected
instance E7_irreducible : E7Pairing.IsIrreducible :=
  rootPairing_isIrreducible_of_connected CartanMatrix.E₇ CartanMatrix.E₇_diag
    CartanMatrix.E₇_transpose E7_positive_definite E7_connected
instance E8_irreducible : E8Pairing.IsIrreducible :=
  rootPairing_isIrreducible_of_connected CartanMatrix.E₈ CartanMatrix.E₈_diag
    CartanMatrix.E₈_transpose E8_positive_definite E8_connected

def E6Base : E6Pairing.Base := coordinateBase CartanMatrix.E₆ CartanMatrix.E₆_diag
  CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos
def E7Base : E7Pairing.Base := coordinateBase CartanMatrix.E₇ CartanMatrix.E₇_diag
  CartanMatrix.E₇_transpose E7_positive_definite CartanMatrix.E₇_off_diag_nonpos
def E8Base : E8Pairing.Base := coordinateBase CartanMatrix.E₈ CartanMatrix.E₈_diag
  CartanMatrix.E₈_transpose E8_positive_definite CartanMatrix.E₈_off_diag_nonpos

def E6Index : Fin 6≃E6Base.support := coordinateIndexEquiv _ _ _ _ _
def E7Index : Fin 7≃E7Base.support := coordinateIndexEquiv _ _ _ _ _
def E8Index : Fin 8≃E8Base.support := coordinateIndexEquiv _ _ _ _ _

theorem E6_cartan : CFSGGeckSerreRepresentation.cartan E6Base E6Index=CartanMatrix.E₆ := by
  ext i j
  exact coordinate_cartan_transpose _ _ _ _ _ i j
theorem E7_cartan : CFSGGeckSerreRepresentation.cartan E7Base E7Index=CartanMatrix.E₇ := by
  ext i j
  exact coordinate_cartan_transpose _ _ _ _ _ i j
theorem E8_cartan : CFSGGeckSerreRepresentation.cartan E8Base E8Index=CartanMatrix.E₈ := by
  ext i j
  exact coordinate_cartan_transpose _ _ _ _ _ i j

private def transportRationalSource {d : ℕ} {A B : Matrix (Fin d) (Fin d) ℤ}
    {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    (h : A=B) (f : CFSG.Models.Chevalley.RationalLie A→ₗ⁅ℚ⁆L) :
    CFSG.Models.Chevalley.RationalLie B→ₗ⁅ℚ⁆L := by
  cases h
  exact f

def E6Representation : CFSG.Models.Chevalley.RationalLie CartanMatrix.E₆→ₗ⁅ℚ⁆
    CFSGGeckSerreRepresentation.Target E6Base :=
  transportRationalSource E6_cartan
    (CFSGGeckSerreRepresentation.rationalRepresentation E6Base E6Index)
def E7Representation : CFSG.Models.Chevalley.RationalLie CartanMatrix.E₇→ₗ⁅ℚ⁆
    CFSGGeckSerreRepresentation.Target E7Base :=
  transportRationalSource E7_cartan
    (CFSGGeckSerreRepresentation.rationalRepresentation E7Base E7Index)
def E8Representation : CFSG.Models.Chevalley.RationalLie CartanMatrix.E₈→ₗ⁅ℚ⁆
    CFSGGeckSerreRepresentation.Target E8Base :=
  transportRationalSource E8_cartan
    (CFSGGeckSerreRepresentation.rationalRepresentation E8Base E8Index)

end SymmetricSubgroupAsymptotics.CFSGExceptionalNormTwoBases
