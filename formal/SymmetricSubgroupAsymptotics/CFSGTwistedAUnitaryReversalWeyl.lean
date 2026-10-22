import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryReversalDeterminant
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryFixedRadicalGroup

/-! The actual signed reversal is an element of the SAME natural and
original defining-fixed groups. It is determinant one and its fixed
equation is proved from its actual signed transpose/inverse formulas.
No membership in the derived group or two-Sylow generation is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGSerreOrdinaryTwists

def reversalNatural (q : CFSG.PrimePower) (r : ℕ) : NaturalElementary (q.Extension 2) r :=
  ⟨signedReversalUnit (q.Extension 2) r,
    unit_mem_natural_of_det (q.Extension 2) r _ (signedReversalUnit_det (q.Extension 2) r)⟩

theorem signedReversalUnit_fixed (q : CFSG.PrimePower) (r : ℕ) :
    diagramFieldUnitHom (q.Extension 2) r (definingFieldAutomorphism q 2).toRingHom
      (signedReversalUnit (q.Extension 2) r) = signedReversalUnit (q.Extension 2) r := by
  apply unit_fixed_of_isometric (q.Extension 2) r (definingFieldAutomorphism q 2).toRingHom
  rw [map_signedReversalUnit_val]
  have ht : (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r).transpose =
      (↑((signedReversalUnit (q.Extension 2) r)⁻¹) : Mat (q.Extension 2) r) := by
    rw [signedReversalUnit_transpose, signedReversalUnit_inv_parity]
  rw [ht, mul_assoc, Units.inv_mul, mul_one]

def reversalFixed (q : CFSG.PrimePower) (r : ℕ) : naturalFixed r q :=
  ⟨reversalNatural q r, signedReversalUnit_fixed q r⟩

def originalReversal (q : CFSG.PrimePower) (r : ℕ) : Fixed r q :=
  naturalFixedToOriginal q r (reversalFixed q r)

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
