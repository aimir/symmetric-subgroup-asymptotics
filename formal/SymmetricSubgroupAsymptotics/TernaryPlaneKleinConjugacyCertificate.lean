import SymmetricSubgroupAsymptotics.TernaryPlaneKleinPair

/-!
# Finite conjugacy certificate for ternary Klein pairs

This module contains only the finite search carrying a displayed
independent commuting involution pair in `GL₂(3)` to the standard diagonal
Klein four.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace LinearThree

/-- The finite search is stated entirely as equality of four-element
`Finset`s, so its decision procedure never unfolds subgroup closure or a
classical finite instance. -/
set_option maxRecDepth 100000 in
theorem pair_conjugate_standardKleinFinset_certificate :
    ∀ a b : GL3,
      a ≠ 1 → b ≠ 1 → a ≠ b →
      a ^ 2 = 1 → b ^ 2 = 1 → a * b = b * a →
      ∃ g : GL3,
        conjugatedKleinFourElements a b g =
          kleinFourElements
            (DegreeSixS3Wreath.standardKleinLinearMap kleinFirstBit)
            (DegreeSixS3Wreath.standardKleinLinearMap kleinSecondBit) := by
  decide +kernel

/-- Structural bridge from the finite four-element certificate to the
actual generated subgroups. -/
theorem pair_conjugate_standardKlein_certificate
    (a b : GL3)
    (ha : a ≠ 1) (hb : b ≠ 1) (hab : a ≠ b)
    (ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = 1)
    (hcomm : a * b = b * a) :
    ∃ g : GL3,
      (kleinPairSubgroup a b).map (MulAut.conj g).toMonoidHom =
        DegreeSixS3Wreath.standardKleinLinearMap.range := by
  obtain ⟨g, hg⟩ := pair_conjugate_standardKleinFinset_certificate
    a b ha hb hab ha2 hb2 hcomm
  refine ⟨g, ?_⟩
  let f := DegreeSixS3Wreath.standardKleinLinearMap
  have hf2a : (f kleinFirstBit) ^ 2 = 1 :=
    map_kleinFirstBit_square f
  have hf2b : (f kleinSecondBit) ^ 2 = 1 :=
    map_kleinSecondBit_square f
  have hfcomm : f kleinFirstBit * f kleinSecondBit =
      f kleinSecondBit * f kleinFirstBit :=
    map_kleinBits_commute f
  rw [kleinPairSubgroup_eq_kleinFourSubgroup a b ha2 hb2 hcomm,
    binaryKleinRange_eq_pairSubgroup f
      DegreeSixS3Wreath.standardKleinLinearMap_injective,
    kleinPairSubgroup_eq_kleinFourSubgroup
      (f kleinFirstBit) (f kleinSecondBit) hf2a hf2b hfcomm]
  exact map_kleinFourSubgroup_eq_of_conjugated_elements_eq
    a b (f kleinFirstBit) (f kleinSecondBit) g
    ha2 hb2 hcomm hf2a hf2b hfcomm hg

end LinearThree
end SymmetricSubgroupAsymptotics

end
