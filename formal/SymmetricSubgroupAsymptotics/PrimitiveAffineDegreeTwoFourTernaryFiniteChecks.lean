import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoFourTernaryFiniteWitnessData
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoFourTernaryClosure

/-!
# Checked finite payload for the eight four-ternary degree-two tops

Every field below is a closed computation in one of the eight literal
permutation groups.  The shared structural theorem handles arbitrary pair
lifts and arbitrary normal subgroups; this file only certifies the finite
top/core data used by that theorem.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

/-- All eight literal top/core witnesses, discharged by kernel evaluation. -/
noncomputable def degreeTwoFourTernaryFiniteChecks :
    DegreeTwoFourTernaryFiniteChecks where
  membership :=
    { mem := by
        intro r j
        fin_cases r <;> fin_cases j <;> native_decide }
  core_normal := by
    intro r
    fin_cases r <;> native_decide
  core_commutative := by
    intro r
    fin_cases r <;> exact ⟨by native_decide⟩
  core_exponent_three := by
    intro r
    fin_cases r <;> native_decide
  top_card := by
    intro r
    fin_cases r <;> native_decide
  core_card := by
    intro r
    fin_cases r <;> native_decide
  top_transitive := by
    intro r
    fin_cases r <;> native_decide
  exact_orbits := by
    intro r
    fin_cases r <;> native_decide
  quotient_binary := by
    intro r
    fin_cases r <;> native_decide
  centralizer_quotient_card := by
    intro r
    fin_cases r <;> native_decide

/-- The assembled catalogue witnesses consumed by the uniform theorem. -/
noncomputable def degreeTwoFourTernaryCatalogueWitnesses :
    DegreeTwoFourTernaryCatalogueWitnesses :=
  degreeTwoFourTernaryFiniteChecks.catalogueWitnesses

/-- The eight concrete compression packages used by the literal
count-twelve catalogue. -/
noncomputable def degreeTwoFourTernaryCompressionPackages :
    ∀ r : Fin 8,
      DegreeTwoTwelveFourTernaryCompressionPackage
        (degreeTwoFourTernaryInterface r) :=
  degreeTwoFourTernaryCatalogueWitnesses.compressionPackages

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
