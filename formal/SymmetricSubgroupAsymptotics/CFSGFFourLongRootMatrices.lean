import SymmetricSubgroupAsymptotics.CFSGFFourIntegralRealization
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckNoncentralMatrix
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylUnits

/-! Long F4 node 2 has exactly the original E6 node-3 root polynomial.
Its fourth-root and noncentrality identities are transferred by literal
matrix equality, with no group-identification premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourSerreMatrices
open CFSGNormTwoRootPairing CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGSerreQuadraticMatrix
local instance fFourLongRootMatricesDecEq : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _

abbrev e6RealizationData := CFSGNormTwoGeckIntegralRealization.realizationData
  CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index

theorem long_fieldRoot (K : Type*) [CommRing K] (neg : Bool) :
    fieldRoot realizationData K neg 2=fieldRoot e6RealizationData K neg 3 := by
  cases neg <;> rfl

theorem long_fieldSecond (K : Type*) [CommRing K] (neg : Bool) :
    fieldSecond realizationData K neg 2=fieldSecond e6RealizationData K neg 3 := by
  cases neg <;> rfl

theorem canonical_long_root (K : Type*) [CommRing K] (neg : Bool) (t : K) :
    canonicalRoot realizationData K neg 2 t=canonicalRoot e6RealizationData K neg 3 t := by
  apply Units.ext
  rw [canonicalRoot_val,canonicalRoot_val,long_fieldRoot,long_fieldSecond]

theorem canonical_long_weyl (K : Type*) [CommRing K] :
    canonicalWeyl realizationData K 2=canonicalWeyl e6RealizationData K 3 := by
  simp only [canonicalWeyl,canonical_long_root]

theorem long_weyl_four (K : Type*) [CommRing K] :
    (canonicalWeyl realizationData K 2)^4=1 := by
  rw [canonical_long_weyl]
  exact CFSGNormTwoGeckWeylUnits.weyl_four CartanMatrix.E₆ CartanMatrix.E₆_transpose
    E6_positive_definite E6Base E6Index K 3

theorem long_root_does_not_fix_weyl_root (K : Type) [Field K] :
    (canonicalRoot realizationData K false 2 1 : Matrix Index Index K)*
      ((canonicalWeyl realizationData K 2 : Matrix Index Index K)*fieldRoot realizationData K false 2*
        (↑((canonicalWeyl realizationData K 2)⁻¹):Matrix Index Index K))*
      (↑((canonicalRoot realizationData K false 2 1)⁻¹):Matrix Index Index K)≠
    (canonicalWeyl realizationData K 2 : Matrix Index Index K)*fieldRoot realizationData K false 2*
      (↑((canonicalWeyl realizationData K 2)⁻¹):Matrix Index Index K) := by
  rw [canonical_long_root,canonical_long_weyl,long_fieldRoot]
  exact CFSGNormTwoGeckNoncentralMatrix.root_does_not_fix_weyl_root CartanMatrix.E₆
    CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K 3

end SymmetricSubgroupAsymptotics.CFSGFFourSerreMatrices
