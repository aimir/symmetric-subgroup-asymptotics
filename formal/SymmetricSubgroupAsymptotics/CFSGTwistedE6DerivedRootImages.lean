import SymmetricSubgroupAsymptotics.CFSGTwistedE6A2CanonicalAction
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckAdjacentWeylConjugacy
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOrthogonalColumns
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticCanonicalTransport
import SymmetricSubgroupAsymptotics.CFSGQuadraticWeylDerivedRoot

/-! Explicit actual commutators in the DERIVED pinned fixed subgroup.
When 2 is nonzero their original E6 image is the fixed long root at 1.
Characteristic two is intentionally not covered by this calculation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6FixedA2
open CFSG.Models.Chevalley CFSGSerreQuadraticMatrix CFSGExceptionalGeckIntegralData
open CFSGExceptionalNormTwoBases CFSGNormTwoRootPairing CFSGExceptionalCartanPositiveDefinite
open CFSGSerreOrdinaryTwists
local instance twistedE6DerivedRootImagesDecEq : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _

def halfParameter (q : CFSG.PrimePower) : q.Extension 2 := -(2:q.Extension 2)⁻¹

theorem halfParameter_fixed (q : CFSG.PrimePower) :
    definingFieldAutomorphism q 2 (halfParameter q)=halfParameter q := by
  simp only [halfParameter,map_neg,map_inv₀,map_ofNat]

def derivedRootLift (q : CFSG.PrimePower) (neg : Bool) : Derived q :=
  CFSGSerreFixedRootElements.derivedCommutator CartanMatrix.E₆ (q.Extension 2)
    CFSG.Models.e6Twist (fun _=>q.order) ((weyl q 0)^2)
    (root q neg 1 (halfParameter q) (halfParameter_fixed q))

def derivedImageAction (q : CFSG.PrimePower) :=
  (imageRepresentation E6Data (q.Extension 2)).comp (derivedToOriginal q)

private theorem adjacent_pairing :
    CFSGIntegerMatrixPairing.integerPairing CartanMatrix.E₆
      (E6Index 1:Roots CartanMatrix.E₆).val (E6Index 3:Roots CartanMatrix.E₆).val= -1 := by
  rw [CFSGNormTwoGeckOrthogonalColumns.integerPairing_eq_cartan]
  have hh := congrFun (congrFun E6_cartan 3) 1
  change E6Base.cartanMatrix (E6Index 1) (E6Index 3)=CartanMatrix.E₆ 3 1 at hh
  exact hh.trans (by decide)

private theorem adjacent_rational_sign (neg : Bool) :
    (canonicalWeyl E6Data ℚ 1 : Matrix (E6Base.support⊕Roots CartanMatrix.E₆)
      (E6Base.support⊕Roots CartanMatrix.E₆) ℚ)^2*fieldRoot E6Data ℚ neg 3=
    -(fieldRoot E6Data ℚ neg 3*(canonicalWeyl E6Data ℚ 1 : Matrix
      (E6Base.support⊕Roots CartanMatrix.E₆) (E6Base.support⊕Roots CartanMatrix.E₆) ℚ)^2) := by
  simpa only [E6Data,canonicalWeyl_transportSource,fieldRoot_transportSource] using
    CFSGNormTwoGeckAdjacentWeylConjugacy.rational_adjacent_sign CartanMatrix.E₆
      CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index 1 3 adjacent_pairing neg

theorem natural_derived_root_word (q : CFSG.PrimePower) (h2 : (2:q.Extension 2)≠0) (neg : Bool) :
    ⁅(naturalWeyl q 0)^2,naturalRoot q neg 1 (halfParameter q)⁆=naturalRoot q neg 1 1 := by
  apply Subtype.ext
  change ⁅(canonicalWeyl E6Data (q.Extension 2) 1)^2,
      canonicalRoot E6Data (q.Extension 2) neg 3 (halfParameter q)⁆=
    canonicalRoot E6Data (q.Extension 2) neg 3 1
  have hh := canonical_weyl_square_commutator E6Data 1 3 neg (adjacent_rational_sign neg)
    (q.Extension 2) (halfParameter q)
  have hp : -(2*halfParameter q)=1 := by
    dsimp only [halfParameter]
    field_simp [h2]
  simpa only [hp] using hh

theorem derivedRoot_image (q : CFSG.PrimePower) (h2 : (2:q.Extension 2)≠0) (neg : Bool) :
    derivedImageAction q (derivedRootLift q neg)=imageAction q (root q neg 1 1 (one_fixed q)) := by
  change imageAction q
      ⁅(weyl q 0)^2,root q neg 1 (halfParameter q) (halfParameter_fixed q)⁆=_
  rw [map_commutatorElement,map_pow,imageAction_weyl_eq_canonical,
    imageAction_root_eq_canonical,imageAction_root_eq_canonical]
  rw [←map_pow,←map_commutatorElement,natural_derived_root_word q h2 neg]

end SymmetricSubgroupAsymptotics.CFSGTwistedE6FixedA2
