import SymmetricSubgroupAsymptotics.CFSGTwistedE6DerivedRootImages
import SymmetricSubgroupAsymptotics.CFSGQuadraticConjugationImageParity
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckNoncentralMatrix
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylUnits
import SymmetricSubgroupAsymptotics.CFSGSimpleProjectiveDescent

/-! Genuine even order for the ORIGINAL simple twisted E6 model when 2 is
nonzero. The Weyl/root witnesses are actual commutator words in its
literal derived fixed subgroup. The characteristic-two case stays open. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6FixedA2
open CFSG.Models.Chevalley CFSGSerreQuadraticMatrix CFSGExceptionalGeckIntegralData
open CFSGExceptionalNormTwoBases CFSGNormTwoRootPairing CFSGExceptionalCartanPositiveDefinite
local instance twistedE6OddParityDecEq : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _

def derivedWeyl (q : CFSG.PrimePower) : Derived q :=
  derivedRootLift q false*(derivedRootLift q true)⁻¹*derivedRootLift q false

private theorem naturalRoot_inverse (q : CFSG.PrimePower) (neg : Bool) (i : Fin 2)
    (t : q.Extension 2) : (naturalRoot q neg i t)⁻¹=naturalRoot q neg i (-t) := by
  apply Subtype.ext
  exact canonicalRoot_inverse E6Data (q.Extension 2) neg (node i) t

theorem derivedWeyl_image (q : CFSG.PrimePower) (h2 : (2:q.Extension 2)≠0) :
    derivedImageAction q (derivedWeyl q)=canonicalAction q (naturalWeyl q 1) := by
  simp only [derivedWeyl,map_mul,map_inv,derivedRoot_image q h2,imageAction_root_eq_canonical]
  rw [←map_inv,naturalRoot_inverse]
  simp only [naturalWeyl,map_mul]

private theorem long_four (q : CFSG.PrimePower) :
    (canonicalWeyl E6Data (q.Extension 2) 3)^4=1 := by
  rw [E6Data,canonicalWeyl_transportSource]
  exact CFSGNormTwoGeckWeylUnits.weyl_four CartanMatrix.E₆ CartanMatrix.E₆_transpose
    E6_positive_definite E6Base E6Index (q.Extension 2) 3

private theorem long_noncommuting (q : CFSG.PrimePower) :
    (canonicalRoot E6Data (q.Extension 2) false 3 1 : Matrix
      (E6Base.support⊕Roots CartanMatrix.E₆) (E6Base.support⊕Roots CartanMatrix.E₆) (q.Extension 2))*
      ((canonicalWeyl E6Data (q.Extension 2) 3 : Matrix
        (E6Base.support⊕Roots CartanMatrix.E₆) (E6Base.support⊕Roots CartanMatrix.E₆) (q.Extension 2))*
      fieldRoot E6Data (q.Extension 2) false 3*
      (↑((canonicalWeyl E6Data (q.Extension 2) 3)⁻¹) : Matrix
        (E6Base.support⊕Roots CartanMatrix.E₆) (E6Base.support⊕Roots CartanMatrix.E₆) (q.Extension 2)))*
      (↑((canonicalRoot E6Data (q.Extension 2) false 3 1)⁻¹) : Matrix
        (E6Base.support⊕Roots CartanMatrix.E₆) (E6Base.support⊕Roots CartanMatrix.E₆) (q.Extension 2))≠
    (canonicalWeyl E6Data (q.Extension 2) 3 : Matrix
      (E6Base.support⊕Roots CartanMatrix.E₆) (E6Base.support⊕Roots CartanMatrix.E₆) (q.Extension 2))*
      fieldRoot E6Data (q.Extension 2) false 3*
      (↑((canonicalWeyl E6Data (q.Extension 2) 3)⁻¹) : Matrix
        (E6Base.support⊕Roots CartanMatrix.E₆) (E6Base.support⊕Roots CartanMatrix.E₆) (q.Extension 2)) := by
  simpa only [E6Data,canonicalRoot_transportSource,canonicalWeyl_transportSource,
    fieldRoot_transportSource] using CFSGNormTwoGeckNoncentralMatrix.root_does_not_fix_weyl_root
      CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index (q.Extension 2) 3

private theorem derivedWeyl_action (q : CFSG.PrimePower) (h2 : (2:q.Extension 2)≠0)
    (y : (baseChange E6Data (q.Extension 2)).range) :
    (derivedImageAction q (derivedWeyl q) y).val=
      (canonicalWeyl E6Data (q.Extension 2) 3 : Matrix
        (E6Base.support⊕Roots CartanMatrix.E₆) (E6Base.support⊕Roots CartanMatrix.E₆) (q.Extension 2))*y.val*
      (↑((canonicalWeyl E6Data (q.Extension 2) 3)⁻¹) : Matrix
        (E6Base.support⊕Roots CartanMatrix.E₆) (E6Base.support⊕Roots CartanMatrix.E₆) (q.Extension 2)) := by
  rw [derivedWeyl_image q h2]
  rfl

private theorem derivedRoot_action (q : CFSG.PrimePower) (h2 : (2:q.Extension 2)≠0)
    (y : (baseChange E6Data (q.Extension 2)).range) :
    (derivedImageAction q (derivedRootLift q false) y).val=
      (canonicalRoot E6Data (q.Extension 2) false 3 1 : Matrix
        (E6Base.support⊕Roots CartanMatrix.E₆) (E6Base.support⊕Roots CartanMatrix.E₆) (q.Extension 2))*y.val*
      (↑((canonicalRoot E6Data (q.Extension 2) false 3 1)⁻¹) : Matrix
        (E6Base.support⊕Roots CartanMatrix.E₆) (E6Base.support⊕Roots CartanMatrix.E₆) (q.Extension 2)) := by
  rw [derivedRoot_image q h2,imageAction_root_eq_canonical]
  rfl

theorem twistedE6_even_card_of_two_ne_zero (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (h2 : (2:q.Extension 2)≠0) :
    Even (Nat.card (CFSG.Models.TwistedE6 q)) := by
  let f := derivedImageAction q
  let u := derivedWeyl q
  let v := derivedRootLift q false
  have hnot := CFSGQuadraticConjugationImageParity.image_word_not_center E6Data (q.Extension 2)
    f u v 3 (derivedWeyl_action q h2) (derivedRoot_action q h2) (long_four q) (long_noncommuting q)
  let Q := QuotientGroup.mk' (Subgroup.center f.range)
  have hne : Q (f.rangeRestrict u)≠1 := by
    intro h
    exact hnot ((QuotientGroup.eq_one_iff _).mp h)
  letI : Nontrivial (f.range⧸Subgroup.center f.range) := ⟨⟨Q (f.rangeRestrict u),1,hne⟩⟩
  let e := CFSGSimpleProjectiveDescent.projectiveEquivOfSimple f.rangeRestrict f.rangeRestrict_surjective
  change Even (Nat.card (Derived q⧸Subgroup.center (Derived q)))
  rw [Nat.card_congr e.toEquiv]
  exact CFSGQuadraticConjugationImageParity.image_projective_even_card E6Data (q.Extension 2)
    f u v 3 (derivedWeyl_action q h2) (derivedRoot_action q h2) (long_four q) (long_noncommuting q)

end SymmetricSubgroupAsymptotics.CFSGTwistedE6FixedA2
