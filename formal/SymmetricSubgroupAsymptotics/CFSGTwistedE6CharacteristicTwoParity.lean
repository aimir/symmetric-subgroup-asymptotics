import SymmetricSubgroupAsymptotics.CFSGTwistedE6CharTwoDerivedImages
import SymmetricSubgroupAsymptotics.CFSGQuadraticConjugationImageParity
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckNoncentralMatrix
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylUnits
import SymmetricSubgroupAsymptotics.CFSGSimpleProjectiveDescent

/-! Genuine even order for the ORIGINAL simple twisted E6 model in
characteristic two. The two root witnesses are actual preimages in the
literal derived fixed subgroup, obtained by commutator-image equality. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6FixedA2
open CFSG.Models.Chevalley CFSGSerreQuadraticMatrix CFSGExceptionalGeckIntegralData
open CFSGExceptionalNormTwoBases CFSGNormTwoRootPairing CFSGExceptionalCartanPositiveDefinite
local instance twistedE6CharTwoParityDecEq : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _

def charTwoDerivedWeyl (q : CFSG.PrimePower) [CharP (q.Extension 2) 2] : Derived q :=
  charTwoDerivedRootLift q false*(charTwoDerivedRootLift q true)⁻¹*charTwoDerivedRootLift q false

private theorem naturalRoot_inverse (q : CFSG.PrimePower) (neg : Bool) (i : Fin 2)
    (t : q.Extension 2) : (naturalRoot q neg i t)⁻¹=naturalRoot q neg i (-t) := by
  apply Subtype.ext
  exact canonicalRoot_inverse E6Data (q.Extension 2) neg (node i) t

theorem charTwoDerivedWeyl_image (q : CFSG.PrimePower) [CharP (q.Extension 2) 2] :
    derivedImageAction q (charTwoDerivedWeyl q)=canonicalAction q (naturalWeyl q 1) := by
  simp only [charTwoDerivedWeyl,map_mul,map_inv,charTwoDerivedRoot_image q,imageAction_root_eq_canonical]
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

private theorem charTwoDerivedWeyl_action (q : CFSG.PrimePower) [CharP (q.Extension 2) 2]
    (y : (baseChange E6Data (q.Extension 2)).range) :
    (derivedImageAction q (charTwoDerivedWeyl q) y).val=
      (canonicalWeyl E6Data (q.Extension 2) 3 : Matrix
        (E6Base.support⊕Roots CartanMatrix.E₆) (E6Base.support⊕Roots CartanMatrix.E₆) (q.Extension 2))*y.val*
      (↑((canonicalWeyl E6Data (q.Extension 2) 3)⁻¹) : Matrix
        (E6Base.support⊕Roots CartanMatrix.E₆) (E6Base.support⊕Roots CartanMatrix.E₆) (q.Extension 2)) := by
  rw [charTwoDerivedWeyl_image q]
  rfl

private theorem derivedRoot_action (q : CFSG.PrimePower) [CharP (q.Extension 2) 2]
    (y : (baseChange E6Data (q.Extension 2)).range) :
    (derivedImageAction q (charTwoDerivedRootLift q false) y).val=
      (canonicalRoot E6Data (q.Extension 2) false 3 1 : Matrix
        (E6Base.support⊕Roots CartanMatrix.E₆) (E6Base.support⊕Roots CartanMatrix.E₆) (q.Extension 2))*y.val*
      (↑((canonicalRoot E6Data (q.Extension 2) false 3 1)⁻¹) : Matrix
        (E6Base.support⊕Roots CartanMatrix.E₆) (E6Base.support⊕Roots CartanMatrix.E₆) (q.Extension 2)) := by
  rw [charTwoDerivedRoot_image q,imageAction_root_eq_canonical]
  rfl

theorem twistedE6_even_card_of_characteristic_two (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] [CharP (q.Extension 2) 2] :
    Even (Nat.card (CFSG.Models.TwistedE6 q)) := by
  let f := derivedImageAction q
  let u := charTwoDerivedWeyl q
  let v := charTwoDerivedRootLift q false
  have hnot := CFSGQuadraticConjugationImageParity.image_word_not_center E6Data (q.Extension 2)
    f u v 3 (charTwoDerivedWeyl_action q) (derivedRoot_action q) (long_four q) (long_noncommuting q)
  let Q := QuotientGroup.mk' (Subgroup.center f.range)
  have hne : Q (f.rangeRestrict u)≠1 := by
    intro h
    exact hnot ((QuotientGroup.eq_one_iff _).mp h)
  letI : Nontrivial (f.range⧸Subgroup.center f.range) := ⟨⟨Q (f.rangeRestrict u),1,hne⟩⟩
  let e := CFSGSimpleProjectiveDescent.projectiveEquivOfSimple f.rangeRestrict f.rangeRestrict_surjective
  change Even (Nat.card (Derived q⧸Subgroup.center (Derived q)))
  rw [Nat.card_congr e.toEquiv]
  exact CFSGQuadraticConjugationImageParity.image_projective_even_card E6Data (q.Extension 2)
    f u v 3 (charTwoDerivedWeyl_action q) (derivedRoot_action q) (long_four q) (long_noncommuting q)

end SymmetricSubgroupAsymptotics.CFSGTwistedE6FixedA2
