import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalOppositeAlignment
import SymmetricSubgroupAsymptotics.CFSGOppositeSylowOfAlignment

/-! Every automorphism of the SAME original simple twisted E6 group
can be adjusted by an actual inner automorphism to preserve its literal
positive and negative subgroups. The fixed negative target is proved
Sylow from the actual alignment, rather than assumed to be so. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalPairAlignment
open CFSGTwistedE6GeckOriginalOppositeAlignment CFSGTwistedE6GeckOriginalProjection
open CFSGTwistedE6GeckProjectiveSylowOrder CFSGTwistedE6GeckImagePositiveSylow
open CFSGTwistedE6GeckDerivedSylowNormalizer CFSGTwistedE6OriginalGoodSylow
open CFSGTwistedE6FixedA2 CFSGSerreOrdinaryTwists CFSGTwistedE6GeckRelativeRootGenerated
open CFSGTwistedE6GeckRootGeneratedPGroup
local instance (q : CFSG.PrimePower) : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
local instance (q : CFSG.PrimePower) : Finite (derivedImageAction q).range :=
  Finite.of_surjective (preimageToImage q) (preimageToImage_surjective q)
local instance (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TwistedE6 q)] :
    Finite (CFSG.Models.TwistedE6 q) := original_finite q

def originalOppositeSylow (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TwistedE6 q)] :
    Sylow q.prime (CFSG.Models.TwistedE6 q) :=
  (imageOppositeSylow q).mapSurjective (f:=imageToOriginal q) (imageToOriginal_surjective q)

theorem original_opposite_sylows_disjoint (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] :
    (originalPositiveSylow q : Subgroup (CFSG.Models.TwistedE6 q))⊓
      (originalOppositeSylow q : Subgroup (CFSG.Models.TwistedE6 q))=⊥ := by
  change ((imagePositiveSylow q : Subgroup (derivedImageAction q).range).map (imageToOriginal q))⊓
    ((imageOppositeSylow q : Subgroup (derivedImageAction q).range).map (imageToOriginal q))=⊥
  exact CFSGCentralKernelPElements.disjoint_map (imageToOriginal q) (imagePositiveSylow q)
    (positiveToOriginal_injective q) (le_of_eq (imageToOriginal_kernel q))
    (imagePositiveSylow q : Subgroup (derivedImageAction q).range)
    (imageOppositeSylow q : Subgroup (derivedImageAction q).range)
    (imagePositiveSylow q).isPGroup' (imageOppositeSylow q).isPGroup' (imageSylows_inf q)

theorem original_negative_is_sylow (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] :
    ∃S : Sylow q.prime (CFSG.Models.TwistedE6 q),
      (S : Subgroup (CFSG.Models.TwistedE6 q))=originalNegative q ∧
      (originalPositiveSylow q : Subgroup (CFSG.Models.TwistedE6 q))⊓
        (S : Subgroup (CFSG.Models.TwistedE6 q))=⊥ :=
  CFSGOppositeSylowOfAlignment.exists_negative_sylow (originalPositiveSylow q)
    (originalOppositeSylow q) (originalNegative q) (original_opposite_sylows_disjoint q)
    (original_opposite_conjugate_by_positive q)

theorem original_exists_inner_fix_pair (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (f : MulAut (CFSG.Models.TwistedE6 q)) :
    ∃g : CFSG.Models.TwistedE6 q,
      (originalPositiveSylow q : Subgroup (CFSG.Models.TwistedE6 q)).map
        (MulAut.conj g*f).toMonoidHom=(originalPositiveSylow q : Subgroup (CFSG.Models.TwistedE6 q)) ∧
      (originalNegative q).map (MulAut.conj g*f).toMonoidHom=originalNegative q :=
  CFSGOppositeSylowOfAlignment.exists_inner_fix_pair (originalPositiveSylow q)
    (originalOppositeSylow q) (originalNegative q) (original_opposite_sylows_disjoint q)
    (original_opposite_conjugate_by_positive q) f

theorem signedFixedToOriginal_range (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (neg : Bool) :
    (signedFixedToOriginal q neg).range=
      (rootPart (q.Extension 2) (definingFieldAutomorphism q 2) neg).map (generatedToOriginal q) := by
  ext x
  constructor
  · rintro ⟨u,rfl⟩
    exact ⟨signedFixedToGenerated q neg u,u.property,rfl⟩
  · rintro ⟨u,hu,rfl⟩
    exact ⟨⟨u.val,hu⟩,rfl⟩

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalPairAlignment
