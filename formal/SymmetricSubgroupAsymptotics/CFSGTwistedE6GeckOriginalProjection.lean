import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckProjectiveSylowOrder
import Mathlib.Tactic.Linarith

/-! Literal surjections from J and its SAME Derived action range to the
ORIGINAL twisted E6 model. The named positive Sylow restriction is
injective after the central quotient, by the proved disjoint Sylow pair. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalProjection
open CFSGTwistedE6GeckProjectiveSylowOrder CFSGTwistedE6GeckImagePositiveSylow
open CFSGTwistedE6GeckDerivedProjectiveImage CFSGTwistedE6GeckDerivedSylowNormalizer
open CFSGTwistedE6GeckRelativeRootGenerated CFSGTwistedE6OriginalGoodSylow
open CFSGTwistedE6FixedA2 CFSGSerreOrdinaryTwists
local instance (q : CFSG.PrimePower) : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
local instance (q : CFSG.PrimePower) : Finite (derivedImageAction q).range :=
  Finite.of_surjective (preimageToImage q) (preimageToImage_surjective q)

def imageToOriginal (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TwistedE6 q)] :
    (derivedImageAction q).range→*CFSG.Models.TwistedE6 q :=
  (originalProjectiveImageEquiv q).symm.toMonoidHom.comp
    (QuotientGroup.mk' (Subgroup.center (derivedImageAction q).range))

theorem imageToOriginal_surjective (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] : Function.Surjective (imageToOriginal q) :=
  (originalProjectiveImageEquiv q).symm.surjective.comp (QuotientGroup.mk'_surjective _)

theorem imageToOriginal_kernel (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] :
    (imageToOriginal q).ker=Subgroup.center (derivedImageAction q).range := by
  exact (MonoidHom.ker_mulEquiv_comp
    (QuotientGroup.mk' (Subgroup.center (derivedImageAction q).range))
    (originalProjectiveImageEquiv q).symm).trans (QuotientGroup.ker_mk' _)

def generatedToOriginal (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TwistedE6 q)] :
    fixedRootGenerated (q.Extension 2) (definingFieldAutomorphism q 2)→*CFSG.Models.TwistedE6 q :=
  (imageToOriginal q).comp (generatedToDerived q)

theorem generatedToOriginal_surjective (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] : Function.Surjective (generatedToOriginal q) :=
  (imageToOriginal_surjective q).comp (generatedToDerived_surjective q)

def positiveToOriginal (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TwistedE6 q)] :
    imagePositiveSylow q→*CFSG.Models.TwistedE6 q :=
  (imageToOriginal q).comp (imagePositiveSylow q : Subgroup (derivedImageAction q).range).subtype

theorem positiveToOriginal_injective (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] : Function.Injective (positiveToOriginal q) := by
  intro x y he
  apply CFSGDisjointSylowProjectiveOrder.quotient_center_sylow_injective
    (imagePositiveSylow q) (imageOppositeSylow q) (imageSylows_inf q)
  exact (originalProjectiveImageEquiv q).symm.injective he

def originalPositiveSylow (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TwistedE6 q)] :
    Sylow q.prime (CFSG.Models.TwistedE6 q) :=
  (imagePositiveSylow q).mapSurjective (f:=imageToOriginal q) (imageToOriginal_surjective q)

theorem originalPositiveSylow_card (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] :
    Nat.card (originalPositiveSylow q)=Nat.card (imagePositiveSylow q) := by
  change Nat.card ((imagePositiveSylow q : Subgroup (derivedImageAction q).range).map
    (imageToOriginal q))=Nat.card (imagePositiveSylow q)
  exact CFSGCentralKernelPElements.p_subgroup_card_map
    (imageToOriginal q) (imagePositiveSylow q) (positiveToOriginal_injective q)
    (le_of_eq (imageToOriginal_kernel q)) _ (imagePositiveSylow q).isPGroup'

theorem original_finite (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TwistedE6 q)] :
    Finite (CFSG.Models.TwistedE6 q) :=
  Finite.of_surjective (imageToOriginal q) (imageToOriginal_surjective q)

theorem originalPositiveSylow_ne_top (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] :
    (originalPositiveSylow q : Subgroup (CFSG.Models.TwistedE6 q))≠⊤ := by
  letI : Finite (CFSG.Models.TwistedE6 q) := original_finite q
  intro htop
  have hc : Nat.card (imagePositiveSylow q)=Nat.card (CFSG.Models.TwistedE6 q) := by
    rw [←originalPositiveSylow_card]
    change Nat.card (originalPositiveSylow q : Subgroup (CFSG.Models.TwistedE6 q))=_
    rw [htop,Subgroup.card_top]
  have hs := original_positive_sylow_square_lt_order q
  rw [hc] at hs
  have hpos := Nat.card_pos (α:=CFSG.Models.TwistedE6 q)
  nlinarith

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalProjection
