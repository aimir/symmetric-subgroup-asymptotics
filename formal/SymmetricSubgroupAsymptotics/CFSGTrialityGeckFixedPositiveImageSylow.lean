import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedPositiveCardinality
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckDerivedSylowNormalizer
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckPositiveActionInjective

/-! The SAME original Derived action range has an actual Sylow whose
cardinality is q^12. The fixed-positive chart is transported through the
proved preimage Sylow and its actual action; no faithful Lie source is
assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedPositiveImageSylow
open CFSGTrialityGeckFixedPositiveGeneration CFSGTrialityGeckFixedPositiveCardinality
open CFSGTrialityGeckFixedPositiveSylow CFSGTrialityGeckDerivedSylowNormalizer
open CFSGTrialityGeckFixedDerivedMatrixLift CFSGTrialityGeckLongDerivedImage
open CFSGTrialityGeckSourceWordAction CFSGTrialityGeckPositiveTwist
open CFSGTrialityGeckPositiveActionInjective CFSGSerreOrdinaryTwists
open CFSGTrialityGeckMatrixGroupTwist

local instance (q : CFSG.PrimePower) : Fact q.prime.Prime := ⟨q.prime_isPrime⟩

abbrev DerivedImage (q : CFSG.PrimePower) := (derivedImageAction q).range

private def fixedInclusionEquiv {G : Type*} [Group G] (A B : Subgroup G) (hAB : A ≤ B)
    (F : MulAut A) (T : MulAut B)
    (hcov : ∀ a : A,(T ⟨a.val,hAB a.property⟩).val = (F a).val) :
    ((A.subgroupOf B).subgroupOf (CFSGCentralTwistedCommutatorLift.fixedSubgroup T)) ≃*
      CFSGCentralTwistedCommutatorLift.fixedSubgroup F where
  toFun u := by
    let a : A := ⟨u.val.val.val,u.property⟩
    refine ⟨a,?_⟩
    have hb : T u.val.val = u.val.val := u.val.property
    apply Subtype.ext
    exact (hcov a).symm.trans (congrArg (fun b : B => b.val) hb)
  invFun a := by
    let b : B := ⟨a.val.val,hAB a.val.property⟩
    refine ⟨⟨b,?_⟩,a.val.property⟩
    have ha : F a.val = a.val := a.property
    apply Subtype.ext
    exact (hcov a.val).trans (congrArg (fun x : A => x.val) ha)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

def upperEquivFixedPositive (q : CFSG.PrimePower) :
    FixedUpper (q.Extension 3) (definingFieldAutomorphism q 3) ≃*
      fixedPositive (q.Extension 3) (definingFieldAutomorphism q 3) :=
  fixedInclusionEquiv (Positive (q.Extension 3)) (MatrixGroup (q.Extension 3))
    (CFSGTrialityGeckAmbientPositiveSylow.positive_le_matrixGroup (q.Extension 3))
    (positiveTwist (q.Extension 3) (definingFieldAutomorphism q 3))
    (matrixGroupTwist (q.Extension 3) (definingFieldAutomorphism q 3)) (fun _ => rfl)

def preimagePositiveEquiv (q : CFSG.PrimePower) :
    preimageSylow q ≃* fixedPositive (q.Extension 3) (definingFieldAutomorphism q 3) :=
  (Subgroup.subgroupOfEquivOfLe (fixed_upper_le_preimage q)).trans (upperEquivFixedPositive q)

theorem preimagePositiveEquiv_action (q : CFSG.PrimePower) (u : preimageSylow q) :
    (preimageToImage q u.val).val = positiveAction (q.Extension 3) (preimagePositiveEquiv q u).val := rfl

theorem preimage_sylow_action_injective (q : CFSG.PrimePower) :
    Function.Injective ((preimageToImage q).comp (preimageSylow q : Subgroup (naturalDerivedPreimage q)).subtype) := by
  intro u v he
  apply (preimagePositiveEquiv q).injective
  apply Subtype.ext
  apply positiveAction_injective (q.Extension 3) q.prime
  have hv : (preimageToImage q u.val).val = (preimageToImage q v.val).val :=
    congrArg (fun x : DerivedImage q => x.val) he
  exact (preimagePositiveEquiv_action q u).symm.trans
    (hv.trans (preimagePositiveEquiv_action q v))

def imagePositiveSylow (q : CFSG.PrimePower) : Sylow q.prime (DerivedImage q) :=
  (preimageSylow q).mapSurjective (preimageToImage_surjective q)

theorem imagePositiveSylow_range (q : CFSG.PrimePower) :
    (imagePositiveSylow q : Subgroup (DerivedImage q)) =
      ((preimageToImage q).comp (preimageSylow q : Subgroup (naturalDerivedPreimage q)).subtype).range := by
  rw [MonoidHom.range_comp,Subgroup.range_subtype]
  rfl

theorem imagePositiveSylow_card (q : CFSG.PrimePower) :
    Nat.card (imagePositiveSylow q) = q.order ^ 12 := by
  rw [show Nat.card (imagePositiveSylow q) = Nat.card
    ((preimageToImage q).comp (preimageSylow q : Subgroup (naturalDerivedPreimage q)).subtype).range from
      Nat.card_congr (MulEquiv.subgroupCongr (imagePositiveSylow_range q)).toEquiv]
  rw [←Nat.card_congr (MonoidHom.ofInjective (preimage_sylow_action_injective q)).toEquiv,
    Nat.card_congr (preimagePositiveEquiv q).toEquiv]
  exact fixedPositive_card q

theorem exists_positive_lift (q : CFSG.PrimePower) (a : imagePositiveSylow q) :
    ∃ u : fixedPositive (q.Extension 3) (definingFieldAutomorphism q 3),
      positiveAction (q.Extension 3) u.val = a.val.val := by
  have hm : a.val ∈ ((preimageToImage q).comp
      (preimageSylow q : Subgroup (naturalDerivedPreimage q)).subtype).range := by
    rw [←imagePositiveSylow_range]
    exact a.property
  obtain ⟨v,hv⟩ := hm
  refine ⟨preimagePositiveEquiv q v,?_⟩
  have hh : (preimageToImage q v.val).val = a.val.val :=
    congrArg (fun x : DerivedImage q => x.val) hv
  exact (preimagePositiveEquiv_action q v).symm.trans hh

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedPositiveImageSylow
