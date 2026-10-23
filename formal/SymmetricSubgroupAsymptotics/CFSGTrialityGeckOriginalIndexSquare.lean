import SymmetricSubgroupAsymptotics.CFSGTrialityGeckDerivedLongFamilyCardinality
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalOrderLower

/-! Squared least proper index in the SAME ORIGINAL simple triality
model. The q-element highest-root subgroup survives its actual central
quotient; its conjugate family factors through the checked matrix family.
No exceptional order formula or outer-automorphism premise is used. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalIndexSquare
open CFSGTrialityGeckDerivedLongLine CFSGTrialityGeckFixedLongLine
open CFSGTrialityGeckDerivedLongFamilyCardinality CFSGTrialityGeckFixedRootFamilyCardinality
open CFSGTrialityGeckDerivedProjectiveImage CFSGTrialityGeckOriginalOrderLower
open CFSGTrialityGeckFixedPositiveImageSylow CFSGTrialityGeckDerivedSylowNormalizer
open CFSGConjugateFamilyTransport CFSGSimpleConjugateFamilyIndex
open PrimitiveSocleRawStructure

local instance (q : CFSG.PrimePower) : Finite (DerivedImage q) :=
  Finite.of_surjective (preimageToImage q) (preimageToImage_surjective q)

def originalProjection (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TrialityD4 q)] :
    DerivedImage q →* CFSG.Models.TrialityD4 q :=
  (originalProjectiveImageEquiv q).symm.toMonoidHom.comp
    (QuotientGroup.mk' (Subgroup.center (DerivedImage q)))

theorem originalProjection_surjective (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] : Function.Surjective (originalProjection q) :=
  (originalProjectiveImageEquiv q).symm.surjective.comp
    (QuotientGroup.mk'_surjective (Subgroup.center (DerivedImage q)))

def originalLongLine (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TrialityD4 q)] :
    Subgroup (CFSG.Models.TrialityD4 q) :=
  (derivedLongLine q).map (originalProjection q)

theorem original_long_parameter_injective (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] :
    Function.Injective ((originalProjection q).comp (longToDerived q)) := by
  intro x y he
  apply longToDerived_injective q
  have hi := CFSGDisjointSylowProjectiveCardinality.central_quotient_injective
    (imagePositiveSylow q) (oppositeSylow q) (oppositeSylows_disjoint q)
  have hq : (QuotientGroup.mk' (Subgroup.center (DerivedImage q))) (longToDerived q x) =
      (QuotientGroup.mk' (Subgroup.center (DerivedImage q))) (longToDerived q y) :=
    (originalProjectiveImageEquiv q).symm.injective he
  have hp : (⟨longToDerived q x,longToDerived_mem_positiveSylow q x⟩ : imagePositiveSylow q) =
      ⟨longToDerived q y,longToDerived_mem_positiveSylow q y⟩ := hi hq
  exact congrArg (fun z : imagePositiveSylow q => z.val) hp

theorem originalLongLine_card (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] : Nat.card (originalLongLine q) = q.order := by
  have hr : originalLongLine q = ((originalProjection q).comp (longToDerived q)).range :=
    (MonoidHom.range_comp (originalProjection q) (longToDerived q)).symm
  rw [hr]
  exact (Nat.card_congr (MonoidHom.ofInjective (original_long_parameter_injective q)).toEquiv).symm.trans
    (fixedLongLine_card q)

def originalLongFamily (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TrialityD4 q)] :=
  Set.range (fun g : CFSG.Models.TrialityD4 q =>
    (originalLongLine q).map (MulAut.conj g).toMonoidHom)

theorem original_long_family_card_le_fixed (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] :
    Nat.card (originalLongFamily q) ≤ Nat.card (fixedRootFamily q) :=
  (card_family_map_le (originalProjection q) (originalProjection_surjective q) (derivedLongLine q)).trans
    (derived_long_family_card_le_fixed q)

private theorem order_ge_two (q : CFSG.PrimePower) : 2 ≤ q.order := by
  calc
    2 ≤ q.prime := q.prime_isPrime.two_le
    _ = q.prime ^ 1 := (pow_one _).symm
    _ ≤ q.prime ^ q.exponent := Nat.pow_le_pow_right q.prime_isPrime.pos q.exponent_pos

theorem originalLongLine_ne_bot (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] : originalLongLine q ≠ ⊥ := by
  intro h
  have hc := originalLongLine_card q
  rw [h,Subgroup.card_bot] at hc
  have := order_ge_two q
  omega

theorem originalLongLine_ne_top (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] : originalLongLine q ≠ ⊤ := by
  intro h
  have hc := originalLongLine_card q
  rw [h,Subgroup.card_top] at hc
  have hlow := original_card_lower q
  have hq := order_ge_two q
  have hp : q.order ^ 2 ≤ q.order ^ 24 := Nat.pow_le_pow_right (by omega) (by decide)
  rw [hc] at hlow
  nlinarith

theorem original_index_square (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] (ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.TrialityD4 q) ell) :
    ell ^ 2 < Nat.card (CFSG.Models.TrialityD4 q) := by
  have hindex := least_index_le_family (originalLongLine q)
    (originalLongLine_ne_bot q) (originalLongLine_ne_top q) ell hell
  have hfamily : ell ≤ Nat.card (fixedRootFamily q) :=
    hindex.trans (original_long_family_card_le_fixed q)
  exact (Nat.pow_le_pow_left hfamily 2).trans_lt
    ((fixed_root_family_square_lt q).trans_le (original_card_lower q))

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalIndexSquare
