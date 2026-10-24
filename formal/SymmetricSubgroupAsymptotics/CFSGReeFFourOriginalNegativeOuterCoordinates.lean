import SymmetricSubgroupAsymptotics.CFSGReeFFourOuterSignedConjugation
import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalRootCoordinates
import SymmetricSubgroupAsymptotics.CFSGReeFFourSignedBlockWeylGeneration
import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalNegativeRootIntersections

/-! The genuine negative outer parameter hom and its intrinsic original
q-block. Its source is defined by actual Weyl conjugation, with the signed
word identity proved separately; quotient injectivity is inherited only
through the proved original positive chart. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalNegativeOuterCoordinates
open CFSGReeFFourOuterSignedConjugation CFSGReeFFourOuterTorusReflection
open CFSGReeFFourOuterFixedRoot CFSGReeFFourOuterUnipotentGeneration
open CFSGReeFFourFieldParameters CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourPerfectProjection CFSGReeFFourOuterTorusAction
open CFSGReeFFourFixedPositiveFamilies CFSGReeFFourFixedBorelCardinality
open CFSGReeFFourMinimalParabolics CFSGReeFFourSimpleBlockPeelingGeneration
open CFSGReeFFourSignedBlockWeylGeneration CFSGReeFFourOppositionFixedPositiveNegative
open CFSGReeFFourOriginalNegativeRootIntersections CFSGReeFFourOriginalMinimalParabolics
open CFSGReeFFourOriginalOppositeAlignment CFSGReeFFourFixedAmbientHom

def fixedNegativeOuterHom (m : ℕ) : Multiplicative (Field m)→* originalModelFixed m :=
  (MulAut.conj (outerFixedReflection m)).toMonoidHom.comp (fixedOuterHom m)

theorem fixedNegativeOuterHom_value (m : ℕ) (t : Multiplicative (Field m)) :
    fixedNegativeOuterHom m t=fixedSignedOuter m true t.toAdd :=
  fixed_outer_conjugates_parameter m t.toAdd

def originalNegativeOuterHom (m : ℕ) (hm : 0<m) : Multiplicative (Field m)→*CFSG.Models.ReeF4 m :=
  (fixedToOriginal m hm).comp (fixedNegativeOuterHom m)

private theorem map_conjugation {G H : Type*} [Group G] [Group H] (f : G→*H) (w x : G) :
    f (w*x*w⁻¹)=f w*f x*(f w)⁻¹ := by rw [map_mul,map_mul,map_inv]

private theorem originalNegativeOuterHom_conjugation (m : ℕ) (hm : 0<m)
    (t : Multiplicative (Field m)) : originalNegativeOuterHom m hm t=
      (MulAut.conj (fixedToOriginal m hm (outerFixedReflection m))) (originalOuterHom m hm t) :=
  map_conjugation (fixedToOriginal m hm) (outerFixedReflection m) (fixedOuterHom m t)

theorem originalNegativeOuterHom_injective (m : ℕ) (hm : 0<m) :
    Function.Injective (originalNegativeOuterHom m hm) := by
  intro a b he
  have hh := (originalNegativeOuterHom_conjugation m hm a).symm.trans
    (he.trans (originalNegativeOuterHom_conjugation m hm b))
  exact originalOuterHom_injective m hm
    ((MulAut.conj (fixedToOriginal m hm (outerFixedReflection m))).injective hh)

theorem originalNegativeOuterHom_value (m : ℕ) (hm : 0<m) (t : Multiplicative (Field m)) :
    originalNegativeOuterHom m hm t=fixedToOriginal m hm (fixedSignedOuter m true t.toAdd) :=
  congrArg (fixedToOriginal m hm) (fixedNegativeOuterHom_value m t)

private theorem fixedNegativeOuterHom_mem_negative (m : ℕ) (t : Multiplicative (Field m)) :
    fixedNegativeOuterHom m t∈fixedNegative m := by
  rw [fixedNegativeOuterHom_value]
  exact fixedSignedOuter_negative_mem m t.toAdd

private theorem fixedNegativeOuterHom_mem_parabolic (m : ℕ) (t : Multiplicative (Field m)) :
    fixedNegativeOuterHom m t∈simpleParabolic m false := by
  have hW : outerFixedReflection m∈simpleParabolic m false := by
    have hh : simpleWeyl m false∈simpleParabolic m false :=
      (show Subgroup.closure {simpleWeyl m false}≤simpleParabolic m false from le_sup_right)
        (Subgroup.subset_closure (Set.mem_singleton _))
    rwa [simpleWeyl_false] at hh
  have hX : fixedOuterHom m t∈fixedPositive m := by
    have hh : fixedOuterHom m t∈(fixedOuterHom m).range := ⟨t,rfl⟩
    rw [←outer_simple_inversion_eq] at hh
    exact hh.1
  have hXP := ((positive_le_borel m).trans
    (show fixedBorel m≤simpleParabolic m false from le_sup_left)) hX
  exact (simpleParabolic m false).mul_mem ((simpleParabolic m false).mul_mem hW hXP)
    ((simpleParabolic m false).inv_mem hW)

theorem originalNegativeOuterHom_range (m : ℕ) (hm : 0<m) :
    (originalNegativeOuterHom m hm).range=originalNegativeRootBlock m hm false := by
  letI : Finite (originalModelFixed m) :=
    Finite.of_injective (fixedAmbientHom m) (fixedAmbientHom_injective m)
  letI : Finite (CFSG.Models.ReeF4 m) :=
    Finite.of_surjective (fixedToOriginal m hm) (fixedToOriginal_surjective m hm)
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨t,rfl⟩
    rw [←original_negative_inf_simpleParabolic]
    exact ⟨⟨fixedNegativeOuterHom m t,fixedNegativeOuterHom_mem_negative m t,rfl⟩,
      ⟨fixedNegativeOuterHom m t,fixedNegativeOuterHom_mem_parabolic m t,rfl⟩⟩
  · have hc : Nat.card (originalNegativeOuterHom m hm).range=2^(2*m+1) := by
      calc
        _=Nat.card (Multiplicative (Field m)) :=
          (Nat.card_congr (MonoidHom.ofInjective (originalNegativeOuterHom_injective m hm)).toEquiv).symm
        _=Nat.card (Field m) := Nat.card_congr Multiplicative.toAdd
        _=2^(2*m+1) := field_card m
    rw [hc,originalNegativeRootBlock_card]
    simp

end SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalNegativeOuterCoordinates
