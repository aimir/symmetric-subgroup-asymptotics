import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddlePositiveIntersectionNormalizer

/-! Opaque selected-point boundaries for the SAME original positive
commutator. Generic comp/subtype transport prevents kernel reduction
through its fixed-root word when applying the actual strict-kernel fact. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourMiddlePositiveCommutatorIntersection
open CFSGReeFFourMiddlePositiveIntersectionNormalizer
open CFSGReeFFourMiddlePositiveKernelIntersection CFSGReeFFourMiddleGradedKernel
open CFSGReeFFourMiddleParabolicFlag CFSGReeFFourMiddleDerivedFiveRootWords
open CFSGReeFFourFixedPositiveFamilies CFSGReeFFourFixedModelEquivalence
open CFSGGradedMatrixSubgroups CFSGReeFFourFieldParameters

private theorem comap_membership {G H : Type*} [Group G] [Group H]
    (f : G →* H) (K : Subgroup H) (x : G) (hx : x∈K.comap f) : f x∈K := hx

private theorem comp_subtype_apply {G H : Type*} [Group G] [Group H]
    (f : G →* H) (P : Subgroup G) (x : P) : f.comp P.subtype x=f x.val := rfl

private theorem commutator_parabolic_value (m : ℕ) :
    (commutatorInParabolic m).val=positiveCommutator m := rfl

private theorem raw_parabolic_apply (m : ℕ) (x : middleParabolic m) :
    parabolicRawHom m x=fixedRawHom m x.val :=
  comp_subtype_apply (fixedRawHom m) (middleParabolic m) x

private theorem raw_commutator_value (m : ℕ) :
    parabolicRawHom m (commutatorInParabolic m)=fixedRawHom m (positiveCommutator m) :=
  (raw_parabolic_apply m (commutatorInParabolic m)).trans
    (congrArg (fixedRawHom m) (commutator_parabolic_value m))

theorem positiveCommutator_strict (m : ℕ) :
    fixedRawHom m (positiveCommutator m)∈strictUnits middleWeight := by
  have h := comap_membership (parabolicRawHom m)
    (strictUnits (K := Field m) middleWeight) (commutatorInParabolic m)
    (commutator_mem_gradedKernel m)
  exact Eq.mp (congrArg (fun x => x∈strictUnits (K := Field m) middleWeight)
    (raw_commutator_value m)) h

private theorem mem_intersection {G : Type*} [Group G] (U : Subgroup G) (w x : G)
    (hx : x∈U) (hc : w*x*w⁻¹∈U) : x∈U⊓U.comap (MulAut.conj w).toMonoidHom := ⟨hx,hc⟩

theorem positiveCommutator_mem_intersection (m : ℕ) :
    positiveCommutator m∈middlePositiveIntersection m :=
  mem_intersection (fixedPositive m) (CFSGReeFFourRelativePositiveSubgroups.middleFixedWeyl m)
    (positiveCommutator m) (positiveCommutator_mem_positive m)
    ((positive_strict_iff_opposite_positive m (positiveCommutator m)
      (positiveCommutator_mem_positive m)).mp (positiveCommutator_strict m))

end SymmetricSubgroupAsymptotics.CFSGReeFFourMiddlePositiveCommutatorIntersection
