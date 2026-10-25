import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryDerivedGeneration
import SymmetricSubgroupAsymptotics.TwoOddInvolutionIntersectionGeneration
import SymmetricSubgroupAsymptotics.NormalSubgroupConjugateIntersection
import SymmetricSubgroupAsymptotics.CFSGReeFFourAllParameterDerivedPositive
import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedOuterWeylInvolution
import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedDerivedInversionFacts

/-! The actual binary derived positive and negative Sylows generate the
whole original derived fixed group. The ONLY conditional input remains
membership of the original outer involution in that actual derived group.
Opposition is used as an ambient automorphism, never assumed to belong
to the derived group. The exact original Sylows and full group are kept. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryDerivedOppositeGeneration
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourOuterThreeWord CFSGReeFFourMiddleDerivedFiveWord
open CFSGReeFFourRelativePositiveSubgroups CFSGReeFFourBinaryAbelianGenerators
open CFSGReeFFourMinimalParabolics CFSGReeFFourAbelianImageCardinality
open CFSGReeFFourRelativeWeylInvolutions CFSGReeFFourOppositionFixedPositiveNegative
open CFSGReeFFourDerivedAmbientHom CFSGReeFFourAllParameterDerivedPositive
open CFSGReeFFourBinaryDerivedGeneration CFSGReeFFourMiddleSquareCommutator
open CFSGReeFFourDerivedOppositeSylow CFSGReeFFourFixedOuterWeylInvolution
open CFSGReeFFourFixedDerivedInversionFacts

/-- Identify the SAME actual negative Sylow with the negative intersection;
ambient opposition need not be an element of the derived subgroup. -/
theorem negativeSylow_coe_eq_negative_comap (m : ℕ) :
    (negativeSylow m : Subgroup (commutator (originalModelFixed m))) =
      (fixedNegative m).comap (commutator (originalModelFixed m)).subtype := by
  rw [negativeSylow_coe]
  change ((fixedPositive m).comap (commutator (originalModelFixed m)).subtype).map
    (MulAut.conjNormal (oppositionFixed m)).toMonoidHom = _
  rw [NormalSubgroupConjugateIntersection.map_comap_conj_normal,
    fixed_positive_image_eq_fixed_negative]

private theorem derived_head_le
    (hxD : outerInvolution 0 ∈ commutator (originalModelFixed 0)) :
    commutator (originalModelFixed 0) ≤
      (fixedPositive 0 ⊓ commutator (originalModelFixed 0)) ⊔
        Subgroup.closure ({outerFixedWeyl 0, middleFixedWeyl 0} : Set (originalModelFixed 0)) :=
  le_of_eq (derived_eq_positive_intersection_sup_weyls hxD)

/-- The odd three/five product periods recover both actual Weyl
involutions from the two literal positive/negative intersections. -/
theorem positive_inf_derived_sup_negative_inf_derived
    (hxD : outerInvolution 0 ∈ commutator (originalModelFixed 0)) :
    (fixedPositive 0 ⊓ commutator (originalModelFixed 0)) ⊔
      (fixedNegative 0 ⊓ commutator (originalModelFixed 0)) =
        commutator (originalModelFixed 0) :=
  TwoOddInvolutionIntersectionGeneration.sup_eq
    (fixedPositive 0 ⊓ commutator (originalModelFixed 0))
    (fixedNegative 0 ⊓ commutator (originalModelFixed 0))
    (commutator (originalModelFixed 0))
    (outerFixedWeyl 0) (middleFixedWeyl 0) (outerInvolution 0) ((fourCycle 0) ^ 2) 1 2
    inf_le_right inf_le_right (derived_head_le hxD)
    (outer_weyl_square 0) (middleWeyl_square 0) (outerInvolution_square 0) (middle_square_square 0)
    (outerWeyl_product_cube 0) (fiveWord_pow_five 0)
    (outer_positive_derived 0 hxD) (middle_square_positive_derived 0)
    (outer_negative_derived 0 hxD) (middle_square_negative_derived 0)

/-- The original actual Sylow subgroups generate the FULL actual derived
group, without replacing that group by a quotient or an unrelated model. -/
theorem positive_sup_negative_eq_top
    (hxD : outerInvolution 0 ∈ commutator (originalModelFixed 0)) :
    (positiveSylow 0 : Subgroup (commutator (originalModelFixed 0))) ⊔
      (negativeSylow 0 : Subgroup (commutator (originalModelFixed 0))) = ⊤ := by
  let D := commutator (originalModelFixed 0)
  apply Subgroup.map_injective D.subtype_injective
  rw [Subgroup.map_sup, positiveSylow_coe, negativeSylow_coe_eq_negative_comap]
  change ((fixedPositive 0).comap D.subtype).map D.subtype ⊔
    ((fixedNegative 0).comap D.subtype).map D.subtype = (⊤ : Subgroup D).map D.subtype
  rw [Subgroup.map_comap_eq, Subgroup.map_comap_eq, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]
  simpa only [inf_comm] using positive_inf_derived_sup_negative_inf_derived hxD

end SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryDerivedOppositeGeneration
