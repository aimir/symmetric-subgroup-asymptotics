import SymmetricSubgroupAsymptotics.CFSGTwistedA2TorusLayerFaithful
import SymmetricSubgroupAsymptotics.CFSGFiniteFieldScalarNormalizerCard

/-! Cardinality of the actual rank-two torus normalizer in Aut(R).
The intrinsic layer is faithful by the proved central-extension argument;
the actual scalar normalizer reconstruction supplies the field factor.
Original-model automorphism restriction and inner cancellation are later
steps, and are not asserted by this intrinsic count. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGFiniteFieldScalarNormalizer

def rankTwoNormalizerFirstHom (q : CFSG.PrimePower) :
    Subgroup.normalizer ((rankTwoRadicalTorusAutHom q).range : Set (MulAut (fixedRadical q 0))) →*
      AddAut (q.Extension 2) :=
  (rankTwoFirstLayerAutHom q).comp
    (Subgroup.normalizer ((rankTwoRadicalTorusAutHom q).range : Set (MulAut (fixedRadical q 0)))).subtype

theorem rankTwoNormalizerFirstHom_injective (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    Function.Injective (rankTwoNormalizerFirstHom q) := by
  apply (rankTwoNormalizerFirstHom q).ker_eq_bot_iff.mp
  apply bot_unique
  intro f hf
  apply Subgroup.mem_bot.mpr
  apply Subtype.ext
  exact rankTwo_normalizer_first_kernel q hq f.val f.property hf

def rankTwoNormalizerScalarMap (q : CFSG.PrimePower) (hq : 3 ≤ q.order)
    (f : Subgroup.normalizer ((rankTwoRadicalTorusAutHom q).range : Set (MulAut (fixedRadical q 0)))) :
    Subgroup.normalizer (scalarSubgroup (q.Extension 2) : Set (AddAut (q.Extension 2))) :=
  ⟨rankTwoFirstLayerAutHom q f.val, rankTwoFirstLayer_mem_scalar_normalizer q hq f.val f.property⟩

theorem rankTwoNormalizerScalarMap_injective (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    Function.Injective (rankTwoNormalizerScalarMap q hq) := by
  intro f g he
  apply rankTwoNormalizerFirstHom_injective q hq
  exact congrArg
    (fun A : Subgroup.normalizer (scalarSubgroup (q.Extension 2) : Set (AddAut (q.Extension 2))) => A.val) he

theorem rankTwo_torus_normalizer_card_le (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    Nat.card (Subgroup.normalizer ((rankTwoRadicalTorusAutHom q).range : Set (MulAut (fixedRadical q 0)))) ≤
      (q.order ^ 2 - 1) * (2 * q.exponent) := by
  have hmap := Nat.card_le_card_of_injective (rankTwoNormalizerScalarMap q hq)
    (rankTwoNormalizerScalarMap_injective q hq)
  have hbound := card_scalarNormalizer_le (q.Extension 2)
  have hcard : Nat.card (q.Extension 2)ˣ = q.order ^ 2 - 1 := by
    rw [Nat.card_units, CFSGTwistedANaturalMatrices.extension_two_card]
  have haut : Nat.card (q.Extension 2 ≃+* q.Extension 2) = 2 * q.exponent :=
    CFSGFiniteFieldAutomorphisms.card_galoisField_ringAut q.prime (2 * q.exponent)
      (Nat.mul_ne_zero (by decide) (Nat.ne_of_gt q.exponent_pos))
  exact hmap.trans (by simpa only [hcard, haut] using hbound)

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
