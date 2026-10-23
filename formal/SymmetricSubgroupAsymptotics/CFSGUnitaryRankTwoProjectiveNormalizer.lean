import SymmetricSubgroupAsymptotics.CFSGUnitaryRankTwoNaturalSylow
import SymmetricSubgroupAsymptotics.CFSGUnitaryRankTwoKernelCentral
import SymmetricSubgroupAsymptotics.CFSGKernelFlagProductCard
import SymmetricSubgroupAsymptotics.CFSGQuotientNormalizerIntersection

/-! Full natural upper normalizers map onto the full upper normalizers
in the same original projective model. The actual central-kernel and
Sylow separation hypotheses are proved, not supplied by recognition. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedAUpperUnipotent

theorem rankTwoProjectiveUpper_injective (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    Function.Injective ((rankTwoProjectiveCover q hq).comp (rankTwoUpperSubgroup q).subtype) := by
  let f := rankTwoProjectiveCover q hq
  have hinj := CFSGKernelFlagProductCard.injective_on_disjoint f
    (rankTwoUpperFlag q) (rankTwoOppositeSubgroup q) (rankTwoOpposite_inf_flag q)
    (rankTwoProjectiveCover_kernel_le_flag q hq)
  apply (f.comp (rankTwoUpperSubgroup q).subtype).ker_eq_bot_iff.mp
  apply bot_unique
  intro x hx
  let w := reversalFixed q 2
  let y : rankTwoOppositeSubgroup q :=
    ⟨w * x.val * w⁻¹, ⟨x.val, x.property, rfl⟩⟩
  have hy : f.comp (rankTwoOppositeSubgroup q).subtype y =
      f.comp (rankTwoOppositeSubgroup q).subtype 1 := by
    change f (w * x.val * w⁻¹) = f 1
    simp only [map_mul, map_inv, map_one, show f x.val = 1 from hx,
      mul_one, mul_inv_cancel]
  have hone : w * x.val * w⁻¹ = 1 :=
    congrArg (fun z : rankTwoOppositeSubgroup q => z.val) (hinj hy)
  have hxone : x.val = 1 := by
    apply (MulAut.conj w).injective
    change w * x.val * w⁻¹ = w * 1 * w⁻¹
    simpa only [mul_one, mul_inv_cancel] using hone
  exact Subtype.ext hxone

theorem rankTwo_projective_normalizer_map (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    (Subgroup.normalizer (rankTwoUpperSubgroup q : Set _)).map (rankTwoProjectiveCover q hq) =
      Subgroup.normalizer ((rankTwoUpperSubgroup q).map (rankTwoProjectiveCover q hq) : Set _) := by
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  exact CFSGQuotientNormalizerIntersection.normalizer_map_eq_of_central_p_separation
    (rankTwoProjectiveCover q hq) (rankTwoProjectiveCover_surjective q hq)
    (rankTwoNaturalSylow q) (rankTwoProjectiveUpper_injective q hq)
    (rankTwoProjectiveCover_kernel_central q hq) (rankTwoUpperSubgroup q)
    (rankTwoUpperSubgroup_isPGroup q)

theorem rankTwo_projective_normalizer_iff (q : CFSG.PrimePower) (hq : 3 ≤ q.order)
    (V : Subgroup (CFSGTwistedAUpperUnipotent.naturalFixed 2 q)) (hV : IsPGroup q.prime V)
    (g : CFSGTwistedAUpperUnipotent.naturalFixed 2 q) :
    rankTwoProjectiveCover q hq g ∈ Subgroup.normalizer (V.map (rankTwoProjectiveCover q hq) : Set _) ↔
      g ∈ Subgroup.normalizer (V : Set _) := by
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  exact CFSGCentralKernelPSubgroupReflection.mem_normalizer_map_iff (rankTwoProjectiveCover q hq)
    (rankTwoNaturalSylow q) (rankTwoProjectiveUpper_injective q hq)
    (rankTwoProjectiveCover_kernel_central q hq) V hV g

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
