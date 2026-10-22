import SymmetricSubgroupAsymptotics.CFSGTwistedA2DerivedGoodSylow
import SymmetricSubgroupAsymptotics.CFSGGoodSylowPrimeSurjective
import SymmetricSubgroupAsymptotics.External.CFSG.Models.LieFamilies

/-! Good defining-characteristic Sylow data for the literal original
CFSG twisted-A2 model. Its actual derived fixed group and its actual
central quotient are used. The classifier explicitly excludes q=2. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGReduction
open CFSGTwistedANaturalMatrices CFSGTwistedA2UnipotentArrays

theorem twistedA2_goodSylowPrime (q : CFSG.PrimePower) (hsmall : q.order ≠ 2) :
    GoodSylowPrime (CFSG.Models.TwistedA 2 q) q.prime := by
  have hq2 : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
  have hq : 3 ≤ q.order := by omega
  letI : Finite (fixedNaturalPullback 2 q) :=
    Finite.of_injective (pullbackMatrix 2 q) (pullbackMatrix_two_injective q)
  letI : Finite (OriginalFixedA 2 q) :=
    Finite.of_surjective (pullbackSource 2 q) (pullbackSource_surjective 2 (by decide) q)
  let D := ↥(commutator (OriginalFixedA 2 q))
  change GoodSylowPrime (D ⧸ Subgroup.center D) q.prime
  exact goodSylowPrime_surjective (QuotientGroup.mk' (Subgroup.center D))
    (QuotientGroup.mk'_surjective _) (originalDerived_goodSylowPrime q hq)

end SymmetricSubgroupAsymptotics.CFSGReduction
