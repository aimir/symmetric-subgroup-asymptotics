import SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentPSubgroups
import SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentDerived
import SymmetricSubgroupAsymptotics.CFSGSylowNormalizerMaximality

/-! The literal rank-two original unipotent subgroup is Sylow in the
WHOLE original fixed source. The criterion uses the p-group normalizer
condition inside every possible p-overgroup, not an ambient SU order. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentArrays
open CFSGTwistedANaturalMatrices

noncomputable def originalSylow (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    Sylow q.prime (OriginalFixedA 2 q) := by
  letI : Finite (fixedNaturalPullback 2 q) :=
    Finite.of_injective (pullbackMatrix 2 q) (pullbackMatrix_two_injective q)
  letI : Finite (OriginalFixedA 2 q) :=
    Finite.of_surjective (pullbackSource 2 q) (pullbackSource_surjective 2 (by decide) q)
  exact CFSGSylowNormalizerMaximality.sylowOfNormalizer (originalUnipotent q)
    (originalUnipotent_isPGroup q hq) (original_normalizer_pSubgroups q hq)

theorem originalSylow_coe (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    (originalSylow q hq : Subgroup (OriginalFixedA 2 q)) = originalUnipotent q := rfl

theorem originalSylow_le_commutator (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    (originalSylow q hq : Subgroup (OriginalFixedA 2 q)) ≤
      commutator (OriginalFixedA 2 q) := originalUnipotent_le_commutator q hq

end SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentArrays
