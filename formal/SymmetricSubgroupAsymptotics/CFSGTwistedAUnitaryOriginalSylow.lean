import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryNormalizerPSubgroups
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryWholeUpperDerived
import SymmetricSubgroupAsymptotics.CFSGSylowNormalizerMaximality

/-! The actual original upper subgroup is Sylow in the WHOLE original
fixed source, uniformly all ranks and fields. In rank>=3 it lies in the
original derived subgroup by the independently proved same-source
normal-closure argument, including every field of order two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent

def originalSylow (q : CFSG.PrimePower) (r : ℕ) (hr : 1 ≤ r) : Sylow q.prime (Fixed r q) := by
  letI : Finite (Fixed r q) := originalFixed_finite q r hr
  exact CFSGSylowNormalizerMaximality.sylowOfNormalizer (originalUnipotent r q)
    (originalUnipotent_isPGroup r q) (original_normalizer_pSubgroups q r hr)

theorem originalSylow_coe (q : CFSG.PrimePower) (r : ℕ) (hr : 1 ≤ r) :
    (originalSylow q r hr : Subgroup (Fixed r q)) = originalUnipotent r q := rfl

theorem originalSylow_le_derived (q : CFSG.PrimePower) (s : ℕ) :
    (originalSylow q (s + 3) (by omega) : Subgroup (Fixed (s + 3) q)) ≤
      commutator (Fixed (s + 3) q) := originalUnipotent_le_derived q s

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
