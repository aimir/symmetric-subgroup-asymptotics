import SymmetricSubgroupAsymptotics.CFSGOpposedSubgroupPeeling

/-! Inversion-block equality and Weyl equality give negative conjugate
membership over an ABSTRACT group. Concrete applications do not project
or transport the expanded model-specific block predicate themselves. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.InversionSubgroupConjugateMembership
open CFSGOpposedSubgroupPeeling
variable {G : Type*} [Group G]

theorem conjugate_mem (U V H : Subgroup G) (w w' s : G)
    (hblock : inversionPart U V w = H) (hw : w = w') (hs : s ∈ H) :
    w' * s * w'⁻¹ ∈ V := by
  have hb : s ∈ inversionPart U V w := by rw [hblock]; exact hs
  have hn : w * s * w⁻¹ ∈ V := hb.2
  simpa only [hw] using hn

end SymmetricSubgroupAsymptotics.InversionSubgroupConjugateMembership
