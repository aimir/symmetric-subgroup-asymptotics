import SymmetricSubgroupAsymptotics.CyclicSocleQuotientTools
import Mathlib.GroupTheory.PGroup

/-! A nonbinary original quotient cannot kill the kernel of a homomorphism
into a binary group. No surjectivity to the ambient group is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

theorem nonbinary_quotient_not_le_kernel {G B : Type} [Group G] [Group B]
    (f : G →* B) (hB : IsPGroup 2 B)
    (N : Subgroup G) [N.Normal] (hQ : ¬ IsPGroup 2 (G ⧸ N)) :
    ¬ f.ker≤N := by
  intro hle
  obtain ⟨q,hq,_⟩ := CyclicSocleQuotientTools.exists_surjective_factor
    f.rangeRestrict f.rangeRestrict_surjective
    (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) (by
      rw [QuotientGroup.ker_mk']
      intro g hg
      exact hle (congrArg Subtype.val hg))
  exact hQ ((hB.to_subgroup f.range).of_surjective q hq)

end SymmetricSubgroupAsymptotics
