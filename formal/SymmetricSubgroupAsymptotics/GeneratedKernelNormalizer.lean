import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Subgroup.Lattice

/-! A finite kernel chart need not be central in the original group.
Actual generator conjugation permutations prove normality of its exact range. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.GeneratedKernelNormalizer
variable {G K J : Type} [Group G] [Group K]

 theorem range_normal (s : J → G)
    (hgen : Subgroup.closure (Set.range s)=⊤)
    (kappa : K →* G) (conjugate : J → Equiv.Perm K)
    (hconj : ∀ j k, kappa (conjugate j k)=s j*kappa k*(s j)⁻¹) :
    kappa.range.Normal := by
  have hs (j : J) : s j∈Subgroup.normalizer (kappa.range : Set G) := by
    apply Subgroup.mem_normalizer_iff.mpr
    intro g
    constructor
    · rintro ⟨k,rfl⟩
      exact ⟨conjugate j k,hconj j k⟩
    · rintro ⟨k,hk⟩
      refine ⟨(conjugate j).symm k,?_⟩
      have hh := hconj j ((conjugate j).symm k)
      rw [(conjugate j).apply_symm_apply] at hh
      exact mul_left_cancel (mul_right_cancel (hh.symm.trans hk))
  apply Subgroup.normalizer_eq_top_iff.mp
  apply top_unique
  rw [←hgen]
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨j,rfl⟩
  exact hs j

end SymmetricSubgroupAsymptotics.GeneratedKernelNormalizer
