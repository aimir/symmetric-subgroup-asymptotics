import SymmetricSubgroupAsymptotics.CFSGOrdinaryRankExtension
import SymmetricSubgroupAsymptotics.CFSGFiniteRankCardinality
import Mathlib.GroupTheory.QuotientGroup.Defs

/-! Ordinary generators across the literal intersection with a normal
subgroup. The displayed kernel and intersection are explicitly isomorphic. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSubgroupKernelRank
variable {G : Type*} [Group G] (N S : Subgroup G) [S.Normal]

def kernelEquivIntersection :
    ((QuotientGroup.mk' S).comp N.subtype).ker ≃* N.subgroupOf S where
  toFun x := ⟨⟨x.val.val, (QuotientGroup.eq_one_iff _).mp x.property⟩, x.val.property⟩
  invFun x := ⟨⟨x.val.val, x.property⟩, (QuotientGroup.eq_one_iff _).mpr x.val.property⟩
  left_inv x := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; apply Subtype.ext; rfl
  map_mul' x y := by apply Subtype.ext; apply Subtype.ext; rfl

theorem rank_le_intersection_add_logb_quotient [Finite G] :
    (Group.rank N : ℝ) ≤ Group.rank (N.subgroupOf S) + Real.logb 2 (Nat.card (G ⧸ S)) := by
  let f := (QuotientGroup.mk' S).comp N.subtype
  have h := CFSGOrdinaryRankExtension.rank_le_kernel_add_range f
  have he := Group.rank_congr (kernelEquivIntersection N S)
  rw [he] at h
  have hc : (Group.rank N : ℝ) ≤ Group.rank (N.subgroupOf S) + Group.rank f.range := by
    exact_mod_cast h
  linarith [CFSGFiniteRankCardinality.subgroup_rank_le_logb_card (G ⧸ S) f.range]

end SymmetricSubgroupAsymptotics.CFSGSubgroupKernelRank
