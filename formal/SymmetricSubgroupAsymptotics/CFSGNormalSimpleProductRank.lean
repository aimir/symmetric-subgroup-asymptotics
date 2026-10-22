import SymmetricSubgroupAsymptotics.CFSGFiniteProductRank

/-! Ordinary rank of an actual normal subgroup of a product of nonabelian
simple groups. The coordinate equivalence is built on that same subgroup. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormalSimpleProductRank
open CFSGNormalSubgroupSimpleProduct CFSGFiniteProductRank
variable {I : Type*} [Fintype I] [DecidableEq I]
    (S : I → Type*) [∀ i, Group (S i)] [∀ i, IsSimpleGroup (S i)]
    (hn : ∀ i, ¬ IsMulCommutative (S i)) (N : Subgroup (∀ i, S i)) [N.Normal]
include hn

def coordinateEquiv : N ≃* ∀ i, N.map (Pi.evalMonoidHom S i) where
  toFun n i := ⟨n.val i, ⟨n.val, n.property, rfl⟩⟩
  invFun x := ⟨fun i => (x i).val, by
    exact (le_of_eq (normal_eq_coordinate_product S hn N).symm) (fun i _ => (x i).property)⟩
  left_inv n := Subtype.ext rfl
  right_inv x := by funext i; apply Subtype.ext; rfl
  map_mul' a b := by funext i; apply Subtype.ext; rfl

include hn in
theorem rank_le_sum_factors [∀ i, Finite (S i)] :
    Group.rank N ≤ ∑ i, Group.rank (S i) := by
  classical
  have he := Group.rank_congr (coordinateEquiv S hn N)
  rw [he]
  refine (rank_le_sum_rank (fun i => N.map (Pi.evalMonoidHom S i))).trans ?_
  apply Finset.sum_le_sum
  intro i _
  let p := Pi.evalMonoidHom S i
  letI : (N.map p).Normal := Subgroup.Normal.map inferInstance _
    (fun a => ⟨Pi.mulSingle i a, Pi.mulSingle_eq_same i a⟩)
  rcases (inferInstance : (N.map p).Normal).eq_bot_or_eq_top with hb | ht
  · have hzero : Group.rank (⊥ : Subgroup (S i)) = 0 := by
      have hc : Subgroup.closure (∅ : Set (⊥ : Subgroup (S i))) = ⊤ := Subsingleton.elim _ _
      have hr := Group.rank_le (S := ∅) (by simpa only [Finset.coe_empty] using hc)
      simpa only [Finset.card_empty, Nat.le_zero] using hr
    rw [Group.rank_congr (MulEquiv.subgroupCongr hb), hzero]
    exact Nat.zero_le _
  · exact le_of_eq (Group.rank_congr ((MulEquiv.subgroupCongr ht).trans Subgroup.topEquiv))

end SymmetricSubgroupAsymptotics.CFSGNormalSimpleProductRank
