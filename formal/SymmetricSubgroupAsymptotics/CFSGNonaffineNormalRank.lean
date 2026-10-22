import SymmetricSubgroupAsymptotics.CFSGSubgroupKernelRank
import SymmetricSubgroupAsymptotics.CFSGNormalSimpleProductRank
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawChart

/-! Actual normal-subgroup ordinary rank through the full original
nonaffine socle. The only numerical simple-factor premise is displayed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNonaffineNormalRank
open PrimitiveSocleRawStructure
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X)

theorem normal_rank_le_factors_add_quotient (hs : Group.rank D.Simple ≤ 2)
    (N : Subgroup G) [N.Normal] :
    (Group.rank N : ℝ) ≤ 2 * D.factorCount + Real.logb 2 (Nat.card (G ⧸ finiteGroupSocle G)) := by
  let K := N.subgroupOf (finiteGroupSocle G)
  let M := K.map D.socleEquiv.toMonoidHom
  letI : M.Normal := Subgroup.Normal.map inferInstance _ D.socleEquiv.surjective
  have h := CFSGNormalSimpleProductRank.rank_le_sum_factors
    (fun _ : Fin D.factorCount => D.Simple) (fun _ => D.noncommutative) M
  have he := Group.rank_congr (D.socleEquiv.subgroupMap K)
  have hK : Group.rank K ≤ D.factorCount * Group.rank D.Simple := by
    rw [he]
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] using h
  have hK2 : Group.rank K ≤ 2 * D.factorCount :=
    hK.trans (by simpa only [Nat.mul_comm] using Nat.mul_le_mul_left D.factorCount hs)
  have hc : (Group.rank K : ℝ) ≤ 2 * D.factorCount := by exact_mod_cast hK2
  have hbound := CFSGSubgroupKernelRank.rank_le_intersection_add_logb_quotient N (finiteGroupSocle G)
  change (Group.rank N : ℝ) ≤ Group.rank K + _ at hbound
  linarith

end SymmetricSubgroupAsymptotics.CFSGNonaffineNormalRank
