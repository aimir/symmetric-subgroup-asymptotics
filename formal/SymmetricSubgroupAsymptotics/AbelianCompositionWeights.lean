import SymmetricSubgroupAsymptotics.ChiefTernaryWeights
import SymmetricSubgroupAsymptotics.SubnormalCompositionRefinement
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Abelianization.Defs

/-! Individual composition edges lying inside an actual abelian chief
interval have at most one ternary factor. These bounds prepare the
chosen-chief-weight versus actual composition-length comparison. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped IsMulCommutative
namespace SymmetricSubgroupAsymptotics

theorem quotient_isMulCommutative_of_abelian_map {G Q:Type*} [Group G] [Group Q]
    [IsMulCommutative Q] (f:G→*Q) (N:Subgroup G) [N.Normal]
    (hk:f.ker≤N) : IsMulCommutative (G⧸N) := by
  have hc : commutator G≤N := (Abelianization.commutator_subset_ker f).trans hk
  have hz : (commutator G).map (QuotientGroup.mk' N)=⊥ :=
    (Subgroup.map_eq_bot_iff _).mpr (by simpa only [QuotientGroup.ker_mk'] using hc)
  rw [map_commutator_eq,MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective N)] at hz
  exact (commutator_eq_bot_iff (G⧸N)).mp hz

section Interval
variable {R:Type} [Group R] (B L S T:Subgroup R) [B.Normal] [L.Normal]
variable (hBS:B≤S) (hST:S≤T) (hTL:T≤L)
variable [IsMulCommutative (normalChainQuotient B L)]
variable [(S.subgroupOf T).Normal]
include hBS hST hTL

theorem abelianInterval_quotient_commutative : IsMulCommutative (T⧸S.subgroupOf T) := by
  let f : T→*normalChainQuotient B L :=
    (normalChainMap B L).comp (Subgroup.inclusion hTL)
  apply quotient_isMulCommutative_of_abelian_map f (S.subgroupOf T)
  intro t ht
  apply hBS
  exact (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val ht)

theorem abelianInterval_simple_ternary_weight
    [IsSimpleGroup (T⧸S.subgroupOf T)] :
    (S.relIndex T).factorization 3≤1 := by
  letI := abelianInterval_quotient_commutative B L S T hBS hST hTL
  have hp : (Nat.card (T⧸S.subgroupOf T)).Prime := IsSimpleGroup.prime_card
  rw [Subgroup.relIndex,Subgroup.index_eq_card,hp.factorization]
  simp only [Finsupp.single_apply]
  split_ifs <;> omega

end Interval

end SymmetricSubgroupAsymptotics
