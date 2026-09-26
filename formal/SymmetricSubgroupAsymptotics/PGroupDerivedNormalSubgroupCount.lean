import SymmetricSubgroupAsymptotics.PGroupNormalSubgroupCount
import SymmetricSubgroupAsymptotics.PrimeSubdirectNormalRank

/-! Install the bounded-index normal-subgroup count with the actual
finite maximum of ambient relative heads. The derived-normal endpoint
uses the original containment M ≤ G', with no supplied numerical bound. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem pGroup_normal_subgroup_count_le_normalHeadMax (hG : IsPGroup p G)
    (M : Subgroup G) [M.Normal] (a : ℕ) :
    Nat.card (NormalSubgroupsAtMostIndex M (p ^ a)) ≤
      p ^ (a * primeNormalHeadMax p M) := by
  apply pGroup_normal_subgroup_count_le hG M (primeNormalHeadMax p M)
  intro L _ hL
  exact primeRelativeHead_le_normalHeadMax p M L hL

/-- Every counted subgroup is normal in the whole original G, lies
inside the displayed original M, and has its literal index in M bounded.
The controlling rank is the actual maximum over normals inside G'. -/
theorem pGroup_derived_normal_subgroup_count_le (hG : IsPGroup p G)
    (M : Subgroup G) [M.Normal] (hM : M ≤ commutator G) (a : ℕ) :
    Nat.card (NormalSubgroupsAtMostIndex M (p ^ a)) ≤
      p ^ (a * primeDerivedNormalRank p G) := by
  apply pGroup_normal_subgroup_count_le hG M (primeDerivedNormalRank p G)
  intro L _ hL
  exact primeRelativeHead_le_normalHeadMax p (commutator G) L (hL.trans hM)

end SymmetricSubgroupAsymptotics
