import SymmetricSubgroupAsymptotics.MetacyclicGeneratorPair
import SymmetricSubgroupAsymptotics.PublishedBurnsideTwoPrimeSolvability
set_option autoImplicit false
noncomputable section
open scoped IsMulCommutative
namespace SymmetricSubgroupAsymptotics

theorem isSolvable_of_cyclic_normal_and_quotient
    {G : Type} [Group G] (K : Subgroup G) [K.Normal]
    [IsCyclic K] [IsCyclic (G ⧸ K)] : IsSolvable G := by
  letI : IsSolvable K := isSolvable_of_comm (fun x y => mul_comm x y)
  letI : IsSolvable (G ⧸ K) := isSolvable_of_comm (fun x y => mul_comm x y)
  exact solvable_of_ker_le_range K.subtype (QuotientGroup.mk' K)
    (by rw [QuotientGroup.ker_mk',Subgroup.range_subtype])

theorem isSolvable_of_generating_pair_cyclic_conjugates
    {G : Type} [Group G] (a b : G)
    (hgen : Subgroup.closure ({a,b} : Set G)=⊤)
    (hba : b*a*b⁻¹ ∈ Subgroup.zpowers a)
    (hbia : b⁻¹*a*b ∈ Subgroup.zpowers a) : IsSolvable G := by
  letI := zpowers_normal_of_generating_pair a b hgen hba hbia
  letI := quotient_isCyclic_of_generating_pair a b hgen
  exact isSolvable_of_cyclic_normal_and_quotient (Subgroup.zpowers a)

theorem isSolvable_closure_of_conjugate_powers
    {G : Type} [Group G] (a b : G) (k l : ℕ)
    (hba : b*a*b⁻¹=a^k) (hbia : b⁻¹*a*b=a^l) :
    IsSolvable (Subgroup.closure ({a,b} : Set G)) := by
  let R := Subgroup.closure ({a,b} : Set G)
  let aR : R := ⟨a,Subgroup.subset_closure (by simp)⟩
  let bR : R := ⟨b,Subgroup.subset_closure (by simp)⟩
  apply isSolvable_of_generating_pair_cyclic_conjugates aR bR
    (closure_pair_subtype_generators a b)
  · have h : bR*aR*bR⁻¹=aR^k := Subtype.ext hba
    rw [h]
    exact Subgroup.npow_mem_zpowers aR k
  · have h : bR⁻¹*aR*bR=aR^l := Subtype.ext hbia
    rw [h]
    exact Subgroup.npow_mem_zpowers aR l

end SymmetricSubgroupAsymptotics
