import SymmetricSubgroupAsymptotics.Non2PreE7B6RankTailSource
import SymmetricSubgroupAsymptotics.ScalarFourHeadDefinitions
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Commutator.Basic

/-! An actual normal subgroup meeting the C3 top leaves a small binary
quotient. A self-centralizing binary kernel of order at most64 suffices:
one nontrivial mixed commutator cuts its surviving image to order at most32.
No normal-subgroup census or quotient type list is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical commutatorElement
namespace SymmetricSubgroupAsymptotics
namespace CubicOutsideKernelBinaryQuotient

variable {G : Type} [Group G] [Finite G]
  (top : G →* CyclicThree)
  (hbinary : IsPGroup 2 top.ker) (hcard : Nat.card top.ker ≤ 64)
  (hcentralizer : ∀ g : G, (∀ k : top.ker, g * k = k * g) → g ∈ top.ker)
  (N : Subgroup G) [N.Normal] (hN : ¬ N ≤ top.ker)

include hN in
private theorem top_on_normal_surjective :
    Function.Surjective (top.comp N.subtype) := by
  letI : Fact (Nat.card CyclicThree).Prime := ⟨by
    norm_num [CyclicThree,Nat.card_eq_fintype_card]⟩
  apply MonoidHom.range_eq_top.mp
  apply (top.comp N.subtype).range.eq_bot_or_eq_top_of_prime_card.resolve_left
  intro hb
  apply hN
  intro n hn
  apply MonoidHom.mem_ker.mpr
  have hm : top n ∈ (top.comp N.subtype).range := ⟨⟨n,hn⟩,rfl⟩
  rw [hb] at hm
  exact Subgroup.mem_bot.mp hm

private def kernelMap : top.ker →* G ⧸ N :=
  (QuotientGroup.mk' N).comp top.ker.subtype

include hN in
private theorem kernelMap_surjective : Function.Surjective (kernelMap top N) := by
  intro q
  obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective N q
  obtain ⟨n,hn⟩ := top_on_normal_surjective top N hN (top g)
  have hk : g * (n : G)⁻¹ ∈ top.ker := by
    rw [MonoidHom.mem_ker,map_mul,map_inv]
    have hn' : top (n : G) = top g := hn
    rw [hn',mul_inv_cancel]
  refine ⟨⟨g * (n : G)⁻¹,hk⟩,?_⟩
  change (QuotientGroup.mk' N) (g * (n : G)⁻¹) = (QuotientGroup.mk' N) g
  have hnq : (QuotientGroup.mk' N) (n : G) = 1 :=
    (QuotientGroup.eq_one_iff (N := N) (n : G)).mpr n.2
  rw [map_mul,map_inv,hnq,inv_one,mul_one]

include hcentralizer hN in
private theorem kernelMap_kernel_nontrivial : Nontrivial (kernelMap top N).ker := by
  obtain ⟨n,hn,hnot⟩ := Set.not_subset.mp hN
  have hex : ∃ k : top.ker, n * k ≠ k * n := by
    by_contra hh
    apply hnot
    apply hcentralizer n
    intro k
    exact not_ne_iff.mp (not_exists.mp hh k)
  obtain ⟨k,hk⟩ := hex
  let c : G := n * k * n⁻¹ * (k : G)⁻¹
  have hcN : c ∈ N := by
    simpa only [c,mul_assoc] using
      N.mul_mem hn ((inferInstance : N.Normal).conj_mem n⁻¹ (N.inv_mem hn) k)
  have hcK : c ∈ top.ker := by
    simp [c,MonoidHom.mem_ker,map_mul,map_inv,MonoidHom.mem_ker.mp k.2]
  have hcne : c ≠ 1 := by
    intro hc
    exact hk (commutatorElement_eq_one_iff_mul_comm.mp hc)
  let z : (kernelMap top N).ker := ⟨⟨c,hcK⟩,by
    rw [MonoidHom.mem_ker]
    exact (QuotientGroup.eq_one_iff c).mpr hcN⟩
  exact ⟨⟨z,1,by
    intro hz
    exact hcne (congrArg (fun x : (kernelMap top N).ker => ((x : top.ker) : G)) hz)⟩⟩

/-- The original quotient is binary of order at most32. -/
def certificate : PreE7B6QuotientCertificate (G ⧸ N) := by
  have hs := kernelMap_surjective top N hN
  have hp : IsPGroup 2 (G ⧸ N) := hbinary.of_surjective (kernelMap top N) hs
  have hc : Nat.card (G ⧸ N) ≤ 32 := by
    letI := kernelMap_kernel_nontrivial top hcentralizer N hN
    have hk : 2 ≤ Nat.card (kernelMap top N).ker := by
      have hh := Finite.one_lt_card_iff_nontrivial.mpr
        (inferInstance : Nontrivial (kernelMap top N).ker)
      omega
    have he := Subgroup.card_eq_card_quotient_mul_card_subgroup (kernelMap top N).ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
      (kernelMap top N) hs).toEquiv] at he
    have hqpos : 0 < Nat.card (G ⧸ N) := Nat.card_pos
    nlinarith
  exact .binary hp hc

end CubicOutsideKernelBinaryQuotient
end SymmetricSubgroupAsymptotics
end
