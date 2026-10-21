import SymmetricSubgroupAsymptotics.BinaryExcessProposition53Proof
import SymmetricSubgroupAsymptotics.BinaryProperNormalGapAbelianization
import SymmetricSubgroupAsymptotics.PGroupRankPreservingKernelCommutator

/-! The proved binary excess classification supplies a strict original
proper-normal rank gap in EVERY excess-one degree. Hence the full original
abelianization is elementary, and a SAME rank-preserving denominator is
derived, without computational abelianization tests in degree16 or32. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics
open MarkedC4 MarkedC4.RDTExcessStructure
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- This consumes only the proved exact h53 theorem, not a new input. -/
theorem binary_excess_one_abelianization_exponent
    (n : ℕ) (G : Subgroup (Equiv.Perm (Fin n))) (hn : 2<n)
    (hG : IsPGroup 2 G) (htrans : ∀ x y : Fin n,∃ g : G,g.val x=y)
    (hexcess : HasExcess G n 1) : ∀ a : Abelianization G, a^2=1 := by
  obtain ⟨V,hV,hv⟩ := hexcess.1
  have hhigh : (n : ℝ)/4<(normalGen V : ℝ) := by
    norm_num at hv
    linarith
  obtain ⟨i,hi,hexcessi,_,honly,_⟩ := publishedProposition53Binary_proved
    n G hn hG htrans ⟨V,hV,hhigh⟩
  have hi1 : i=1 := by
    rcases hi with hi | hi
    · exact hi
    · obtain ⟨W,hW,hw⟩ := hexcessi.1
      have hb := hexcess.2 W hW
      rw [hi] at hw
      norm_num at hw hb
      linarith
  subst i
  letI := hV
  have hVtop : V=⊤ := honly rfl V hV hhigh
  letI : Group.IsNilpotent G := hG.isNilpotent
  rw [hVtop,MarkedC4.ActualExcessOneQuotientRank.normalGen_top_eq_genRank G] at hv
  apply binary_abelianization_exponent_of_strict_proper_normal_gap hG
  intro N hN hproper
  have hb : (normalGen N : ℝ)≤(n : ℝ)/4 := by
    by_contra h
    exact hproper (honly rfl N hN (lt_of_not_ge h))
  have hlt : (normalGen N : ℝ)<(genRank G : ℝ) := by
    norm_num at hv
    linarith
  exact_mod_cast hlt

/-- The source subgroup and original normal denominator are unchanged. -/
theorem binary_excess_one_rank_preserving_denominator_le_commutator
    (n : ℕ) (G : Subgroup (Equiv.Perm (Fin n))) (hn : 2<n)
    (hG : IsPGroup 2 G) (htrans : ∀ x y : Fin n,∃ g : G,g.val x=y)
    (hexcess : HasExcess G n 1) (N : Subgroup G) [N.Normal]
    (hrank : genRank (G ⧸ N)=genRank G) : N≤commutator G := by
  have hk := pGroup_kernel_le_commutator_of_rank_preserving_abelianization_exponent
    2 hG (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
    (binary_excess_one_abelianization_exponent n G hn hG htrans hexcess) hrank
  simpa only [QuotientGroup.ker_mk'] using hk

end SymmetricSubgroupAsymptotics
