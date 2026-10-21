import SymmetricSubgroupAsymptotics.BinaryPairRankNineSmallDerivedNormalF
import SymmetricSubgroupAsymptotics.PGroupElementaryAbelianizationRank

/-! An actual order-budget consumer for rank-nine degree-thirty-two sources.
The original top has order at most512; an actual source order at most2^19
then gives the required all-denominator normal-F packet. The strict
large-derived branch forces the SAME original kernel to have dimension10.
No finite model or split extension is a premise. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
local instance orderBudgetPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
open MarkedC4.ActualNormalFMarkedPeel
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    [MulAction.IsPretransitive U X] (F : BinaryPairFrame U (Fin 16))
include F

theorem rank_nine_order_budget_all_normal_unit
    (hU : IsPGroup 2 U) (hrank : MarkedC4.genRank U=9)
    (hcard : Nat.card U≤2^19) (htop : Nat.card F.top.range≤512)
    (hnon : ¬∀ t : F.top.range,t^2=1)
    (N : Subgroup U) [N.Normal] (hnonab : ¬∀ a b : U ⧸ N,a*b=b*a) :
    ∃ V : Subgroup (U ⧸ N),V.Normal ∧
      commutatorLog V+centralLog V≤16 ∧ centralLog V≤8 := by
  have hdegree : Nat.card X=32 := by simpa only [Nat.card_fin] using F.card_points
  have hexp := binary_degree_thirty_two_rank_nine_abelianization_exponent U hU hdegree hrank
  have hAb : Nat.card (Abelianization U)=512 := by
    rw [pGroup_abelianization_card_eq_pow_genRank 2 hU hexp,hrank]
    decide
  have hc := (commutator U).card_mul_index
  change Nat.card (commutator U)*Nat.card (Abelianization U)=Nat.card U at hc
  rw [hAb] at hc
  have hd : Nat.card (commutator U)≤1024 := by norm_num at hcard; omega
  apply F.rank_nine_small_derived_all_normal_unit hU hrank hd ?_ hnon N hnonab
  intro hbig
  by_contra hn
  have hk : Module.finrank (ZMod 2) F.kernelSpace≤9 := by omega
  have hK : Nat.card F.kernelSpace≤512 := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F.kernelSpace)
    rw [Nat.card_zmod] at hh
    rw [hh]
    exact (Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) hk).trans_eq (by decide)
  have hu := Nat.mul_le_mul hK htop
  rw [F.kernelSpace_card_mul_top] at hu
  omega

theorem rank_nine_pair_dimension_order_budget_all_normal_unit
    (hU : IsPGroup 2 U) (hrank : MarkedC4.genRank U=9)
    (k h : ℕ) (hK : Module.finrank (ZMod 2) F.kernelSpace≤k)
    (hH : Nat.card F.top.range≤2^h) (hbudget : k+h≤19) (hsmall : h≤9)
    (hnon : ¬∀ t : F.top.range,t^2=1)
    (N : Subgroup U) [N.Normal] (hnonab : ¬∀ a b : U ⧸ N,a*b=b*a) :
    ∃ V : Subgroup (U ⧸ N),V.Normal ∧
      commutatorLog V+centralLog V≤16 ∧ centralLog V≤8 := by
  have hKcard : Nat.card F.kernelSpace≤2^k := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F.kernelSpace)
    rw [Nat.card_zmod] at hh
    rw [hh]
    exact Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) hK
  have hcard : Nat.card U≤2^19 := by
    calc
      _ = Nat.card F.kernelSpace*Nat.card F.top.range := F.kernelSpace_card_mul_top.symm
      _ ≤ 2^k*2^h := Nat.mul_le_mul hKcard hH
      _ = 2^(k+h) := (pow_add _ _ _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) hbudget
  have htop : Nat.card F.top.range≤512 := hH.trans
    ((Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) hsmall).trans_eq (by decide))
  exact F.rank_nine_order_budget_all_normal_unit hU hrank hcard htop hnon N hnonab

end SymmetricSubgroupAsymptotics.BinaryPairFrame
