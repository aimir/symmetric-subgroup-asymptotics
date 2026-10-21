import SymmetricSubgroupAsymptotics.PGroupGeneratorAbelianizationOrder
import SymmetricSubgroupAsymptotics.NormalFEquivalenceTransport
import SymmetricSubgroupAsymptotics.RDTDegreeEightExceptionalTransport
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import SymmetricSubgroupAsymptotics.TransitiveNonabelianCenterBound

/-! Generic small-order normal-F bounds, without a carrier catalogue.
The original quotient rank is retained in the abelianization estimate. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SmallBinaryNormalFBounds
open MarkedC4 MarkedC4.ActualNormalFMarkedPeel MarkedC4.RDTNormalFInterface
variable {G : Type} [Group G] [Finite G]

theorem nonabelian_center_index_four_le (hnonab : ¬∀ a b : G,a*b=b*a) :
    4≤(Subgroup.center G).index := by
  by_contra hnot
  let Z := Subgroup.center G
  have hcard : Nat.card (G ⧸ Z)≤3 := by
    change Z.index≤3
    dsimp [Z]
    omega
  have hpos : 0<Nat.card (G ⧸ Z) := Nat.card_pos
  haveI : IsCyclic (G ⧸ Z) := by
    have hc : Nat.card (G ⧸ Z)=1 ∨ Nat.card (G ⧸ Z)=2 ∨ Nat.card (G ⧸ Z)=3 := by omega
    rcases hc with hc | hc | hc
    · letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact isCyclic_of_card_dvd_prime (p := 2) (by simpa only [hc] using (one_dvd (2 : ℕ)))
    · letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact isCyclic_of_card_dvd_prime (p := 2) (by simpa only [hc] using (dvd_refl (2 : ℕ)))
    · letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact isCyclic_of_card_dvd_prime (p := 3) (by simpa only [hc] using (dvd_refl (3 : ℕ)))
  apply hnonab
  exact commutative_of_cyclic_center_quotient (QuotientGroup.mk' Z) (by
    intro x hx
    exact (QuotientGroup.eq_one_iff x).mp hx)

theorem center_card_le_four_of_card_le_sixteen
    (hcard : Nat.card G≤16) (hnonab : ¬∀ a b : G,a*b=b*a) :
    Nat.card (Subgroup.center G)≤4 := by
  have hi := nonabelian_center_index_four_le hnonab
  have hf := (Subgroup.center G).card_mul_index
  nlinarith

theorem transitive_eight_center_card_le_four
    {X : Type} [MulAction G X] [FaithfulSMul G X]
    [MulAction.IsPretransitive G X] [Finite X]
    (hG : IsPGroup 2 G) (hX : Nat.card X=8)
    (hnonab : ¬∀ a b : G,a*b=b*a) :
    Nat.card (Subgroup.center G)≤4 := by
  have hx : Nonempty X := (Nat.card_pos_iff.mp (by omega : 0<Nat.card X)).1
  obtain ⟨x⟩ := hx
  have hlt := transitive_nonabelian_center_card_lt x hnonab
  rw [hX] at hlt
  obtain ⟨k,hk⟩ := (hG.to_subgroup (Subgroup.center G)).exists_card_eq
  rw [hk] at hlt ⊢
  have hsmall : k<3 := by
    by_contra hnot
    have hb := Nat.pow_le_pow_right (by decide : 0<2) (by omega : 3≤k)
    norm_num at hb
    omega
  interval_cases k <;> norm_num

theorem commutator_card_le_four_of_rank_three
    (hG : IsPGroup 2 G) (hcard : Nat.card G≤32) (hrank : 3≤genRank G) :
    Nat.card (commutator G)≤4 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpow : 8≤2^genRank G := Nat.pow_le_pow_right (by decide : 0<(2 : ℕ)) hrank
  have hab := pGroup_pow_genRank_le_abelianization_card 2 hG
  have hf := (commutator G).card_eq_card_quotient_mul_card_subgroup
  change Nat.card G=Nat.card (Abelianization G)*Nat.card (commutator G) at hf
  nlinarith

theorem top_log_bounds_of_card_bounds
    (hc : Nat.card (commutator G)≤4) (hz : Nat.card (Subgroup.center G)≤4) :
    commutatorLog (⊤ : Subgroup G)+centralLog (⊤ : Subgroup G)≤4 ∧
      centralLog (⊤ : Subgroup G)≤2 := by
  have hlog (n : ℕ) (hn : 0<n) (hfour : n≤4) : Real.logb 2 (n : ℝ)≤2 := by
    apply (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ)<2)
      (by exact_mod_cast hn)).mpr
    norm_num
    exact_mod_cast hfour
  have hd := hlog _ (Nat.card_pos (α := commutator G)) hc
  have hcen := hlog _ (Nat.card_pos (α := Subgroup.center G)) hz
  have hc' : commutatorLog (⊤ : Subgroup G)≤2 := hd
  have hz' : centralLog (⊤ : Subgroup G)≤2 := by
    simpa only [centralLog,targetCentralizer,Subgroup.coe_top,Subgroup.centralizer_univ] using hcen
  exact ⟨by linarith,hz'⟩

theorem quotient_top_log_bounds
    (hG : IsPGroup 2 G) (hcard : Nat.card G≤32)
    (hcenter : Nat.card (Subgroup.center G)≤4)
    (N : Subgroup G) [N.Normal] (hrank : 3≤genRank (G ⧸ N))
    (hnonab : ¬∀ a b : G ⧸ N,a*b=b*a) :
    commutatorLog (⊤ : Subgroup (G ⧸ N))+centralLog (⊤ : Subgroup (G ⧸ N))≤4 ∧
      centralLog (⊤ : Subgroup (G ⧸ N))≤2 := by
  have hquot : Nat.card (G ⧸ N)≤Nat.card G :=
    Nat.le_of_dvd (Nat.card_pos (α := G)) N.index_dvd_card
  apply top_log_bounds_of_card_bounds
  · exact commutator_card_le_four_of_rank_three (hG.to_quotient N) (hquot.trans hcard) hrank
  · by_cases hN : N=⊥
    · subst N
      rwa [←Nat.card_congr (RDTDegreeEightExceptionalTransport.centerEquiv
        (QuotientGroup.quotientBot : G ⧸ (⊥ : Subgroup G) ≃* G)).toEquiv] at hcenter
    · have hNcard : 2≤Nat.card N := ((N.one_lt_card_iff_ne_bot).mpr hN)
      have hf := N.card_eq_card_quotient_mul_card_subgroup
      have hsmall : Nat.card (G ⧸ N)≤16 := by nlinarith
      exact center_card_le_four_of_card_le_sixteen hsmall hnonab

end SymmetricSubgroupAsymptotics.SmallBinaryNormalFBounds
