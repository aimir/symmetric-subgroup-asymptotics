import SymmetricSubgroupAsymptotics.SevenPointSimpleSylowNormalizerExact
import SymmetricSubgroupAsymptotics.PerfectSmallPermutationEmbedding
import SymmetricSubgroupAsymptotics.CFSGOddOrderSolvabilityComplete

/-! Exact elementary order alternative for an actual transitive simple
seven-point source. The sole CFSG use excludes the odd order315 case by
the now proved odd-order theorem. No model identification is supplied. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SevenPointTransitiveSimpleOrderDichotomy
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
private theorem divisor_receipt : ∀ k : Fin 121, k.val ∣ 120 → k.val % 7=1 →
    k.val=1 ∨ k.val=8 ∨ k.val=15 ∨ k.val=120 := by decide +kernel

theorem card_eq_168_or_2520 (hCFSG : CFSG.CFSGClassification)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    [MulAction G (Fin 7)] [FaithfulSMul G (Fin 7)]
    [MulAction.IsPretransitive G (Fin 7)] (hn : ¬IsMulCommutative G) :
    Nat.card G=168 ∨ Nat.card G=2520 := by
  letI : Group.IsPerfect G := simple_perfect_of_nonabelian hn
  let j := perfectPermutationToAlternating (MulAction.toPermHom G (Fin 7))
  have hj : Function.Injective j := perfectPermutationToAlternating_injective _
    (show Function.Injective (MulAction.toPermHom G (Fin 7)) from MulAction.toPerm_injective)
  have hd : Nat.card G ∣ 2520 := by
    have hh := Subgroup.card_dvd_of_injective j hj
    simpa only [nat_card_alternatingGroup,Nat.card_fin] using hh
  have hseven : 7 ∣ Nat.card G := by
    have hi : Nat.card (Fin 7) ∣ Nat.card G := by
      rw [←MulAction.index_stabilizer_of_transitive G (0 : Fin 7)]
      exact Subgroup.index_dvd_card _
    simpa only [Nat.card_fin] using hi
  have hval : (Nat.card G).factorization 7=1 := by
    have hhi := (Nat.factorization_le_iff_dvd Nat.card_pos.ne' (by decide : 2520 ≠ 0)).mpr hd 7
    have hlo := (Nat.Prime.dvd_iff_one_le_factorization (by decide : Nat.Prime 7) Nat.card_pos.ne').mp hseven
    have he : (2520 : ℕ).factorization 7=1 := by decide +kernel
    rw [he] at hhi
    omega
  let P : Sylow 7 G := Classical.choice inferInstance
  have hP : Nat.card P=7 := by rw [P.card_eq_multiplicity,hval,pow_one]
  have hN := SevenPointSimpleSylowNormalizerExact.normalizer_card_eq_twentyOne hn P hP
  have hm : 21*Nat.card (Sylow 7 G)=Nat.card G := by
    have hh := (Subgroup.normalizer (P : Set G)).card_mul_index
    rw [←P.card_eq_index_normalizer,hN] at hh
    exact hh
  have hdiv : Nat.card (Sylow 7 G) ∣ 120 := by
    apply (Nat.mul_dvd_mul_iff_left (by decide : 0 < 21)).mp
    simpa only [hm,show 21*120=2520 by decide] using hd
  have hmod : Nat.card (Sylow 7 G)%7=1 := by
    have hh := card_sylow_modEq_one 7 G
    change Nat.card (Sylow 7 G)%7=1%7 at hh
    simpa only [show 1%7=1 by decide] using hh
  have hle := Nat.le_of_dvd (by decide : 0 < 120) hdiv
  have hge := SimplePrimeSylowSuccessorIndexSquare.sylow_count_ge_prime_succ hn P hP
  rcases divisor_receipt ⟨Nat.card (Sylow 7 G),by omega⟩ hdiv hmod with h1 | h8 | h15 | h120
  · change Nat.card (Sylow 7 G) = 1 at h1
    omega
  · change Nat.card (Sylow 7 G) = 8 at h8
    exact Or.inl (by rw [←hm,h8])
  · change Nat.card (Sylow 7 G) = 15 at h15
    have ho : Nat.card G=315 := by rw [←hm,h15]
    letI : IsSolvable G := CFSGReduction.odd_order_solvable_of_cfsg hCFSG G
      (by rw [ho]; decide)
    exact (hn (isMulCommutative_iff.mpr (IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance))).elim
  · change Nat.card (Sylow 7 G) = 120 at h120
    exact Or.inr (by rw [←hm,h120])

end SymmetricSubgroupAsymptotics.SevenPointTransitiveSimpleOrderDichotomy
