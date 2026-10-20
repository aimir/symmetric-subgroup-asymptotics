import SymmetricSubgroupAsymptotics.BinaryTransitiveNormalQuarterPlusTwo
import SymmetricSubgroupAsymptotics.PGroupNormalGeneratorCharacterEquality
import SymmetricSubgroupAsymptotics.PermutationAbelianQuotientOrderBoundPGroup

/-! The full abelianization, including higher binary cyclic factors, has
the same universal excess-two order ceiling. Only the actual exponent-two
pair kernel is replaced by its relative head. The smaller original top's
full abelianization order is retained throughout. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

namespace BinaryPairFrame

/-- The full original abelianization order across an actual pair frame.
There is no elementary-exponent hypothesis on the original abelianization. -/
theorem abelianization_card_le_actual_kernel_normalGen
    {X I : Type} [Finite X] [Finite I]
    {U : Subgroup (Equiv.Perm X)} (F : BinaryPairFrame U I) (hU : IsPGroup 2 U) :
    Nat.card (Abelianization U) ≤ 2 ^ MarkedC4.normalGen F.top.ker *
      Nat.card (Abelianization F.top.range) := by
  letI := Fintype.ofFinite I
  have hker : F.top.rangeRestrict.ker = F.top.ker := MonoidHom.ker_rangeRestrict F.top
  have hpow (k : F.top.rangeRestrict.ker) : (k : U) ^ 2 = 1 := by
    let a : F.top.ker := ⟨k, by rw [← hker]; exact k.property⟩
    have ha : a ^ 2 = 1 := by
      apply F.kernelChart.injective
      rw [map_pow, map_one]
      change (2 : ℕ) • (F.kernelChart a).toAdd = 0
      rw [← Nat.cast_smul_eq_nsmul (ZMod 2), ZMod.natCast_self, zero_smul]
    exact congrArg Subtype.val ha
  have hext := PermutationAbelianQuotientOrderBound.abelianization_card_elementary_kernel
    2 F.top.rangeRestrict F.top.rangeRestrict_surjective hpow
  rw [← pGroup_normalGen_eq_primeRelativeHead 2 hU F.top.rangeRestrict.ker, hker] at hext
  exact hext

end BinaryPairFrame

/-- The full original transitive binary abelianization has order at most
2^(floor(degree/4)+2), without any exponent-two or finite-census premise. -/
theorem twoGroup_transitive_abelianization_card_le_quarter_add_two
    {X : Type} [Finite X] (U : Subgroup (Equiv.Perm X))
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U) :
    Nat.card (Abelianization U) ≤ 2 ^ (Nat.card X / 4 + 2) := by
  suffices hh : ∀ n (X : Type) [Finite X] (U : Subgroup (Equiv.Perm X))
      [MulAction.IsPretransitive U X], IsPGroup 2 U → Nat.card X = n →
      Nat.card (Abelianization U) ≤ 2 ^ (Nat.card X / 4 + 2) from hh _ X U hU rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro X _ U _ hU hn
    by_cases hsmall : Nat.card X ≤ 8
    · exact (PermutationAbelianQuotientOrderBound.pGroup_abelianization_card_le 2 U X hU).trans
        (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))
    · letI : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by omega)
      let x : X := Classical.choice inferInstance
      obtain ⟨D⟩ := transitiveBinaryPairCover_nonempty U hU x
      have hact : ∀ (u : U) (i : D.Points), u • i = D.frame.top u i := fun _ _ => rfl
      have hdegree := D.degree_product
      letI := D.top_pretransitive
      have hext := D.frame.abelianization_card_le_actual_kernel_normalGen hU
      by_cases hel : BinarySquareActionStructure.SquaresActTrivially (G := U) (X := D.Points)
      · obtain ⟨s⟩ := pGroup_primeIndexSubgroupChain_exists hU
          (MulAction.stabilizer U D.base) ⊤ le_top
        have hcard : Nat.card D.Points = 2 ^ s.length := by
          simpa only [Subgroup.relIndex_top_right,
            MulAction.index_stabilizer_of_transitive U D.base] using s.relIndex
        have htopel : BinarySquareActionStructure.SquaresActTrivially
            (G := D.Top) (X := D.Points) := by
          intro a i
          obtain ⟨u, rfl⟩ := D.frame.top.rangeRestrict_surjective a
          change (D.frame.top.rangeRestrict u) ^ 2 • i = i
          rw [← map_pow]
          exact hel u i
        have htopcard : Nat.card D.Top = 2 ^ s.length :=
          (ElementaryBinaryTransitiveNormalRank.card_eq_degree htopel D.base).trans hcard
        have htopab : Nat.card (Abelianization D.Top) ≤ 2 ^ s.length :=
          (Nat.card_le_card_of_surjective (QuotientGroup.mk' (commutator D.Top))
            (QuotientGroup.mk'_surjective (commutator D.Top))).trans_eq htopcard
        have hu : UniformSubrepresentationGeneratorBound
            (permutationFunctionRepresentation (ZMod 2) U D.Points)
              (s.length.choose (s.length / 2)) := by
          letI := Fintype.ofFinite D.Points
          apply pGroup_uniformSubrepresentationGeneratorBound_of_head_le hU
          intro M
          exact twoGroup_permutationSubrepresentationHead_le_width hU s.length hcard D.base M
        have hkernel := D.frame.normalGen_le_of_uniform_pair_module hact _ hu D.frame.top.ker le_rfl
        have hk : 3 ≤ s.length := by
          by_contra he
          have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : s.length ≤ 2)
          rw [← hcard] at hp
          norm_num at hp
          omega
        have hcapacity : s.length.choose (s.length / 2) + s.length ≤ Nat.card X / 4 + 2 := by
          by_cases hwide : 5 ≤ s.length
          · have hb := binary_middle_add_rank_le_half_power s.length hwide
            have hp : 2 ^ s.length = 2 * 2 ^ (s.length - 1) := by
              conv_lhs => rw [show s.length = (s.length - 1) + 1 by omega]
              rw [pow_succ]
              exact Nat.mul_comm _ _
            rw [← hcard] at hp
            omega
          · have hs : s.length = 3 ∨ s.length = 4 := by omega
            rcases hs with hs | hs <;> rw [hs] at hcard ⊢ <;>
              norm_num [Nat.choose] at hcard ⊢ <;> omega
        exact hext.trans ((Nat.mul_le_mul
          (Nat.pow_le_pow_right (by decide : 0 < 2) hkernel) htopab).trans
            ((pow_add 2 _ _).symm.le.trans
              (Nat.pow_le_pow_right (by decide : 0 < 2) hcapacity)))
      · have hkernel := D.frame.normalGen_le_quarter_of_not_elementary hact hU hel
          D.frame.top.ker le_rfl
        have htop := ih (Nat.card D.Points) (by have := D.points_card_lt; omega)
          D.Points D.Top (D.top_isPGroup hU) rfl
        have hcapacity : Nat.card D.Points / 4 + (Nat.card D.Points / 4 + 2) ≤
            Nat.card X / 4 + 2 := by omega
        exact hext.trans ((Nat.mul_le_mul
          (Nat.pow_le_pow_right (by decide : 0 < 2) hkernel) htop).trans
            ((pow_add 2 _ _).symm.le.trans
              (Nat.pow_le_pow_right (by decide : 0 < 2) hcapacity)))

end SymmetricSubgroupAsymptotics
