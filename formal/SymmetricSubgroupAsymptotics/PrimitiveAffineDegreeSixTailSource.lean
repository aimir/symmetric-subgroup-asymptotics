import SymmetricSubgroupAsymptotics.C3DegreeSixAlignedLocal
import SymmetricSubgroupAsymptotics.Non2PreE7UniformQuotientTailSource
import SymmetricSubgroupAsymptotics.Non2PreE7SmallModelNumerics
import SymmetricSubgroupAsymptotics.FiniteGroupPaddedGenerators

/-!
# A complete cold source for aligned degree-six actions

The degree-six structural dichotomy gives a `2^(8b/15)` estimate on every
literal quotient.  Here its finite constants are bounded uniformly, summed
over the original normal menu, and installed through the complete cold-tail
constructor.  This is the numerical row needed by exceptional affine block
systems whose ambient action has degree six.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

/-- A finite group of order at most `2^l` has at most `2^(l^2)`
automorphisms. -/
theorem mulEquiv_card_le_two_pow_sq_of_order
    {G : Type*} [Group G] [Finite G] (l : ℕ)
    (horder : Nat.card G ≤ 2 ^ l) :
    Nat.card (G ≃* G) ≤ 2 ^ (l * l) := by
  calc
    Nat.card (G ≃* G) ≤ Nat.card G ^ Nat.log 2 (Nat.card G) :=
      Non2UnipotentPrefixFiniteMenu.mulEquiv_card_le_card_pow_log G
    _ ≤ (2 ^ l) ^ Nat.log 2 (Nat.card G) :=
      Nat.pow_le_pow_left horder _
    _ ≤ (2 ^ l) ^ l := by
      apply Nat.pow_le_pow_right (by positivity)
      exact (Nat.log_mono_right (b := 2) horder).trans_eq
        (Nat.log_pow (by norm_num) l)
    _ = 2 ^ (l * l) := by rw [pow_mul]

/-- Every degree-six permutation subgroup and each of its quotients has
order at most `2^10`. -/
theorem degreeSix_subgroup_and_quotient_order_le
    (U : Subgroup (Equiv.Perm (Fin 6)))
    (N : Subgroup U) [N.Normal] :
    Nat.card U ≤ 2 ^ 10 ∧ Nat.card (U ⧸ N) ≤ 2 ^ 10 := by
  have hU720 : Nat.card U ≤ 720 := by
    have h := Subgroup.card_le_card_group U
    rw [Nat.card_perm, Nat.card_fin] at h
    norm_num at h
    rw [Nat.card_eq_fintype_card]
    exact h
  have hU : Nat.card U ≤ 2 ^ 10 := hU720.trans (by norm_num)
  refine ⟨hU, ?_⟩
  exact (Nat.card_le_card_of_surjective (QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N)).trans hU

/-- Explicit finite constant for every quotient in the aligned degree-six
dichotomy.  The generous power of two is chosen so its complete normal menu
fits the standard width-six coefficient budget without case arithmetic. -/
theorem degreeSix_alignedAction_uniformQuotientBound
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (hKP : KovacsPraegerAbelianizationBound)
    (U : Subgroup (Equiv.Perm (Fin 6))) [MulAction.IsPretransitive U (Fin 6)]
    (hU : C3HighAlignedAction U)
    (N : Subgroup U) [N.Normal]
    (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J (U ⧸ N)) : ℝ) ≤
      (2 : ℝ) ^ (102 : ℕ) * (2 : ℝ) ^ ((8 / 15 : ℝ) * b) := by
  obtain ⟨N0, hN0, hHigh, _⟩ := hU
  letI := hN0
  have hHigh' : 3 * Nat.card (Fin 6) <
      20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N0) := by
    simpa using hHigh
  have hUorder := (degreeSix_subgroup_and_quotient_order_le U N).1
  have hQorder := (degreeSix_subgroup_and_quotient_order_le U N).2
  have hAutU : Nat.card (U ≃* U) ≤ 2 ^ 100 := by
    simpa using mulEquiv_card_le_two_pow_sq_of_order 10 hUorder
  have hAutQ : Nat.card ((U ⧸ N) ≃* (U ⧸ N)) ≤ 2 ^ 100 := by
    simpa using mulEquiv_card_le_two_pow_sq_of_order 10 hQorder
  rcases degreeSix_high_oddIndexOwner_or_binaryBlock hPrimitive
      (A := U) (Ω := Fin 6) N0 (by simp) hHigh' with hOdd |
      ⟨omega0, D, hFibre, hPoints⟩
  · obtain ⟨W⟩ := hOdd
    have hbound := W.quotientEpimorphism_bound hKP (by simp) N b J
    apply hbound.trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have hsum : Nat.card (U ≃* U) + Nat.card ((U ⧸ N) ≃* (U ⧸ N)) + 1 ≤
        2 ^ 102 := by omega
    exact_mod_cast hsum
  · let points : D.Points ≃ Fin 3 := Finite.equivFinOfCardEq hPoints
    let F := D.binaryBlockFrame hFibre points
    have hTop : Nat.card F.top.range = 3 :=
      D.binaryBlockFrame_top_card N0 hFibre hPoints hHigh' points
    obtain ⟨B⟩ := F.blockCoordinates_nonempty hTop
    let e := D.originalPermutationEquiv
    let M : Subgroup D.originalPermutationImage := N.map e.toMonoidHom
    haveI hM : M.Normal := Subgroup.Normal.map (show N.Normal from inferInstance)
      e.toMonoidHom e.surjective
    have hcongr : Nat.card (GroupEpimorphism J (U ⧸ N)) =
        Nat.card (GroupEpimorphism J (D.originalPermutationImage ⧸ M)) :=
      fusionGroupEpimorphism_card_congr (MulEquiv.refl J)
        (QuotientGroup.congr N M e rfl)
    have hbound := B.quotientEpimorphism_bound M hKP b J
    rw [hcongr]
    apply hbound.trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have hcardQ : Nat.card (D.originalPermutationImage ⧸ M) ≤ 2 ^ 10 := by
      rw [← Nat.card_congr (QuotientGroup.congr N M e rfl).toEquiv]
      exact hQorder
    have hAut : Nat.card ((D.originalPermutationImage ⧸ M) ≃*
        (D.originalPermutationImage ⧸ M)) ≤ 2 ^ 100 := by
      simpa using mulEquiv_card_le_two_pow_sq_of_order 10 hcardQ
    have hsum : Nat.card ((D.originalPermutationImage ⧸ M) ≃*
        (D.originalPermutationImage ⧸ M)) + 1 ≤ 2 ^ 102 := by omega
    exact_mod_cast hsum

namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineDegreeSixTailSource

variable (hPrimitive : PrimitiveTernaryStrictHeadBound)
  (hKP : KovacsPraegerAbelianizationBound)
  (U : PreE7NonPairActionClass 6)
  (hU : C3HighAlignedAction (preE7NonPairAction 6 U))

/-- The common cold exponent fits the width-six pre-E7 window. -/
theorem theta_window :
    (8 / 15 : ℝ) ≤ preE7CharacterWindow 6 := by
  norm_num [preE7CharacterWindow, preE7CharacterRho, halfDegree]

/-- The constant `2^102` on every literal normal axis has total at most
`2^202`. -/
theorem coefficient_total_le :
    fusionAxisEnvelopeTotal (preE7NonPairAction 6 U)
        (fun _ => (2 : ℝ) ^ (102 : ℕ)) ≤
      (2 : ℝ) ^ (202 : ℕ) := by
  have horder : Nat.card (preE7NonPairAction 6 U) ≤ 2 ^ 10 := by
    have h := Subgroup.card_le_card_group (preE7NonPairAction 6 U)
    have h720 : Nat.card (preE7NonPairAction 6 U) ≤ 720 := by
      rw [Nat.card_perm, Nat.card_fin] at h
      norm_num at h
      rw [Nat.card_eq_fintype_card]
      exact h
    exact h720.trans (by norm_num)
  have hnormal : Nat.card
      {N : Subgroup (preE7NonPairAction 6 U) // N.Normal} ≤ 2 ^ 100 := by
    simpa using normalSubgroup_card_le_two_pow_sq 10 horder
  have hmenuNat : Nat.card
      {N : Subgroup (preE7NonPairAction 6 U) // N.Normal} * 2 ^ 102 ≤
      2 ^ 202 := by
    calc
      Nat.card {N : Subgroup (preE7NonPairAction 6 U) // N.Normal} * 2 ^ 102 ≤
          2 ^ 100 * 2 ^ 102 := Nat.mul_le_mul_right _ hnormal
      _ = 2 ^ 202 := by rw [← pow_add]
  calc
    fusionAxisEnvelopeTotal (preE7NonPairAction 6 U)
        (fun _ => (2 : ℝ) ^ (102 : ℕ)) =
        (Nat.card
          {N : Subgroup (preE7NonPairAction 6 U) // N.Normal} : ℝ) *
          (2 : ℝ) ^ (102 : ℕ) := by
      simp [fusionAxisEnvelopeTotal, Finset.sum_const, nsmul_eq_mul]
      exact @Fintype.card_congr
        {N : Subgroup (preE7NonPairAction 6 U) // N.Normal}
        {N : Subgroup (preE7NonPairAction 6 U) // N.Normal}
        (Subtype.fintype Subgroup.Normal) originalNormalFintype (Equiv.refl _)
    _ ≤ ((2 ^ 202 : ℕ) : ℝ) := by exact_mod_cast hmenuNat
    _ = (2 : ℝ) ^ (202 : ℕ) := by norm_num

include hPrimitive hKP hU in
/-- Complete quotient-tail data for one aligned degree-six action. -/
noncomputable def data :
    PreE7UniformQuotientTailSourceData .acert 6 U where
  width_lower := by norm_num
  theta := 8 / 15
  theta_window := theta_window
  coefficient := fun _ => (2 : ℝ) ^ (102 : ℕ)
  coefficient_nonneg := fun _ => by positivity
  quotient_bound := by
    intro N b J
    letI : MulAction.IsPretransitive
        (preE7NonPairAction 6 U) (Fin 6) :=
      Non2TransitiveActionClass.representative_pretransitive U.1.1
    exact degreeSix_alignedAction_uniformQuotientBound hPrimitive hKP
      (preE7NonPairAction 6 U) hU N.1 b J
  coefficient_total_bound := by
    intro b
    calc
      fusionAxisEnvelopeTotal (preE7NonPairAction 6 U)
          (fun _ => (2 : ℝ) ^ (102 : ℕ)) ≤
          (2 : ℝ) ^ (202 : ℕ) := coefficient_total_le U
      _ = Real.rpow (2 : ℝ) (202 : ℝ) := by
        simp
      _ ≤ Real.rpow (2 : ℝ) (36 * (6 : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        norm_num
      _ ≤ _ := two_rpow_thirtySix_width_le_menuMass
        (w := 6) (by norm_num) b

include hPrimitive hKP hU in
/-- Final rank-tail source for the aligned degree-six ambient action. -/
noncomputable def source : PreE7RankTailSourceOrYonedaTopData 6 U :=
  (data hPrimitive hKP U hU).toRankTailSourceOrYonedaTop

end PrimitiveAffineDegreeSixTailSource
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
