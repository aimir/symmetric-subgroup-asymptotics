import SymmetricSubgroupAsymptotics.SixPairNonbinaryTopKernelEnvelope
import SymmetricSubgroupAsymptotics.SixPairOriginalBinaryDualSections
import SymmetricSubgroupAsymptotics.TransitiveSixBinaryNaturalUniform
import SymmetricSubgroupAsymptotics.SixPairOriginalBinaryQuotientCard
import SymmetricSubgroupAsymptotics.OriginalKernelNonbinaryResidual
import SymmetricSubgroupAsymptotics.BinaryTargetRankTailSum
import SymmetricSubgroupAsymptotics.BinaryPairKernelCard

/-! Complete source sums over every original normal quotient of a
six-pair action. A binary quotient has order at most 32; a nonbinary
quotient retains a nonbinary quotient of the actual six-point top.
The latter's socle-one property is a structural lemma, supplied separately
by the actual block geometry. No original denominator is restricted to
lie inside the pair kernel. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.SixPairActualNonbinaryTopQuotientSum
open Non2UnipotentPrefixFiniteMenu OriginalKernelModuleChart

variable {U : Subgroup (Equiv.Perm (Fin 12))}
    [MulAction.IsPretransitive U (Fin 12)] (F : BinaryPairFrame U (Fin 6))

omit [MulAction.IsPretransitive U (Fin 12)] in
theorem top_order_le : Nat.card F.top.range ≤ 720 := by
  have h := Nat.card_le_card_of_injective
    (Subtype.val : F.top.range → Equiv.Perm (Fin 6)) Subtype.val_injective
  simpa only [Nat.card_perm,Nat.card_fin] using h

omit [MulAction.IsPretransitive U (Fin 12)] in
include F in
theorem original_order_le : Nat.card U ≤ 2^16 := by
  have hk : Nat.card F.kernelSpace ≤ 2^6 := by
    have hh := Nat.card_le_card_of_injective
      (Subtype.val : F.kernelSpace → (Fin 6 → ZMod 2)) Subtype.val_injective
    have hf : Nat.card (Fin 6 → ZMod 2)=2^6 := by
      rw [Nat.card_fun,Nat.card_fin,Nat.card_eq_fintype_card (α := ZMod 2),ZMod.card]
    rwa [hf] at hh
  rw [←F.kernelSpace_card_mul_top]
  exact (Nat.mul_le_mul hk (top_order_le F)).trans (by norm_num)

include F in
theorem quotient_sum_le
    (hsocle : ∀ (M : Subgroup F.top.range) [M.Normal],
      ¬IsPGroup 2 (F.top.range ⧸ M) → SocleNormalGeneratorBound (F.top.range ⧸ M) 1)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (N : Subgroup U) [N.Normal] (b : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)),(Nat.card (GroupEpimorphism J (U ⧸ N)) : ℝ)) ≤
      BinaryKernelRankTailNumerics.raw 1 736 b+
        (subgroupCount b : ℝ)*((2 : ℝ)^(234 : ℕ)*(2 : ℝ)^((43/30 : ℝ)*b)) := by
  by_cases hb : IsPGroup 2 (U ⧸ N)
  · obtain ⟨r,hr⟩ := hb.exists_card_eq
    have hp : 2^r≤2^5 := by
      rw [←hr]
      exact F.original_binary_quotient_card_le_thirtyTwo N hb
    have hrank : r≤5 := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp hp
    apply (BinaryTargetRankTailSum.full_sum_le 5 r hrank hr b).trans
    apply add_le_add
    · unfold BinaryKernelRankTailNumerics.raw
      simp only [one_mul]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact pow_le_pow_right₀ (by exact_mod_cast Nat.succ_le_iff.mpr (Nat.factorial_pos b))
        (by decide : 5≤736)
    · apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hp : (2 : ℝ)^(((5 : ℝ)*(51/200))*b) ≤ (2 : ℝ)^((43/30 : ℝ)*b) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (mul_le_mul_of_nonneg_right (by norm_num : (5 : ℝ)*(51/200)≤43/30) (Nat.cast_nonneg b))
      exact hp.trans (le_mul_of_one_le_left (by positivity)
        (one_le_pow₀ (by norm_num : (1 : ℝ)≤2)))
  · let pi := F.top.rangeRestrict
    let A := SixPairPrimitiveAllNormalB6.kernelModule F
    let E := SixPairPrimitiveAllNormalB6.originalKernelChart F
    have hpi : Function.Surjective pi := F.top.rangeRestrict_surjective
    have ht : Function.Surjective (sectionTop pi N hpi) := by
      intro q
      obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (pi.ker ⊔ N) q
      exact ⟨pi g,sectionTop_apply pi N hpi g⟩
    let e := QuotientGroup.quotientKerEquivOfSurjective (sectionTop pi N hpi) ht
    have hR : ¬IsPGroup 2 (U ⧸ (pi.ker ⊔ N)) := by
      intro h
      exact hb ((E.quotientChart pi A N).isPGroup_two_of_base
        (base pi N) (E.sectionRepresentation pi A N) h)
    have hs : SocleNormalGeneratorBound (U ⧸ (pi.ker ⊔ N)) 1 :=
      CyclicSocleQuotientTools.socleBound_equiv e
        (hsocle (sectionTop pi N hpi).ker (fun h => hR (h.of_equiv e)))
    letI : MulAction.IsPretransitive F.top.range (Fin 6) := F.top_pretransitive
    have hu := transitiveSix_binary_natural_uniform_two (G := F.top.range)
    have hg := SixPairOriginalBinaryDualSections.dual_generated F hu N
    have hq : Nat.card (U ⧸ N) ≤ 2^16 :=
      (Nat.card_le_card_of_surjective (QuotientGroup.mk' N)
        (QuotientGroup.mk'_surjective N)).trans (original_order_le F)
    have htop : Nat.card (U ⧸ (pi.ker ⊔ N)) ≤ 720 :=
      (Nat.card_le_card_of_surjective (sectionTop pi N hpi) ht).trans (top_order_le F)
    exact SixPairNonbinaryTopKernelEnvelope.raw_sum_le
      (base pi N) (base_surjective pi N) (E.sectionRepresentation pi A N)
      (E.quotientChart pi A N) hg hq htop hs hZmud lit b

end SymmetricSubgroupAsymptotics.SixPairActualNonbinaryTopQuotientSum
