import SymmetricSubgroupAsymptotics.WidthThirtyTwoFiniteTopBinaryEnvelope
import SymmetricSubgroupAsymptotics.BinaryPairActualKernelDualSections
import SymmetricSubgroupAsymptotics.PermutationFunctionSelfDual
import SymmetricSubgroupAsymptotics.BinaryPairKernelCard
import SymmetricSubgroupAsymptotics.ZmudFaithfulCharacterInput
import SymmetricSubgroupAsymptotics.FusionEpimorphismTransport
import SymmetricSubgroupAsymptotics.CyclicSocleQuotientTools
import SymmetricSubgroupAsymptotics.OriginalKernelNonbinaryResidual
import SymmetricSubgroupAsymptotics.BinaryTargetRankTailSum

/-! Reusable original-axis estimates at width32. Structural callers
must prove their actual top order, natural-module bound and quotient
socle bounds. Both the all-quotients and nonbinary-only variants retain
the same original denominator, including axes outside the pair kernel. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.WidthThirtyTwoActualKernelQuotientSum
open Non2UnipotentPrefixFiniteMenu OriginalKernelModuleChart

theorem ordinary_cost {R : Type} [Group R] [Finite R]
    {k H : ℕ} (hsocle : SocleNormalGeneratorBound R k)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (theta : ℝ) (hslope : (k : ℝ)*(Real.logb 2 5/3)+(51/200 : ℝ)*H≤theta)
    (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J R) : ℝ)*(2 : ℝ)^(((51/200 : ℝ)*H)*b) ≤
      (Nat.card (R ≃* R) : ℝ)*(2 : ℝ)^(theta*b) := by
  have hc : (Nat.card (GroupEpimorphism J R) : ℝ) ≤
      (Nat.card (R ≃* R) : ℝ)*(2 : ℝ)^(((k : ℝ)*(Real.logb 2 5/3))*b) := by
    simpa only [ZmudFaithfulCharacterTupleInput.generalCertificate_slope] using
      (hZmud.generalCertificate hsocle).envelope lit b J
  apply (mul_le_mul_of_nonneg_right hc (by positivity)).trans
  rw [mul_assoc,←Real.rpow_add (by norm_num : (0 : ℝ)<2)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  nlinarith [mul_le_mul_of_nonneg_right hslope (Nat.cast_nonneg (α := ℝ) b)]

variable {U : Subgroup (Equiv.Perm (Fin 32))} (F : BinaryPairFrame U (Fin 16))

include F in
theorem original_order_le (ht : Nat.card F.top.range≤2^32) : Nat.card U≤2^48 := by
  have hk : Nat.card F.kernelSpace≤2^16 := by
    have hh := Nat.card_le_card_of_injective
      (Subtype.val : F.kernelSpace → (Fin 16 → ZMod 2)) Subtype.val_injective
    have hf : Nat.card (Fin 16 → ZMod 2)=2^16 := by
      rw [Nat.card_fun,Nat.card_fin,Nat.card_eq_fintype_card (α := ZMod 2),ZMod.card]
    rwa [hf] at hh
  rw [←F.kernelSpace_card_mul_top]
  exact (Nat.mul_le_mul hk ht).trans_eq (by rw [←pow_add])

include F in
theorem section_sum_le {k H : ℕ}
    (ht : Nat.card F.top.range≤2^32)
    (hu : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) F.top.range (Fin 16)) H)
    (N : Subgroup U) [N.Normal]
    (hsocle : SocleNormalGeneratorBound (U ⧸ (F.top.rangeRestrict.ker ⊔ N)) k)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (theta : ℝ) (hslope : (k : ℝ)*(Real.logb 2 5/3)+(51/200 : ℝ)*H≤theta)
    (b : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)),(Nat.card (GroupEpimorphism J (U ⧸ N)) : ℝ)) ≤
      BinaryKernelRankTailNumerics.raw 1 4294967344 b+
        (subgroupCount b : ℝ)*((2 : ℝ)^(2560 : ℕ)*(2 : ℝ)^(theta*b)) := by
  let pi := F.top.rangeRestrict
  let A := F.actualKernelModule
  let E := F.actualOriginalKernelChart
  have ht' : Function.Surjective (sectionTop pi N F.top.rangeRestrict_surjective) := by
    intro q
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (pi.ker ⊔ N) q
    exact ⟨pi g,sectionTop_apply pi N F.top.rangeRestrict_surjective g⟩
  have hq : Nat.card (U ⧸ N)≤2^48 :=
    (Nat.card_le_card_of_surjective (QuotientGroup.mk' N)
      (QuotientGroup.mk'_surjective N)).trans (original_order_le F ht)
  have hr : Nat.card (U ⧸ (pi.ker ⊔ N))≤2^32 :=
    (Nat.card_le_card_of_surjective (sectionTop pi N F.top.rangeRestrict_surjective) ht').trans ht
  exact WidthThirtyTwoFiniteTopBinaryEnvelope.raw_sum_le
    (base pi N) (base_surjective pi N) (E.sectionRepresentation pi A N)
    (E.quotientChart pi A N)
    (F.actualSectionDualGeneratedBy (permutationFunctionRepresentation_dual_uniform hu) N)
    hq hr theta (ordinary_cost hsocle hZmud lit theta hslope) b

include F in
theorem quotient_sum_le {k H : ℕ}
    (ht : Nat.card F.top.range≤2^32)
    (hu : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) F.top.range (Fin 16)) H)
    (hsocle : ∀ (M : Subgroup F.top.range) [M.Normal],
      SocleNormalGeneratorBound (F.top.range ⧸ M) k)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (theta : ℝ) (hslope : (k : ℝ)*(Real.logb 2 5/3)+(51/200 : ℝ)*H≤theta)
    (N : Subgroup U) [N.Normal] (b : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)),(Nat.card (GroupEpimorphism J (U ⧸ N)) : ℝ)) ≤
      BinaryKernelRankTailNumerics.raw 1 4294967344 b+
        (subgroupCount b : ℝ)*((2 : ℝ)^(2560 : ℕ)*(2 : ℝ)^(theta*b)) := by
  let pi := F.top.rangeRestrict
  let f := sectionTop pi N F.top.rangeRestrict_surjective
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (pi.ker ⊔ N) q
    exact ⟨pi g,sectionTop_apply pi N F.top.rangeRestrict_surjective g⟩
  let e := QuotientGroup.quotientKerEquivOfSurjective f hf
  exact section_sum_le F ht hu N
    (CyclicSocleQuotientTools.socleBound_equiv e (hsocle f.ker)) hZmud lit theta hslope b

include F in
theorem quotient_sum_le_of_split {k H : ℕ}
    (ht : Nat.card F.top.range≤2^32)
    (hu : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) F.top.range (Fin 16)) H)
    (hsocle : ∀ (M : Subgroup F.top.range) [M.Normal],
      ¬IsPGroup 2 (F.top.range ⧸ M) → SocleNormalGeneratorBound (F.top.range ⧸ M) k)
    (hbinary : ∀ (N : Subgroup U) [N.Normal], IsPGroup 2 (U ⧸ N) → Nat.card (U ⧸ N)≤2^15)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (theta : ℝ) (hslope : (k : ℝ)*(Real.logb 2 5/3)+(51/200 : ℝ)*H≤theta)
    (hbinarySlope : (15 : ℝ)*(51/200)≤theta)
    (N : Subgroup U) [N.Normal] (b : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)),(Nat.card (GroupEpimorphism J (U ⧸ N)) : ℝ)) ≤
      BinaryKernelRankTailNumerics.raw 1 4294967344 b+
        (subgroupCount b : ℝ)*((2 : ℝ)^(2560 : ℕ)*(2 : ℝ)^(theta*b)) := by
  by_cases hb : IsPGroup 2 (U ⧸ N)
  · obtain ⟨r,hr⟩ := hb.exists_card_eq
    have hp : 2^r≤2^15 := by rw [←hr]; exact hbinary N hb
    have hle : r≤15 := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp hp
    apply (BinaryTargetRankTailSum.full_sum_le 15 r hle hr b).trans
    apply add_le_add
    · unfold BinaryKernelRankTailNumerics.raw
      simp only [one_mul]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact pow_le_pow_right₀ (by exact_mod_cast Nat.succ_le_iff.mpr (Nat.factorial_pos b))
        (by decide : 15≤4294967344)
    · apply mul_le_mul_of_nonneg_left _ (by positivity)
      have he := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ)≤2)
        (mul_le_mul_of_nonneg_right hbinarySlope (Nat.cast_nonneg (α := ℝ) b))
      exact he.trans (le_mul_of_one_le_left (by positivity)
        (one_le_pow₀ (by norm_num : (1 : ℝ)≤2)))
  · let pi := F.top.rangeRestrict
    let A := F.actualKernelModule
    let E := F.actualOriginalKernelChart
    have hR : ¬IsPGroup 2 (U ⧸ (pi.ker ⊔ N)) := by
      intro h
      exact hb ((E.quotientChart pi A N).isPGroup_two_of_base
        (base pi N) (E.sectionRepresentation pi A N) h)
    let f := sectionTop pi N F.top.rangeRestrict_surjective
    have hf : Function.Surjective f := by
      intro q
      obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (pi.ker ⊔ N) q
      exact ⟨pi g,sectionTop_apply pi N F.top.rangeRestrict_surjective g⟩
    let e := QuotientGroup.quotientKerEquivOfSurjective f hf
    have hs := hsocle f.ker (fun h => hR (h.of_equiv e))
    exact section_sum_le F ht hu N
      (CyclicSocleQuotientTools.socleBound_equiv e hs) hZmud lit theta hslope b

end SymmetricSubgroupAsymptotics.WidthThirtyTwoActualKernelQuotientSum
