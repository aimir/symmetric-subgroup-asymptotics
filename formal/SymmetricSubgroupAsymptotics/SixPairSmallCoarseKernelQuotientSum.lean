import SymmetricSubgroupAsymptotics.FiniteTopSmallKernelQuotients
import SymmetricSubgroupAsymptotics.FiniteTopSmallBinaryKernelRawSum
import SymmetricSubgroupAsymptotics.SixPairThreePairOriginalNormals
import SymmetricSubgroupAsymptotics.BinaryTargetRankTailSum

/-! Complete original-normal sum for an actual coarse kernel of order at
most four. Retained axes keep the original transitive three-point top;
other axes give binary quotients of order at most eight. Both branches
retain nonsplit kernels, including C4. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.SixPairSmallCoarseKernelQuotientSum
open Non2UnipotentPrefixFiniteMenu OriginalKernelModuleChart

variable {X I : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U I)
  (E : ProductBlockFrame F.top.range (Fin 3) (ZMod 2))

include F E in
theorem original_order_le_five
    (hcard : Nat.card (SixPairNestedTopFrames.nestedFrame F E).top.ker≤4) :
    Nat.card U≤2^5 := by
  let C := SixPairNestedTopFrames.nestedFrame F E
  have ht : Nat.card C.top.range≤6 :=
    FiniteTopKernelHomLiftCount.top_card_le_six C.top.range.subtype Subtype.val_injective
  have he := C.top.ker.card_mul_index
  rw [Subgroup.index_ker] at he
  exact he.symm.le.trans ((Nat.mul_le_mul hcard ht).trans (by norm_num))

/-- Every actual original normal quotient has the same complete-source
budget, with the correct retained/residual top in each branch. -/
theorem quotient_sum_le [MulAction.IsPretransitive U X]
    (hcard : Nat.card (SixPairNestedTopFrames.nestedFrame F E).top.ker≤4)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (N : Subgroup U) [N.Normal] (b : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)),(Nat.card (GroupEpimorphism J (U ⧸ N)) : ℝ))≤
      BinaryKernelRankTailNumerics.raw 1 11 b+
        (subgroupCount b : ℝ)*((2 : ℝ)^(64 : ℕ)*(2 : ℝ)^((43/30 : ℝ)*(b : ℝ))) := by
  let C := SixPairNestedTopFrames.nestedFrame F E
  let T := C.top.range
  let pi := C.top.rangeRestrict
  have hpi : Function.Surjective pi := C.top.rangeRestrict_surjective
  have hk : pi.ker=C.top.ker := by
    ext g
    constructor
    · intro hg
      exact congrArg (fun t : T => (t : Equiv.Perm (Fin 3))) hg
    · intro hg
      exact Subtype.ext hg
  have hK : IsPGroup 2 pi.ker := by
    rw [hk]
    exact SixPairThreePairKernelExponent.kernel_binary F E
  have hkc : Nat.card pi.ker≤4 := by simpa only [hk] using hcard
  have hQ : Nat.card (U ⧸ N)≤2^5 :=
    (Nat.card_le_card_of_surjective (QuotientGroup.mk' N)
      (QuotientGroup.mk'_surjective N)).trans (original_order_le_five F E hcard)
  by_cases hN : N≤pi.ker
  · let top := FiniteTopSmallKernelQuotients.retainedTop pi N hN
    have hs := FiniteTopSmallKernelQuotients.retainedTop_surjective pi N hpi hN
    obtain ⟨hb,hbcard⟩ := FiniteTopSmallKernelQuotients.retained_kernel_small pi N hN hK hkc
    exact FiniteTopKernelHomLiftCount.raw_sum_le top hs T.subtype Subtype.val_injective
      hb hbcard hQ hZmud lit b
  · letI : MulAction.IsPretransitive T (Fin 3) :=
      ⟨C.top_range_transitive (fun x y => MulAction.exists_smul_eq U x y)⟩
    letI : (N.map pi).Normal := (inferInstance : N.Normal).map pi hpi
    have hne : N.map pi≠⊥ := by
      intro he
      exact hN ((Subgroup.map_eq_bot_iff (H := N)).mp he)
    have ht := SixPairThreePointNormalTop.quotient_card_le_two T (N.map pi) hne
    have hr : Nat.card (U ⧸ (pi.ker ⊔ N))≤2 :=
      (residualTop_card_eq pi hpi N).le.trans ht
    obtain ⟨hb,hbcard⟩ := FiniteTopSmallKernelQuotients.residual_binary_small pi N hK hkc hr
    obtain ⟨r,he⟩ := hb.exists_card_eq
    have hpow : 2^r≤2^3 := by simpa only [he] using hbcard
    have hrank : r≤3 := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp hpow
    have hh := BinaryTargetRankTailSum.full_sum_le 3 r hrank he b
    apply hh.trans
    apply add_le_add
    · unfold BinaryKernelRankTailNumerics.raw
      simp only [one_mul]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply pow_le_pow_right₀ _ (by decide : 3≤11)
      exact_mod_cast (Nat.succ_le_iff.mpr (Nat.factorial_pos b) : 1≤b.factorial)
    · apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hp : (2 : ℝ)^(((3 : ℝ)*(51/200))*(b : ℝ))≤
          (2 : ℝ)^((43/30 : ℝ)*(b : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ)≤2)
          (mul_le_mul_of_nonneg_right (by norm_num : (3 : ℝ)*(51/200)≤43/30) (Nat.cast_nonneg b))
      exact hp.trans (le_mul_of_one_le_left (by positivity)
        (one_le_pow₀ (by norm_num : (1 : ℝ)≤2)))

end SymmetricSubgroupAsymptotics.SixPairSmallCoarseKernelQuotientSum
