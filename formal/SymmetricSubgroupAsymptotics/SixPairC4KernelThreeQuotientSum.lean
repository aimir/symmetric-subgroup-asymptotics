import SymmetricSubgroupAsymptotics.FiniteTopBoundedBinaryKernelQuotients
import SymmetricSubgroupAsymptotics.FiniteTopC4KernelThreeRawSum
import SymmetricSubgroupAsymptotics.ThreePointTransitiveCubicMembership
import SymmetricSubgroupAsymptotics.TwoBinaryThreeCubicTopTypes
import SymmetricSubgroupAsymptotics.SixPairThreePairOriginalNormals
import SymmetricSubgroupAsymptotics.BinaryTargetRankTailSum

/-! Complete original-normal sums for actual coarse kernels embedded in
C4³. Every quotient retains its literal kernel image and the correct
original or residual top; no splitting or elementary assumption is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.SixPairC4KernelThreeQuotientSum
open Non2UnipotentPrefixFiniteMenu OriginalKernelModuleChart

variable {X I : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U I)
  (E : ProductBlockFrame F.top.range (Fin 3) (ZMod 2))

include F E in
theorem original_order_le_nine
    (j : (SixPairNestedTopFrames.nestedFrame F E).top.ker →* (Fin 3 → C4CoordinateHomCount.C4))
    (hj : Function.Injective j) : Nat.card U≤2^9 := by
  let C := SixPairNestedTopFrames.nestedFrame F E
  have hk : Nat.card C.top.ker≤64 := by
    apply (Nat.card_le_card_of_injective j hj).trans_eq
    norm_num [Nat.card_fun,C4CoordinateHomCount.C4,Nat.card_congr Multiplicative.toAdd]
  have ht : Nat.card C.top.range≤6 :=
    FiniteTopKernelHomLiftCount.top_card_le_six C.top.range.subtype Subtype.val_injective
  have he := C.top.ker.card_mul_index
  rw [Subgroup.index_ker] at he
  exact he.symm.le.trans ((Nat.mul_le_mul hk ht).trans (by norm_num))

/-- Every original denominator retains an actual C4-coordinate kernel.
The original top is kept exactly when possible; otherwise the actual
residual top is cyclic of order at most two. -/
theorem quotient_sum_le [MulAction.IsPretransitive U X]
    (j : (SixPairNestedTopFrames.nestedFrame F E).top.ker →* (Fin 3 → C4CoordinateHomCount.C4))
    (hj : Function.Injective j) (hKP : KovacsPraegerAbelianizationBound)
    (N : Subgroup U) [N.Normal] (b : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)),(Nat.card (GroupEpimorphism J (U ⧸ N)) : ℝ))≤
      MarkedC4KernelRankTailNumerics.raw 1 15 b+
        (subgroupCount b : ℝ)*((2 : ℝ)^(80 : ℕ)*(2 : ℝ)^((43/30 : ℝ)*(b : ℝ))) := by
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
  let jpi : pi.ker →* (Fin 3 → C4CoordinateHomCount.C4) :=
    j.comp (MulEquiv.subgroupCongr hk).toMonoidHom
  have hjpi : Function.Injective jpi := hj.comp (MulEquiv.subgroupCongr hk).injective
  have hQ : Nat.card (U ⧸ N)≤2^9 :=
    (Nat.card_le_card_of_surjective (QuotientGroup.mk' N)
      (QuotientGroup.mk'_surjective N)).trans (original_order_le_nine F E j hj)
  have hTcard : Nat.card T≤6 :=
    FiniteTopKernelHomLiftCount.top_card_le_six T.subtype Subtype.val_injective
  letI : MulAction.IsPretransitive T (Fin 3) :=
    ⟨C.top_range_transitive (fun x y => MulAction.exists_smul_eq U x y)⟩
  by_cases hN : N≤pi.ker
  · let top := FiniteTopSmallKernelQuotients.retainedTop pi N hN
    have hs := FiniteTopSmallKernelQuotients.retainedTop_surjective pi N hpi hN
    obtain ⟨r,hr,jr,hjr⟩ := C4CoordinateSurjectiveQuotient.exists_embedding jpi hjpi
      (FiniteTopSmallKernelQuotients.retainedKernelMap pi N hN)
      (FiniteTopSmallKernelQuotients.retainedKernelMap_surjective pi N hN)
    have htype : IsCyclic T ∨ Nonempty (T ≃* Equiv.Perm (Fin 3)) := by
      rcases SixPairThreePointNormalTop.cardinal_cases T with h3 | h6
      · letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
        exact Or.inl (isCyclic_of_prime_card h3)
      · exact Or.inr ⟨TwoBinaryThreePermutationCoordinates.symmetricEquivOfCardSix T h6⟩
    exact FiniteTopC4KernelThree.raw_sum_le top hs hTcard hr jr hjr hQ htype hKP b
  · letI : (N.map pi).Normal := (inferInstance : N.Normal).map pi hpi
    have hne : N.map pi≠⊥ := by
      intro he
      exact hN ((Subgroup.map_eq_bot_iff (H := N)).mp he)
    have ht := SixPairThreePointNormalTop.quotient_card_le_two T (N.map pi) hne
    have hr : Nat.card (U ⧸ (pi.ker ⊔ N))≤2 :=
      (residualTop_card_eq pi hpi N).le.trans ht
    let top := base pi N
    have hs := base_surjective pi N
    obtain ⟨r,hrr,jr,hjr⟩ := C4CoordinateSurjectiveQuotient.exists_embedding jpi hjpi
      (quotientKernelMap pi N) (quotientKernelMap_surjective pi N)
    have htype : IsCyclic (U ⧸ (pi.ker ⊔ N)) ∨
        Nonempty ((U ⧸ (pi.ker ⊔ N)) ≃* Equiv.Perm (Fin 3)) :=
      Or.inl (SharpCyclicOrSymmetricThreeEpiEnvelope.cyclic_of_card_le_two hr)
    exact FiniteTopC4KernelThree.raw_sum_le top hs (hr.trans (by decide))
      hrr jr hjr hQ htype hKP b

end SymmetricSubgroupAsymptotics.SixPairC4KernelThreeQuotientSum
