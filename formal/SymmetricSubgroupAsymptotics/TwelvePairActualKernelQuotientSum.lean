import SymmetricSubgroupAsymptotics.TwelvePairFiniteTopEnvelope
import SymmetricSubgroupAsymptotics.BinaryPairActualKernelDualSections
import SymmetricSubgroupAsymptotics.PermutationFunctionSelfDual
import SymmetricSubgroupAsymptotics.BinaryPairKernelCard
import SymmetricSubgroupAsymptotics.FusionEpimorphismTransport

/-! Exact original-axis bounds for a twelve-pair target. An original
normal subgroup need not lie in the binary kernel; its residual top is
identified with the corresponding quotient of the SAME actual top. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.TwelvePairActualKernelQuotientSum
open Non2UnipotentPrefixFiniteMenu OriginalKernelModuleChart
variable {U : Subgroup (Equiv.Perm (Fin 24))} (F : BinaryPairFrame U (Fin 12))

include F in
theorem original_order_le (ht : Nat.card F.top.range ≤ 2^29) : Nat.card U ≤ 2^41 := by
  have hk : Nat.card F.kernelSpace ≤ 2^12 := by
    have hh := Nat.card_le_card_of_injective
      (Subtype.val : F.kernelSpace → (Fin 12 → ZMod 2)) Subtype.val_injective
    have hf : Nat.card (Fin 12 → ZMod 2)=2^12 := by
      rw [Nat.card_fun,Nat.card_fin,Nat.card_eq_fintype_card (α := ZMod 2),ZMod.card]
    rwa [hf] at hh
  rw [←F.kernelSpace_card_mul_top]
  exact (Nat.mul_le_mul hk ht).trans_eq (by rw [←pow_add])

include F in
theorem quotient_sum_le
    (ht : Nat.card F.top.range ≤ 2^29)
    (hu : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) F.top.range (Fin 12)) 4)
    (hcost : ∀ (M : Subgroup F.top.range) [M.Normal] (b : ℕ)
      (J : Subgroup (Equiv.Perm (Fin b))),
      (Nat.card (GroupEpimorphism J (F.top.range ⧸ M)) : ℝ) ≤
        (2 : ℝ)^(841 : ℕ)*(2 : ℝ)^((5/3 : ℝ)*b))
    (N : Subgroup U) [N.Normal] (b : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)),(Nat.card (GroupEpimorphism J (U ⧸ N)) : ℝ)) ≤
      BinaryKernelRankTailNumerics.raw 1 536870953 b+
        (subgroupCount b : ℝ)*((2 : ℝ)^(2030 : ℕ)*(2 : ℝ)^((403/150 : ℝ)*b)) := by
  let pi := F.top.rangeRestrict
  let A := F.actualKernelModule
  let E := F.actualOriginalKernelChart
  let f := sectionTop pi N F.top.rangeRestrict_surjective
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (pi.ker ⊔ N) q
    exact ⟨pi g,sectionTop_apply pi N F.top.rangeRestrict_surjective g⟩
  let e := QuotientGroup.quotientKerEquivOfSurjective f hf
  have hq : Nat.card (U ⧸ N) ≤ 2^41 :=
    (Nat.card_le_card_of_surjective (QuotientGroup.mk' N)
      (QuotientGroup.mk'_surjective N)).trans (original_order_le F ht)
  have hr : Nat.card (U ⧸ (pi.ker ⊔ N)) ≤ 2^29 :=
    (Nat.card_le_card_of_surjective f hf).trans ht
  have hc (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))) :
      (Nat.card (GroupEpimorphism J (U ⧸ (pi.ker ⊔ N))) : ℝ) ≤
        (2 : ℝ)^(841 : ℕ)*(2 : ℝ)^((5/3 : ℝ)*b) := by
    have he := fusionGroupEpimorphism_card_congr (MulEquiv.refl J) e
    rw [←he]
    exact hcost f.ker b J
  exact TwelvePairFiniteTopEnvelope.raw_sum_le
    (base pi N) (base_surjective pi N) (E.sectionRepresentation pi A N)
    (E.quotientChart pi A N)
    (F.actualSectionDualGeneratedBy (permutationFunctionRepresentation_dual_uniform hu) N)
    hq hr hc b

end SymmetricSubgroupAsymptotics.TwelvePairActualKernelQuotientSum
