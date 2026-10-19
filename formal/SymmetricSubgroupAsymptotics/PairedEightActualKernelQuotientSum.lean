import SymmetricSubgroupAsymptotics.PairedEightActualKernelModel
import SymmetricSubgroupAsymptotics.PairedEightOriginalResidualTopCost
import SymmetricSubgroupAsymptotics.FiniteTopBinaryDualKernelGeneratorEnvelope
import SymmetricSubgroupAsymptotics.BinaryPairKernelCard

/-! Complete source sums on each original normal quotient of a physical
eight-pair action. Both the exact module section and its residual top
are constructed from that same original normal subgroup. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.PairedEightActualKernelQuotientSum
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoPairedEightSharedTops OriginalKernelModuleChart
open PairedEightActualKernelModel

variable {U : Subgroup (Equiv.Perm (Fin 16))}
    (F : BinaryPairFrame U (Fin 8)) (j : Fin 24)
    (e : F.top.range ≃* (interface j).top)
    (coords : Fin 8 ≃ Fin 8)
    (hact : ∀ (p : F.top.range) (i : Fin 8), coords ((p : Equiv.Perm (Fin 8)) i)=
      (e p : Equiv.Perm (Fin 8)) (coords i))

include F e in
theorem top_order_le : Nat.card (interface j).top ≤ 2^16 := by
  have hh := Nat.card_le_card_of_injective
    (Subtype.val : F.top.range → Equiv.Perm (Fin 8)) Subtype.val_injective
  rw [Nat.card_perm,Nat.card_fin] at hh
  have he := Nat.card_congr e.toEquiv
  rw [he] at hh
  exact hh.trans (by norm_num)

include F j e in
theorem original_order_le : Nat.card U ≤ 2^24 := by
  have hk : Nat.card F.kernelSpace ≤ 2^8 := by
    have hh := Nat.card_le_card_of_injective
      (Subtype.val : F.kernelSpace → (Fin 8 → ZMod 2)) Subtype.val_injective
    have hf : Nat.card (Fin 8 → ZMod 2)=2^8 := by
      rw [Nat.card_fun,Nat.card_fin,Nat.card_eq_fintype_card (α := ZMod 2),ZMod.card]
    rw [hf] at hh
    exact hh
  have ht : Nat.card F.top.range ≤ 2^16 := by
    rw [Nat.card_congr e.toEquiv]
    exact top_order_le F j e
  rw [←F.kernelSpace_card_mul_top]
  exact (Nat.mul_le_mul hk ht).trans_eq (by rw [←pow_add])

include hact in
theorem quotient_sum_le
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (N : Subgroup U) [N.Normal] (b : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)),(Nat.card (GroupEpimorphism J (U ⧸ N)) : ℝ)) ≤
      Non2UnipotentPrefixFiniteMenu.BinaryKernelRankTailNumerics.raw 1 65560 b+
        (subgroupCount b : ℝ)*((2 : ℝ)^(640 : ℕ)*(2 : ℝ)^((31/16 : ℝ)*b)) := by
  let pi := top F j e
  let A := kernelModule F j e
  let E := kernelChart F j e
  have hpi : Function.Surjective pi := top_surjective F j e
  have hq : Nat.card (U ⧸ N) ≤ 2^24 :=
    (Nat.card_le_card_of_surjective (QuotientGroup.mk' N)
      (QuotientGroup.mk'_surjective N)).trans (original_order_le F j e)
  have ht : Nat.card (U ⧸ (pi.ker ⊔ N)) ≤ 2^16 :=
    (Nat.card_le_card_of_surjective (sectionTop pi N hpi)
      (PairedEightOriginalResidualTopCost.residual_top_surjective j pi hpi N)).trans
        (top_order_le F j e)
  exact FiniteTopBinaryDualKernelGeneratorEnvelope.raw_sum_le
    (base pi N) (base_surjective pi N) (E.sectionRepresentation pi A N)
    (E.quotientChart pi A N)
    (all_original_sections_dual_generated F j e coords hact N) hq ht (31/16)
    (fun b J => PairedEightOriginalResidualTopCost.cost j pi hpi N hZmud lit b J) b

end SymmetricSubgroupAsymptotics.PairedEightActualKernelQuotientSum
