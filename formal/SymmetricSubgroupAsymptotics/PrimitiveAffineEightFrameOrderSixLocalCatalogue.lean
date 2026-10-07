import SymmetricSubgroupAsymptotics.FiniteSurjectiveKernelTransport
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameLocalRowCatalogue

/-!
# Point-stabilizer order-six local dispatcher

An order-six point stabilizer with no quotient of order three has a unique
eligible order-three-or-six quotient: the stabilizer itself.  This turns one
checked faithful local row into the exact literal local-row catalogue used by
the eight-frame consumer.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeEightLiteralLocalRowCatalogue

theorem stabilizer_card_six_of_card_fortyEight
    (T : Subgroup (Equiv.Perm (Fin 8)))
    [MulAction.IsPretransitive T (Fin 8)]
    (hT : Nat.card T = 48) :
    Nat.card (MulAction.stabilizer T (0 : Fin 8)) = 6 := by
  have hindex : (MulAction.stabilizer T (0 : Fin 8)).index = 8 := by
    simpa only [Nat.card_fin] using
      MulAction.index_stabilizer_of_transitive T (0 : Fin 8)
  have hcard := (MulAction.stabilizer T (0 : Fin 8)).card_mul_index
  rw [hindex, hT] at hcard
  omega

theorem surjectiveHom_kernel_card_one_of_six_to_six
    {H L : Type*} [Group H] [Finite H] [Group L] [Finite L]
    (f : H →* L) (hf : Function.Surjective f)
    (hH : Nat.card H = 6) (hL : Nat.card L = 6) :
    Nat.card f.ker = 1 := by
  have hcard := f.ker.card_mul_index
  rw [Subgroup.index_ker, f.range_eq_top_of_surjective hf,
    Nat.card_congr Subgroup.topEquiv.toEquiv, hH, hL] at hcard
  omega

/-- The unique local-row catalogue for an order-six point stabilizer once an
order-three quotient has been excluded. -/
noncomputable def singletonOfOrderSix
    (T : Subgroup (Equiv.Perm (Fin 8)))
    (R : DegreeEightLiteralLocalRow T)
    (hsource : Nat.card (MulAction.stabilizer T (0 : Fin 8)) = 6)
    (hnoThree :
      ∀ (L : Type) [Group L] [Finite L]
        (f : MulAction.stabilizer T (0 : Fin 8) →* L),
        Function.Surjective f → Nat.card L = 3 → False)
    (htarget : Nat.card R.ModelLocalGroup = 6) :
    DegreeEightLiteralLocalRowCatalogue T where
  Row := Unit
  row _ := R
  complete := by
    intro L _ _ f hf hcard
    have hL : Nat.card L = 6 := by
      rcases hcard with h3 | ⟨h6, _⟩
      · exact False.elim (hnoThree L f hf h3)
      · exact h6
    have hfker : Nat.card f.ker = 1 :=
      surjectiveHom_kernel_card_one_of_six_to_six
        f hf hsource hL
    have hRker : Nat.card R.literalLocalMap.ker = 1 :=
      surjectiveHom_kernel_card_one_of_six_to_six
        R.literalLocalMap R.literalLocalMap_surjective hsource htarget
    have hkernels : f.ker = R.literalLocalMap.ker := by
      rw [Subgroup.card_eq_one] at hfker hRker
      exact hfker.trans hRker.symm
    refine ⟨(), surjectiveTargetEquivOfKernelEq f R.literalLocalMap
      hf R.literalLocalMap_surjective hkernels, ?_⟩
    exact surjectiveTargetEquivOfKernelEq_comp f R.literalLocalMap
      hf R.literalLocalMap_surjective hkernels

end DegreeEightLiteralLocalRowCatalogue
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
