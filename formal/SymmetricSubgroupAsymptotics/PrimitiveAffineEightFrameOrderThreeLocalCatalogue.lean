import SymmetricSubgroupAsymptotics.FiniteSurjectiveKernelTransport
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameLocalRowCatalogue

/-!
# Point-stabilizer order-three local dispatcher

A transitive order-24 group on eight points has point stabilizer of order
three.  Consequently every eligible order-three-or-six local quotient has
order three and trivial kernel.  Any checked onto order-three local row is
therefore the unique row, with the exact comparison map supplied by the
first isomorphism theorem.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeEightLiteralLocalRowCatalogue

theorem stabilizer_card_three_of_card_twentyFour
    (T : Subgroup (Equiv.Perm (Fin 8)))
    [MulAction.IsPretransitive T (Fin 8)]
    (hT : Nat.card T = 24) :
    Nat.card (MulAction.stabilizer T (0 : Fin 8)) = 3 := by
  have hindex : (MulAction.stabilizer T (0 : Fin 8)).index = 8 := by
    simpa only [Nat.card_fin] using
      MulAction.index_stabilizer_of_transitive T (0 : Fin 8)
  have hcard := (MulAction.stabilizer T (0 : Fin 8)).card_mul_index
  rw [hindex, hT] at hcard
  omega

theorem surjectiveHom_kernel_card_one_of_three_to_three
    {H L : Type*} [Group H] [Finite H] [Group L] [Finite L]
    (f : H →* L) (hf : Function.Surjective f)
    (hH : Nat.card H = 3) (hL : Nat.card L = 3) :
    Nat.card f.ker = 1 := by
  have hcard := f.ker.card_mul_index
  rw [Subgroup.index_ker, f.range_eq_top_of_surjective hf,
    Nat.card_congr Subgroup.topEquiv.toEquiv, hH, hL] at hcard
  omega

/-- The unique local-row catalogue for a literal point stabilizer of order
three.  Equality of the two trivial kernels retains the exact local map. -/
noncomputable def singletonOfOrderThree
    (T : Subgroup (Equiv.Perm (Fin 8)))
    (R : DegreeEightLiteralLocalRow T)
    (hsource : Nat.card (MulAction.stabilizer T (0 : Fin 8)) = 3)
    (htarget : Nat.card R.ModelLocalGroup = 3) :
    DegreeEightLiteralLocalRowCatalogue T where
  Row := Unit
  row _ := R
  complete := by
    intro L _ _ f hf hcard
    have hL : Nat.card L = 3 := by
      rcases hcard with h3 | ⟨h6, _⟩
      · exact h3
      · exfalso
        have hdvd : Nat.card L ∣
            Nat.card (MulAction.stabilizer T (0 : Fin 8)) :=
          Subgroup.card_dvd_of_surjective f hf
        rw [h6, hsource] at hdvd
        norm_num at hdvd
    have hfker : Nat.card f.ker = 1 :=
      surjectiveHom_kernel_card_one_of_three_to_three
        f hf hsource hL
    have hRker : Nat.card R.literalLocalMap.ker = 1 :=
      surjectiveHom_kernel_card_one_of_three_to_three
        R.literalLocalMap R.literalLocalMap_surjective hsource htarget
    have hkernels : f.ker = R.literalLocalMap.ker := by
      rw [Subgroup.card_eq_one] at hfker hRker
      exact hfker.trans hRker.symm
    refine ⟨(), surjectiveTargetEquivOfKernelEq f R.literalLocalMap
      hf R.literalLocalMap_surjective hkernels, ?_⟩
    exact surjectiveTargetEquivOfKernelEq_comp f R.literalLocalMap
      hf R.literalLocalMap_surjective hkernels

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

/-- Select the exact checked order-three row for an actual order-24 top. -/
noncomputable def selectActualOrderTwentyFour
    {ModelGroup : Type} [Group ModelGroup] [Finite ModelGroup]
    (topMatch : DegreeFourZeroCoreEightLiteralTopMatch block ModelGroup)
    (R : DegreeEightLiteralLocalRow topMatch.literalAction)
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥)
    (hmodel : Nat.card ModelGroup = 24)
    (htarget : Nat.card R.ModelLocalGroup = 3) :
    DegreeFourZeroCoreEightPointedLocalMatch
      block P topMatch hr hD (0 : Fin 8) := by
  letI : MulAction.IsPretransitive topMatch.literalAction (Fin 8) :=
    DegreeFourZeroCoreEightLiteralTopMatch.literalAction_pretransitive
      (block := block) topMatch
  have hliteral : Nat.card topMatch.literalAction = 24 := by
    rw [Nat.card_congr topMatch.actionModelEquiv.toEquiv]
    exact hmodel
  let C := singletonOfOrderThree topMatch.literalAction R
    (stabilizer_card_three_of_card_twentyFour
      topMatch.literalAction hliteral) htarget
  exact (selectActual block P topMatch C hr hD).2

end DegreeEightLiteralLocalRowCatalogue
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
