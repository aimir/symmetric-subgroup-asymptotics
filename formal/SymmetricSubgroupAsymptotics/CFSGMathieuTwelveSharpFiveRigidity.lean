import SymmetricSubgroupAsymptotics.FiniteBaseCentralizerSeedBounds
import SymmetricSubgroupAsymptotics.External.CFSG.Certificates.Mathieu12.Cardinality
import Mathlib.Data.Fintype.CardEmbedding

/-! Arbitrary-five rigidity for the SAME original M12. The checked original
Witt fixed-five theorem proves one rigid base. The proved group cardinal95040
equals the number of injective ordered five-tuples, so that base's evaluation
is bijective. No multiple-transitivity or model-identification premise occurs. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSharpFiveRigidity
open CFSG.Certificates.Mathieu12 M12Certificates.WittDesign
open FiniteBaseCentralizerSeedBounds

def standardBase : Fin 5 ↪ Fin 12 where
  toFun i := ⟨i.val,Nat.lt_trans i.isLt (by decide)⟩
  inj' := by intro i j he; exact Fin.ext (congrArg (fun z : Fin 12 => z.val) he)

theorem standard_base_rigid :
    Function.Injective (baseEvaluation M12Subgroup.subtype standardBase) := by
  intro g h he
  have hpoint (i : Fin 5) : g.val (standardBase i) = h.val (standardBase i) :=
    DFunLike.congr_fun he i
  have hfix (i : Fin 5) : (h.val⁻¹*g.val) (standardBase i) = standardBase i := by
    change h.val.symm (g.val (standardBase i)) = standardBase i
    rw [hpoint,Equiv.symm_apply_apply]
  have hp : PreservesWittBlocks (h.val⁻¹*g.val) := by
    simpa only [Subgroup.coe_mul,Subgroup.coe_inv] using M12_preserves_wittBlocks (h⁻¹*g)
  have hd : h.val⁻¹*g.val = 1 :=
    fixed_five_preserves_wittBlocks_eq_one _ hp (hfix 0) (hfix 1) (hfix 2) (hfix 3) (hfix 4)
  exact Subtype.ext (inv_mul_eq_one.mp hd).symm

theorem five_tuple_card : Nat.card (Fin 5 ↪ Fin 12) = 95040 := by
  rw [Nat.card_eq_fintype_card,Fintype.card_embedding_eq]
  norm_num [Fintype.card_fin,Nat.descFactorial]

theorem eq_of_agree_five (base : Fin 5 ↪ Fin 12) (g h : M12)
    (he : ∀ i, g.val (base i) = h.val (base i)) : g = h := by
  exact arbitrary_base_rigid M12Subgroup.subtype standardBase standard_base_rigid
    (M12Cardinality.card_M12.trans five_tuple_card.symm) base g h he

end SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSharpFiveRigidity
