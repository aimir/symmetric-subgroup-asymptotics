import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoSelectedTraceTransitions
import SymmetricSubgroupAsymptotics.PrimePeriodSimpleQuotientIndex

/-! The one selected word a³b² belongs to the SAME actual pinned
Mathieu22 generated subgroup. Its checked point-zero return at eleven
and nonreturn at one supply a prime divisor of that literal model's
cardinality. No model identification, known order, simplicity, or full
permutation-power identity is required. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoSelectedWordOrder
open CFSG.Models.Mathieu22Construction
open CFSGMathieuTwentyTwoSelectedTraceFirstStep CFSGMathieuTwentyTwoSelectedTraceTransitions

private def A : CFSG.Models.Mathieu22 :=
  ⟨a, Subgroup.subset_closure (Or.inl rfl)⟩

private def B : CFSG.Models.Mathieu22 :=
  ⟨b, Subgroup.subset_closure (Or.inr rfl)⟩

/-- The original selected word is an element of the literal generated model. -/
def selectedModelWord : CFSG.Models.Mathieu22 := A ^ 3 * B ^ 2

theorem selectedWord_coe : (selectedModelWord : Equiv.Perm (Fin 22)) = selectedWord := rfl

/-- Prime-period divisibility concerns the actual generated subgroup,
not the whole symmetric group containing the displayed permutations. -/
theorem eleven_dvd_order : 11 ∣ Nat.card CFSG.Models.Mathieu22 := by
  apply PrimePeriodSimpleQuotientIndex.prime_dvd_card_of_point_period
    11 (by decide) selectedModelWord (0 : Fin 22)
  · change ((selectedModelWord : Equiv.Perm (Fin 22)) ^ 11) (0 : Fin 22) = 0
    rw [selectedWord_coe]
    exact return_eleven
  · change (selectedModelWord : Equiv.Perm (Fin 22)) (0 : Fin 22) ≠ 0
    rw [selectedWord_coe]
    exact moved_zero

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoSelectedWordOrder
