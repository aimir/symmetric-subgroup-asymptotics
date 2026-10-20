import SymmetricSubgroupAsymptotics.SixPairFullKernelAllNormalDichotomy
import SymmetricSubgroupAsymptotics.SixPairProperCentralQuotientSocleOne
import SymmetricSubgroupAsymptotics.SixPairThreePairOriginalOrder
import SymmetricSubgroupAsymptotics.SocleOneEpimorphismEnvelopeTwelve
import SymmetricSubgroupAsymptotics.OriginalNormalQuotientAxisSum
import SymmetricSubgroupAsymptotics.GrowingQuotientTransferNumerics

/-! Complete original-axis reduction to the actual center quotient.
The proper-center branch costs at most 2^288; all other axes inject into
U/Z without paying another normal-menu multiplicity. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.SixPairFullKernelOriginalQuotientSum
open SixPairFullKernelCenter Non2UnipotentPrefixFiniteMenu

variable {X I : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U I)
  (E : ProductBlockFrame F.top.range (Fin 3) (ZMod 2))

/-- Every literal original normal axis is counted, including axes meeting
or killing the retained top. -/
theorem complete_weight_le [MulAction.IsPretransitive U X]
    (hfull : SixPairIndependentKernelNormalCommutators.Independent F E)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))) :
    completeQuotientWeight (R := U) J≤
      (2 : ℝ)^(288 : ℕ)*(2 : ℝ)^((43/30 : ℝ)*(b : ℝ))+
        completeQuotientWeight (R := U ⧸ centerImage F E) J := by
  let Z := centerImage F E
  let Ax := {N : Subgroup U // N.Normal}
  let Below := {N : Ax // ¬Z≤N.val}
  let f : Ax → ℝ := fun N => Nat.card (GroupEpimorphism J (U ⧸ N.val))
  have hU : Nat.card U≤2^12 := SixPairThreePairOriginalOrder.card_le_two_pow_twelve F E
  have hn : (Nat.card Below : ℝ)≤(2 : ℝ)^(144 : ℕ) := by
    exact_mod_cast (Nat.card_le_card_of_injective (Subtype.val : Below → Ax)
      Subtype.val_injective).trans (normalSubgroup_card_le_two_pow_sq 12 hU)
  have hf (N : Below) : f N.val≤
      (2 : ℝ)^(144 : ℕ)*(2 : ℝ)^((43/30 : ℝ)*(b : ℝ)) := by
    letI : N.val.val.Normal := N.val.property
    have hN : N.val.val≤Z :=
      (SixPairFullKernelAllNormalDichotomy.normal_dichotomy F E hfull N.val.val).resolve_right
        N.property
    have hs := SixPairProperCentralQuotientSocleOne.socle_bound F E hfull N.val.val hN N.property
    have hQ : Nat.card (U ⧸ N.val.val)≤2^12 :=
      (Nat.card_le_card_of_surjective (QuotientGroup.mk' N.val.val)
        (QuotientGroup.mk'_surjective N.val.val)).trans hU
    exact SocleOneEpimorphismEnvelopeTwelve.epi_card_le hQ hs hZmud lit b J
  have hb : (∑ N : Below,f N.val)≤
      (2 : ℝ)^(288 : ℕ)*(2 : ℝ)^((43/30 : ℝ)*(b : ℝ)) := by
    calc
      _ ≤ ∑ _N : Below,(2 : ℝ)^(144 : ℕ)*(2 : ℝ)^((43/30 : ℝ)*(b : ℝ)) :=
        Finset.sum_le_sum (fun N _ => hf N)
      _ = (Nat.card Below : ℝ)*
          ((2 : ℝ)^(144 : ℕ)*(2 : ℝ)^((43/30 : ℝ)*(b : ℝ))) := by
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_eq_nat_card]
      _ ≤ (2 : ℝ)^(144 : ℕ)*
          ((2 : ℝ)^(144 : ℕ)*(2 : ℝ)^((43/30 : ℝ)*(b : ℝ))) :=
        mul_le_mul_of_nonneg_right hn (by positivity)
      _ = _ := by rw [←mul_assoc,←pow_add]
  have ha : (∑ N : OriginalNormalQuotientAxisInjection.Above Z,f N.val)≤
      completeQuotientWeight (R := U ⧸ Z) J := by
    have h0 := OriginalNormalQuotientAxisInjection.above_epi_sum_le (J := J) Z
    dsimp only [f]
    unfold completeQuotientWeight completeQuotientCount
    rw [Nat.cast_sum]
    convert h0 using 1 <;>
      (apply Finset.sum_congr (by ext N; simp); intro N _; rfl)
  have hsum : (∑ N : Ax,f N)≤
      (2 : ℝ)^(288 : ℕ)*(2 : ℝ)^((43/30 : ℝ)*(b : ℝ))+
        completeQuotientWeight (R := U ⧸ Z) J := by
    rw [←Fintype.sum_subtype_add_sum_subtype (fun N : Ax => Z≤N.val) f]
    exact (add_le_add ha hb).trans_eq (add_comm _ _)
  conv_lhs =>
    unfold completeQuotientWeight completeQuotientCount
    rw [Nat.cast_sum]
  convert hsum using 1 <;>
    (apply Finset.sum_congr (by ext N; simp); intro N _; rfl)

end SymmetricSubgroupAsymptotics.SixPairFullKernelOriginalQuotientSum
