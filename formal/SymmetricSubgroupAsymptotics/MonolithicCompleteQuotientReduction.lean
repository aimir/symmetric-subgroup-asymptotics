import SymmetricSubgroupAsymptotics.OriginalNormalQuotientAxisSum
import SymmetricSubgroupAsymptotics.GrowingQuotientTransferNumerics
import SymmetricSubgroupAsymptotics.FusionEpimorphismTransport

/-! A monolith removes one literal normal axis at a time. Every nonzero
original normal contains Z; those axes inject into the actual quotient's
normal menu, while the zero axis costs only the epimorphisms onto G itself.
No normal-subgroup multiplicity is introduced. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MonolithicCompleteQuotientReduction

variable {G : Type} [Group G] [Finite G]

theorem complete_weight_le (Z : Subgroup G) [Z.Normal]
    (hcover : ∀ (N : Subgroup G) [N.Normal], N ≠ ⊥ → Z ≤ N)
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) :
    completeQuotientWeight (R := G) J ≤
      (Nat.card (GroupEpimorphism J G) : ℝ) +
        completeQuotientWeight (R := G ⧸ Z) J := by
  let Ax := {N : Subgroup G // N.Normal}
  let Below := {N : Ax // ¬Z ≤ N.val}
  let f : Ax → ℝ := fun N => Nat.card (GroupEpimorphism J (G ⧸ N.val))
  have hbot (N : Below) : N.val.val = ⊥ := by
    letI : N.val.val.Normal := N.val.property
    by_contra hn
    exact N.property (hcover N.val.val hn)
  letI : Subsingleton Below := ⟨fun M N => Subtype.ext (Subtype.ext
    ((hbot M).trans (hbot N).symm))⟩
  have hn : (Nat.card Below : ℝ) ≤ 1 := by
    have hi := Nat.card_le_card_of_injective (fun _ : Below => Unit.unit)
      (fun _ _ _ => Subsingleton.elim _ _)
    simpa using (Nat.cast_le (α := ℝ)).mpr hi
  have hf (N : Below) : f N.val = (Nat.card (GroupEpimorphism J G) : ℝ) := by
    dsimp only [f]
    exact_mod_cast fusionGroupEpimorphism_card_congr (MulEquiv.refl J)
      ((QuotientGroup.quotientMulEquivOfEq (hbot N)).trans
        (QuotientGroup.quotientBot : G ⧸ (⊥ : Subgroup G) ≃* G))
  have hb : (∑ N : Below, f N.val) ≤ (Nat.card (GroupEpimorphism J G) : ℝ) := by
    calc
      _ = ∑ _N : Below, (Nat.card (GroupEpimorphism J G) : ℝ) :=
        Finset.sum_congr rfl (fun N _ => hf N)
      _ = (Nat.card Below : ℝ) * (Nat.card (GroupEpimorphism J G) : ℝ) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_eq_nat_card]
      _ ≤ 1 * (Nat.card (GroupEpimorphism J G) : ℝ) :=
        mul_le_mul_of_nonneg_right hn (Nat.cast_nonneg _)
      _ = _ := one_mul _
  have ha : (∑ N : OriginalNormalQuotientAxisInjection.Above Z, f N.val) ≤
      completeQuotientWeight (R := G ⧸ Z) J := by
    have h0 := OriginalNormalQuotientAxisInjection.above_epi_sum_le (J := J) Z
    dsimp only [f]
    unfold completeQuotientWeight completeQuotientCount
    rw [Nat.cast_sum]
    convert h0 using 1 <;>
      (apply Finset.sum_congr (by ext N; simp); intro N _; rfl)
  have hsum : (∑ N : Ax, f N) ≤
      (Nat.card (GroupEpimorphism J G) : ℝ) + completeQuotientWeight (R := G ⧸ Z) J := by
    rw [← Fintype.sum_subtype_add_sum_subtype (fun N : Ax => Z ≤ N.val) f]
    exact (add_le_add ha hb).trans_eq (add_comm _ _)
  conv_lhs =>
    unfold completeQuotientWeight completeQuotientCount
    rw [Nat.cast_sum]
  convert hsum using 1 <;>
    (apply Finset.sum_congr (by ext N; simp); intro N _; rfl)

theorem complete_weight_le_two (Z : Subgroup G) [Z.Normal]
    (hZ : ∀ (N : Subgroup G) [N.Normal], N ≠ ⊥ → Z ≤ N)
    (M : Subgroup (G ⧸ Z)) [M.Normal]
    (hM : ∀ (N : Subgroup (G ⧸ Z)) [N.Normal], N ≠ ⊥ → M ≤ N)
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) :
    completeQuotientWeight (R := G) J ≤
      (Nat.card (GroupEpimorphism J G) : ℝ) +
        (Nat.card (GroupEpimorphism J (G ⧸ Z)) : ℝ) +
          completeQuotientWeight (R := (G ⧸ Z) ⧸ M) J := by
  have h := add_le_add_right (complete_weight_le M hM J)
    (Nat.card (GroupEpimorphism J G) : ℝ)
  exact (complete_weight_le Z hZ J).trans (by simpa only [add_comm, add_left_comm,
    add_assoc] using h)

end SymmetricSubgroupAsymptotics.MonolithicCompleteQuotientReduction
