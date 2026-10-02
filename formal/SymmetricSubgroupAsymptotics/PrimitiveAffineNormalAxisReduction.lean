import SymmetricSubgroupAsymptotics.PrimitiveAffineSolubleDerivedTarget
import SymmetricSubgroupAsymptotics.GrowingQuotientTransferNumerics
import SymmetricSubgroupAsymptotics.FusionEpimorphismTransport

/-!
# Complete normal-axis reduction for primitive affine actions

For a primitive affine action, every nontrivial normal subgroup contains the
regular translation subgroup.  Hence every nonbottom quotient is a literal
quotient of one point stabilizer.  This file records that reduction directly
for the complete quotient weight, without a solubility hypothesis and without
choosing a finite catalogue representative.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineProfile

variable {L Ω : Type} [Group L] [Finite L] [MulAction L Ω] [Finite Ω]
  [Nontrivial Ω] [FaithfulSMul L Ω]
  (P : PrimitiveAffineProfile L Ω)

/-- Every nonbottom normal quotient of a primitive affine group is a literal
quotient of the point stabilizer.  The conclusion is already summed over all
normal axes of that stabilizer, which is the form needed by the fixed-target
composition argument. -/
theorem nonbottom_epimorphism_card_le_completeComplementWeight
    (hprimitive : MulAction.IsPreprimitive L Ω) (x : Ω)
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b)))
    (N : {N : Subgroup L // N.Normal}) (hN : N.1 ≠ ⊥) :
    (Nat.card (GroupEpimorphism J (L ⧸ N.1)) : ℝ) ≤
      completeQuotientWeight (R := P.complement x) J := by
  have hVle : P.V ≤ N.1 :=
    le_of_minimal_selfCentralizing P.V (P.minimal hprimitive)
      (P.selfCentralizing hprimitive) N.1 hN
  have hker : (P.complementProjection x).ker ≤ N.1 := by
    rw [P.complementProjection_ker x]
    exact hVle
  let M : Subgroup (P.complement x) :=
    N.1.map (P.complementProjection x)
  haveI hM : M.Normal :=
    N.2.map _ (P.complementProjection_surjective x)
  let e : (L ⧸ N.1) ≃* (P.complement x ⧸ M) :=
    quotientEquivOfKerLe (P.complementProjection x)
      (P.complementProjection_surjective x) N.1 hker
  rw [fusionGroupEpimorphism_card_congr (MulEquiv.refl J) e]
  exact card_groupEpimorphism_le_completeQuotientWeight J
    ⟨M, inferInstance⟩ (MulEquiv.refl _)

/-- The complete normal menu of a primitive affine action is bounded by the
number of its normal axes times one bottom affine fibre plus one complete
point-stabilizer menu.  This deliberately harmless fixed-target factor avoids
having to identify equal stabilizer axes; all source dependence remains in
the two displayed fibres. -/
theorem completeQuotientWeight_le_normalAxis_mul
    (hprimitive : MulAction.IsPreprimitive L Ω) (x : Ω)
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) :
    completeQuotientWeight (R := L) J ≤
      (Nat.card {N : Subgroup L // N.Normal} : ℝ) *
        ((Nat.card (GroupEpimorphism J L) : ℝ) +
          completeQuotientWeight (R := P.complement x) J) := by
  have hnat : completeQuotientCount (R := L) J ≤
      Nat.card {N : Subgroup L // N.Normal} *
        (Nat.card (GroupEpimorphism J L) +
          completeQuotientCount (R := P.complement x) J) := by
    unfold completeQuotientCount
    change
      (∑ N ∈ (@Finset.univ {N : Subgroup L // N.Normal}
          (Subtype.fintype Subgroup.Normal)),
        Nat.card (GroupEpimorphism J (L ⧸ N.1))) ≤ _
    let c : ℕ := Nat.card (GroupEpimorphism J L) +
      completeQuotientCount (R := P.complement x) J
    have hpoint : ∀ N : {N : Subgroup L // N.Normal},
        Nat.card (GroupEpimorphism J (L ⧸ N.1)) ≤ c := by
      intro N
      by_cases hN : N.1 = ⊥
      · let e : (L ⧸ N.1) ≃* L :=
          (QuotientGroup.quotientMulEquivOfEq hN).trans
            QuotientGroup.quotientBot
        rw [fusionGroupEpimorphism_card_congr (MulEquiv.refl J) e]
        exact Nat.le_add_right _ _
      · have h := P.nonbottom_epimorphism_card_le_completeComplementWeight
          hprimitive x J N hN
        unfold completeQuotientWeight at h
        have h' : Nat.card (GroupEpimorphism J (L ⧸ N.1)) ≤
            completeQuotientCount (R := P.complement x) J := by
          exact_mod_cast h
        exact h'.trans (Nat.le_add_left _ _)
    have hsum := Finset.sum_le_card_nsmul
      (@Finset.univ {N : Subgroup L // N.Normal}
        (Subtype.fintype Subgroup.Normal))
      (fun N => Nat.card (GroupEpimorphism J (L ⧸ N.1))) c
      (fun N _ => hpoint N)
    calc
      _ ≤ (@Fintype.card {N : Subgroup L // N.Normal}
            (Subtype.fintype Subgroup.Normal)) * c := by
        simpa [nsmul_eq_mul] using hsum
      _ = Nat.card {N : Subgroup L // N.Normal} *
          (Nat.card (GroupEpimorphism J L) +
            completeQuotientCount (R := P.complement x) J) := by
        rw [Fintype.card_eq_nat_card]
  unfold completeQuotientWeight
  exact_mod_cast hnat

end PrimitiveAffineProfile
end SymmetricSubgroupAsymptotics

end
