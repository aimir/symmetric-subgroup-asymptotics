import SymmetricSubgroupAsymptotics.Non2PreE7CompleteCharacterIntervalSource
import SymmetricSubgroupAsymptotics.Non2PreE7SmallModelToolkit

/-!
# Complete quotient weights above a minimal self-centralizing normal subgroup

Let `E` be minimal normal and self-centralizing in a finite group `G`.
Every nonbottom normal subgroup of `G` contains `E`.  Consequently the
whole literal normal menu of `G` consists of the bottom axis, together with
an interval which injects by normal correspondence into the complete normal
menu of `G / E`.

This is the action-free form needed by the distinct-sign degree-three
four-block branch.  The bottom axis is deliberately kept as the actual
epimorphism count onto `G`; no independent maximum is taken.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

-- Match the canonical literal-axis enumeration used by the interval
-- theorem imported above.
attribute [-instance] originalNormalFintype

private abbrev NormalAxis (G : Type*) [Group G] :=
  {N : Subgroup G // N.Normal}

private abbrev NormalAxisBelow {G : Type*} [Group G]
    (E : Subgroup G) :=
  {N : NormalAxis G // ¬ E ≤ N.1}

/-- Below a minimal self-centralizing normal subgroup there is only the
bottom literal normal axis. -/
theorem normalAxis_eq_bot_of_not_le_minimal_selfCentralizing
    {G : Type*} [Group G]
    (E : Subgroup G) [E.Normal]
    (hmin : ∀ W : Subgroup G, W.Normal → W ≤ E → W = ⊥ ∨ W = E)
    (hself : ∀ g : G, (∀ e ∈ E, g * e = e * g) → g ∈ E)
    (N : Subgroup G) [N.Normal] (hN : ¬ E ≤ N) :
    N = ⊥ := by
  by_contra hNb
  exact hN (le_of_minimal_selfCentralizing E hmin hself N hNb)

/-- The complete weight of `G` is one bottom-axis count plus one correlated
complete quotient weight of `G / E`.  The coefficient of the quotient menu
is exactly one. -/
theorem completeQuotientWeight_le_quotient_add_epimorphism
    {G : Type*} [Group G] [Finite G]
    (E : Subgroup G) [E.Normal]
    (hmin : ∀ W : Subgroup G, W.Normal → W ≤ E → W = ⊥ ∨ W = E)
    (hself : ∀ g : G, (∀ e ∈ E, g * e = e * g) → g ∈ E)
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) :
    completeQuotientWeight (R := G) J ≤
      completeQuotientWeight (R := G ⧸ E) J +
        (Nat.card (GroupEpimorphism J G) : ℝ) := by
  let Q : NormalAxis G → Prop := fun N ↦ E ≤ N.1
  let f : NormalAxis G → ℝ := fun N ↦
    Nat.card (GroupEpimorphism J (G ⧸ N.1))
  have hsplit := Fintype.sum_subtype_add_sum_subtype Q f
  have habove :
      (∑ N : {N : NormalAxis G // Q N}, f N.1) ≤
        completeQuotientWeight (R := G ⧸ E) J := by
    exact normalAxisAbove_epimorphism_sum_le_completeQuotientWeight E J
  have hbelow_point : ∀ N : NormalAxisBelow E,
      f N.1 = (Nat.card (GroupEpimorphism J G) : ℝ) := by
    intro N
    haveI : N.1.1.Normal := N.1.2
    have hN : N.1.1 = ⊥ :=
      normalAxis_eq_bot_of_not_le_minimal_selfCentralizing
        E hmin hself N.1.1 N.2
    simp only [f]
    have hcard := fusionGroupEpimorphism_card_congr (MulEquiv.refl J)
      ((QuotientGroup.quotientMulEquivOfEq hN).trans
        QuotientGroup.quotientBot)
    exact_mod_cast hcard
  have hbelow_card : Nat.card (NormalAxisBelow E) ≤ 1 := by
    simpa using Nat.card_le_card_of_injective (fun _ ↦ ())
      (fun (N M : NormalAxisBelow E) _ ↦ by
        haveI : N.1.1.Normal := N.1.2
        have hN := normalAxis_eq_bot_of_not_le_minimal_selfCentralizing
          E hmin hself N.1.1 N.2
        haveI : M.1.1.Normal := M.1.2
        have hM := normalAxis_eq_bot_of_not_le_minimal_selfCentralizing
          E hmin hself M.1.1 M.2
        exact Subtype.ext (Subtype.ext (hN.trans hM.symm)))
  have hbelow :
      (∑ N : {N : NormalAxis G // ¬ Q N}, f N.1) ≤
        (Nat.card (GroupEpimorphism J G) : ℝ) := by
    calc
      (∑ N : {N : NormalAxis G // ¬ Q N}, f N.1) =
          (Nat.card (NormalAxisBelow E) : ℝ) *
            (Nat.card (GroupEpimorphism J G) : ℝ) := by
        simp_rw [hbelow_point]
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
          ← Nat.card_eq_fintype_card]
      _ ≤ 1 * (Nat.card (GroupEpimorphism J G) : ℝ) := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast hbelow_card
        · exact Nat.cast_nonneg _
      _ = _ := one_mul _
  unfold completeQuotientWeight completeQuotientCount
  rw [Nat.cast_sum]
  change (∑ N : NormalAxis G, f N) ≤ _
  rw [hsplit.symm]
  exact add_le_add habove hbelow

end SymmetricSubgroupAsymptotics

end
