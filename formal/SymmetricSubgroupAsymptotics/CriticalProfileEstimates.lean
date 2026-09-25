import SymmetricSubgroupAsymptotics.CriticalProductTransport

/-! Actual canonical/noncanonical critical-model families and their estimates. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- Canonical means that the actual model subgroup retains the original
product kernel under the proved coordinate transport. -/
def CriticalModelIsCanonical (p : CriticalProfile) (H : CriticalModelSubgroups p) : Prop :=
  (criticalProductQuotient p.abelianRank (criticalProfileNonabelianChoice p)).ker ≤
    (criticalModelSubgroupsEquivCoordinates p H).1

abbrev CriticalCanonicalModelSubgroups (p : CriticalProfile) :=
  {H : CriticalModelSubgroups p // CriticalModelIsCanonical p H}

abbrev CriticalNoncanonicalModelSubgroups (p : CriticalProfile) :=
  {H : CriticalModelSubgroups p // ¬ CriticalModelIsCanonical p H}

theorem criticalModelSubgroups_card_split (p : CriticalProfile) :
    Nat.card (CriticalModelSubgroups p) = Nat.card (CriticalCanonicalModelSubgroups p) +
      Nat.card (CriticalNoncanonicalModelSubgroups p) := by
  classical
  rw [← Nat.card_congr (Equiv.sumCompl (CriticalModelIsCanonical p)), Nat.card_sum]

/-- The exceptional estimate now counts the literal full model subgroups,
with all C2/V4/D8/E8 projection conditions preserved in the source family. -/
theorem criticalNoncanonicalModelSubgroups_card_le (p : CriticalProfile) :
    (Nat.card (CriticalNoncanonicalModelSubgroups p) : ℝ) ≤
      (exceptionalGaussianConstant / eulerProduct) * (binaryGaussianSum p.rank : ℝ) *
        (2 : ℝ) ^ (-((p.c2 : ℝ) / 2 + p.v4 + p.e8)) := by
  have hle : Nat.card (CriticalNoncanonicalModelSubgroups p) ≤
      Nat.card (CriticalProductNoncanonicalFull p.abelianRank (criticalProfileNonabelianChoice p)) := by
    apply Nat.card_le_card_of_injective
      (fun H : CriticalNoncanonicalModelSubgroups p ↦
        (⟨(criticalModelSubgroupsEquivCoordinates p H.1).1, H.2,
          criticalProfileCoordinateFull_nonabelian p _
            (criticalModelSubgroupsEquivCoordinates p H.1).2⟩ :
          CriticalProductNoncanonicalFull p.abelianRank (criticalProfileNonabelianChoice p)))
    intro H K h
    apply Subtype.ext
    apply (criticalModelSubgroupsEquivCoordinates p).injective
    apply Subtype.ext
    exact congrArg (fun L : CriticalProductNoncanonicalFull p.abelianRank
      (criticalProfileNonabelianChoice p) ↦ L.val) h
  have hb := criticalProduct_noncanonical_full_card_le p.abelianRank (criticalProfileNonabelianChoice p)
  rw [criticalProfile_product_loss, criticalProfile_product_rank] at hb
  exact (show (Nat.card (CriticalNoncanonicalModelSubgroups p) : ℝ) ≤
      (Nat.card (CriticalProductNoncanonicalFull p.abelianRank (criticalProfileNonabelianChoice p)) : ℝ)
      by exact_mod_cast hle).trans hb

/-- The full canonical family injects into all canonical lifts. -/
theorem criticalCanonicalModelSubgroups_card_le (p : CriticalProfile) :
    Nat.card (CriticalCanonicalModelSubgroups p) ≤ binarySubspaceCount p.rank := by
  have hle : Nat.card (CriticalCanonicalModelSubgroups p) ≤
      Nat.card {H : Subgroup (CriticalProfileCoordinateGroup p) //
        (criticalProductQuotient p.abelianRank (criticalProfileNonabelianChoice p)).ker ≤ H} := by
    apply Nat.card_le_card_of_injective
      (fun H : CriticalCanonicalModelSubgroups p ↦
        (⟨(criticalModelSubgroupsEquivCoordinates p H.1).1, H.2⟩ :
          {H : Subgroup (CriticalProfileCoordinateGroup p) //
            (criticalProductQuotient p.abelianRank (criticalProfileNonabelianChoice p)).ker ≤ H}))
    intro H K h
    apply Subtype.ext
    apply (criticalModelSubgroupsEquivCoordinates p).injective
    apply Subtype.ext
    exact congrArg (fun L : {H : Subgroup (CriticalProfileCoordinateGroup p) //
      (criticalProductQuotient p.abelianRank (criticalProfileNonabelianChoice p)).ker ≤ H} ↦ L.val) h
  rw [canonicalLift_count _ (criticalProductQuotient_surjective _ _), criticalProfile_product_rank] at hle
  exact hle

end SymmetricSubgroupAsymptotics
