import SymmetricSubgroupAsymptotics.IndexTwoConjugacyClassCount
import SymmetricSubgroupAsymptotics.BinaryEightBlockClassInduction

/-! An outside block interchange makes either half-action detect its
centralizer in the original two-block kernel. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TwoBlockCentralizerProjection
open PermutationCharacterRankSplit

variable {G X : Type} [Group G] [MulAction G X] [FaithfulSMul G X]
    (K : Subgroup G) (S : SubMulAction K X)
    (hswap : ∀ g : G, g ∉ K → ∀ x : S, g • (x : X) ∈ (Sᶜ : Set X))

include hswap in
/-- The SAME restriction projection detects every outside centralizer. -/
theorem injective_on_centralizers (g : G) (hg : g ∉ K) (a b : K)
    (ha : Commute g (a : G)) (hb : Commute g (b : G))
    (hab : projection (Sᶜ) a = projection (Sᶜ) b) : a = b := by
  have he (x : ↥(Sᶜ)) : (a : G) • (x : X) = (b : G) • (x : X) := by
    exact congrArg Subtype.val
      (Equiv.congr_fun (congrArg Subtype.val hab) x)
  apply Subtype.ext
  apply eq_of_smul_eq_smul (α := X)
  intro x
  by_cases hx : x ∈ S
  · have he' := he ⟨g • x,hswap g hg ⟨x,hx⟩⟩
    apply (MulAction.injective g)
    calc
      g • ((a : G) • x) = (a : G) • (g • x) := by
        simp only [← mul_smul, ha.eq]
      _ = (b : G) • (g • x) := he'
      _ = g • ((b : G) • x) := by
        simp only [← mul_smul, hb.eq]
  · exact he ⟨x,hx⟩

variable [Finite G] [Finite X]

include hswap in
/-- The correlated original kernel is split by its actual restriction
image and actual kernel; there is no replacement by the full product. -/
theorem double_class_card_le (hi : K.index = 2) :
    2 * Nat.card (ConjClasses G) ≤
      Nat.card (ConjClasses (Kernel (Sᶜ))) *
        Nat.card (ConjClasses (Image (Sᶜ))) + 3 * Nat.card (Image (Sᶜ)) := by
  have h := IndexTwoConjugacyClassCount.double_class_card_le K hi
    (projection (Sᶜ)) (injective_on_centralizers K S hswap)
  have hsplit := conjugacyClass_card_le_normal_mul_quotient (Kernel (Sᶜ))
  have hquot := conjugacyClass_card_congr
    (QuotientGroup.quotientKerEquivOfSurjective (projection (Sᶜ))
      (projection_surjective (Sᶜ)))
  rw [hquot] at hsplit
  omega

end SymmetricSubgroupAsymptotics.TwoBlockCentralizerProjection
