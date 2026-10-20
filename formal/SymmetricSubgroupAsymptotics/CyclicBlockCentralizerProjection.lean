import SymmetricSubgroupAsymptotics.NormalSubgroupConjugacyClassCount
import SymmetricSubgroupAsymptotics.BinaryEightBlockClassInduction

/-! A full cycle on the original block set lets one selected block detect
an outside centralizer. The actual kernel on the other blocks is retained. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CyclicBlockCentralizerProjection
open PermutationCharacterRankSplit

variable {G X : Type} [Group G] [MulAction G X] [FaithfulSMul G X]
    (K : Subgroup G) (S : SubMulAction K X)
    (hreach : ∀ g : G, g ∉ K → ∀ x : X, ∃ j : ℤ, (g^j) • x ∈ S)

include hreach in
theorem injective_on_centralizers (g : G) (hg : g ∉ K) (a b : K)
    (ha : Commute g (a : G)) (hb : Commute g (b : G))
    (hab : projection S a = projection S b) : a = b := by
  have he (x : S) : (a : G) • (x : X) = (b : G) • (x : X) := by
    exact congrArg Subtype.val
      (Equiv.congr_fun (congrArg Subtype.val hab) x)
  apply Subtype.ext
  apply eq_of_smul_eq_smul (α := X)
  intro x
  obtain ⟨j,hj⟩ := hreach g hg x
  have he' := he ⟨(g^j) • x,hj⟩
  apply (MulAction.injective (g^j))
  calc
    (g^j) • ((a : G) • x) = (a : G) • ((g^j) • x) := by
      simp only [← mul_smul, (ha.zpow_left j).eq]
    _ = (b : G) • ((g^j) • x) := he'
    _ = (g^j) • ((b : G) • x) := by
      simp only [← mul_smul, (hb.zpow_left j).eq]

variable [Finite G] [Finite X] [K.Normal]

include hreach in
theorem index_mul_class_card_le :
    K.index * Nat.card (ConjClasses G) + Nat.card (Image S) ≤
      Nat.card (ConjClasses (Kernel S)) * Nat.card (ConjClasses (Image S)) +
        K.index ^ 2 * Nat.card (Image S) := by
  have h := NormalSubgroupConjugacyClassCount.index_mul_class_card_le
    K (projection S) (injective_on_centralizers K S hreach)
  have hsplit := conjugacyClass_card_le_normal_mul_quotient (Kernel S)
  have hquot := conjugacyClass_card_congr
    (QuotientGroup.quotientKerEquivOfSurjective (projection S) (projection_surjective S))
  rw [hquot] at hsplit
  omega

end SymmetricSubgroupAsymptotics.CyclicBlockCentralizerProjection
