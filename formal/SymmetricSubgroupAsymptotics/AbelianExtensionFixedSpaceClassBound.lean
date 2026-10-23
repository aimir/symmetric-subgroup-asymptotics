import SymmetricSubgroupAsymptotics.AbelianActionClassBound
import SymmetricSubgroupAsymptotics.AbelianExtensionClassComparison

/-! Fixed-space class bounds for the original, possibly nonsplit,
abelian extension. Its literal quotient conjugation action is retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.AbelianExtensionFixedSpaceClassBound
open AbelianExtensionConjugation AbelianExtensionClassComparison
variable {G : Type*} [Group G] [Finite G] (N : Subgroup G) [N.Normal] [IsMulCommutative N]

theorem class_card_le_fixed (c : ℕ)
    (hfixed : ∀ h : G⧸N, h≠1 → Nat.card {n : N // quotientConjugation N h n=n} ≤ c) :
    Nat.card (ConjClasses G) ≤ Nat.card N+c*Nat.card (ConjClasses (G⧸N)) := by
  letI : CommGroup N := { (inferInstance : Group N) with mul_comm := mul_comm' }
  exact (class_card_le_associated_split N).trans
    (AbelianActionClassBound.class_card_le_fixed (quotientConjugation N) c hfixed)

theorem class_card_mul_quotient_le (c : ℕ)
    (hfixed : ∀ h : G⧸N, h≠1 → Nat.card {n : N // quotientConjugation N h n=n} ≤ c) :
    Nat.card (G⧸N)*Nat.card (ConjClasses G) ≤
      Nat.card N+c*(Nat.card (G⧸N)*Nat.card (ConjClasses (G⧸N))) := by
  letI : CommGroup N := { (inferInstance : Group N) with mul_comm := mul_comm' }
  exact (Nat.mul_le_mul_left _ (class_card_le_associated_split N)).trans
    (AbelianActionClassBound.class_card_mul_complement_le (quotientConjugation N) c hfixed)

end SymmetricSubgroupAsymptotics.AbelianExtensionFixedSpaceClassBound
