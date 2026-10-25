import SymmetricSubgroupAsymptotics.PermutationWreathOrderedClassData
import SymmetricSubgroupAsymptotics.FiniteColoredPartitionEncoding
import SymmetricSubgroupAsymptotics.PermutationalWreathFinite

/-! A full symmetric wreath class bound for an arbitrary finite coefficient
group. Ordered cycle products give an injective class code, and the reversible
colored-partition encoding retains the shared total weight. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FullSymmetricWreathColoredPartitionBound

variable {C I : Type} [Group C] [Finite C] [Finite I]

local instance finiteClasses : Finite (ConjClasses C) :=
  Finite.of_surjective ConjClasses.mk ConjClasses.mk_surjective

theorem class_card_le_coloredParts :
    Nat.card (ConjClasses (PermutationalWreathProduct C (Equiv.Perm I) I)) ≤
      Nat.card (PermutationWreathClassData.ColoredParts (ConjClasses C) (Nat.card I)) :=
  Nat.card_le_card_of_injective PermutationWreathOrderedClassData.classData
    PermutationWreathOrderedClassData.classData_injective

theorem class_card_le_polynomial_fib :
    Nat.card (ConjClasses (PermutationalWreathProduct C (Equiv.Perm I) I)) ≤
      (Nat.card I+1)^Nat.card (ConjClasses C) * Nat.fib (Nat.card I+1) :=
  class_card_le_coloredParts.trans
    (FiniteColoredPartitionEncoding.color_card_le (ConjClasses C) (Nat.card I))

theorem class_card_le_three_color_fib (hC : Nat.card (ConjClasses C) ≤ 3) :
    Nat.card (ConjClasses (PermutationalWreathProduct C (Equiv.Perm I) I)) ≤
      (Nat.card I+1)^3 * Nat.fib (Nat.card I+1) :=
  class_card_le_polynomial_fib.trans
    (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) hC))

end SymmetricSubgroupAsymptotics.FullSymmetricWreathColoredPartitionBound
