import SymmetricSubgroupAsymptotics.BinarySymmetricTopPartitionSquare
import SymmetricSubgroupAsymptotics.PartitionFibonacciBound
import SymmetricSubgroupAsymptotics.BinarySymmetricTopFibonacciBudget

/-! Every faithful binary block group with actual full symmetric top
satisfies the GM cube from twelve blocks onward. The kernel may have
arbitrary correlations and arbitrary codimension. All partition and
numerical estimates are proved, rather than supplied as hypotheses. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinarySymmetricTopClassBound
open OriginalBlockClassBound BinarySymmetricTopFibonacciBudget

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [MulAction.IsPretransitive A X] [FaithfulSMul A Ω]
    [Finite A] [Finite Ω] [Finite X]
    (b : Ω → X) (hb : ∀ (a : A) (ω : Ω), b (a • ω) = a • b ω) (x0 : X)

include hb in
theorem class_cube_le_garonziMaroti
    (htwo : Nat.card (originalBlockFibre b x0) = 2)
    (hTop : Top (A := A) (X := X) = ⊤) (hX : 12 ≤ Nat.card X) :
    Nat.card (ConjClasses A)^3 ≤ 5^(Nat.card Ω-1) := by
  have hsquare : Nat.card (ConjClasses A)^2 ≤ budget (Nat.card X) :=
    (BinarySymmetricTopPartitionSquare.class_square_le_partitions b hb x0 htwo hTop).trans
      (Nat.mul_le_mul_left _ (PartitionFibonacciBound.partition_card_le_fib (Nat.card X)))
  have hbudget := budget_cube_le (Nat.card X) hX
  have hpow : (Nat.card (ConjClasses A)^3)^2 ≤
      (5^(2*Nat.card X-1))^2 := by
    calc
      (Nat.card (ConjClasses A)^3)^2 = (Nat.card (ConjClasses A)^2)^3 := by ring
      _ ≤ (budget (Nat.card X))^3 := Nat.pow_le_pow_left hsquare 3
      _ ≤ 5^(4*Nat.card X-2) := hbudget
      _ = (5^(2*Nat.card X-1))^2 := by
        rw [← pow_mul]
        congr 1
        omega
  have hc := (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp hpow
  have hd : 2*Nat.card X = Nat.card Ω := by
    have h := Nat.card_congr (ActualBlockWreathEmbedding.productEquiv b hb x0)
    rw [Nat.card_prod, htwo] at h
    exact h
  simpa only [hd] using hc

end SymmetricSubgroupAsymptotics.BinarySymmetricTopClassBound
