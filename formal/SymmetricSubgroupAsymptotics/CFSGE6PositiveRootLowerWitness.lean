import SymmetricSubgroupAsymptotics.CFSGExceptionalGeckIntegralData
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveRootGenerators

/-! Thirty-six explicit positive E6 roots give a LOWER bound only.
No exhaustive root census or order formula is assumed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGE6PositiveRootLowerWitness
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoCoordinatePositiveRootGenerators

private def rows : Fin 36 → Fin 6 → ℤ :=
  ![
  ![0, 0, 0, 0, 0, 1],
  ![0, 0, 0, 0, 1, 0],
  ![0, 0, 0, 0, 1, 1],
  ![0, 0, 0, 1, 0, 0],
  ![0, 0, 0, 1, 1, 0],
  ![0, 0, 0, 1, 1, 1],
  ![0, 0, 1, 0, 0, 0],
  ![0, 0, 1, 1, 0, 0],
  ![0, 0, 1, 1, 1, 0],
  ![0, 0, 1, 1, 1, 1],
  ![0, 1, 0, 0, 0, 0],
  ![0, 1, 0, 1, 0, 0],
  ![0, 1, 0, 1, 1, 0],
  ![0, 1, 0, 1, 1, 1],
  ![0, 1, 1, 1, 0, 0],
  ![0, 1, 1, 1, 1, 0],
  ![0, 1, 1, 1, 1, 1],
  ![0, 1, 1, 2, 1, 0],
  ![0, 1, 1, 2, 1, 1],
  ![0, 1, 1, 2, 2, 1],
  ![1, 0, 0, 0, 0, 0],
  ![1, 0, 1, 0, 0, 0],
  ![1, 0, 1, 1, 0, 0],
  ![1, 0, 1, 1, 1, 0],
  ![1, 0, 1, 1, 1, 1],
  ![1, 1, 1, 1, 0, 0],
  ![1, 1, 1, 1, 1, 0],
  ![1, 1, 1, 1, 1, 1],
  ![1, 1, 1, 2, 1, 0],
  ![1, 1, 1, 2, 1, 1],
  ![1, 1, 1, 2, 2, 1],
  ![1, 1, 2, 2, 1, 0],
  ![1, 1, 2, 2, 1, 1],
  ![1, 1, 2, 2, 2, 1],
  ![1, 1, 2, 3, 2, 1],
  ![1, 2, 2, 3, 2, 1]]

private theorem rows_norm : ∀ i, integerPairing CartanMatrix.E₆ (rows i) (rows i) = 2 := by decide
private theorem rows_positive : ∀ i j, 0 ≤ rows i j := by decide
private theorem rows_injective : Function.Injective rows := by decide

def positiveWitness (i : Fin 36) : PositiveRoot CartanMatrix.E₆ :=
  ⟨⟨rows i, rows_norm i⟩, rows_positive i⟩

theorem positiveWitness_injective : Function.Injective positiveWitness := by
  intro i j h
  exact rows_injective (congrArg (fun x : PositiveRoot CartanMatrix.E₆ => x.val.val) h)

theorem positive_root_card_lower : 36 ≤ Nat.card (PositiveRoot CartanMatrix.E₆) := by
  calc
    36 = Nat.card (Fin 36) := by simp
    _ ≤ Nat.card (PositiveRoot CartanMatrix.E₆) :=
      Nat.card_le_card_of_injective positiveWitness positiveWitness_injective

end SymmetricSubgroupAsymptotics.CFSGE6PositiveRootLowerWitness
