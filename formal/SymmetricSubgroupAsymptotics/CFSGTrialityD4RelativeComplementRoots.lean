import SymmetricSubgroupAsymptotics.CFSGTrialityD4PositiveRootIndex
import SymmetricSubgroupAsymptotics.CFSGSignedCartanReflections

/-! Literal D4 root certificates for the two relative rank-one
complements. The short reflection is the commuting outer word [0,2,3],
and the long reflection is [1]. Only the already proved twelve positive
root coordinates are tested; no ambient fixed-group cover is inferred. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTrialityD4RelativeComplementRoots
open CFSGTrialityD4PositiveRootIndex CFSGSignedCartanReflections

def shortStep : Matrix (Fin 4) (Fin 4) ℤ := latticeWord (CartanMatrix.D 4) [0,2,3]
def longStep : Matrix (Fin 4) (Fin 4) ℤ := latticeWord (CartanMatrix.D 4) [1]

theorem shortStep_central_row : shortStep 1 = (Pi.single 1 1 : Fin 4 → ℤ) := by decide

theorem longStep_outer_rows : ∀ i : Fin 4, i ≠ 1 →
    longStep i = (Pi.single i 1 : Fin 4 → ℤ) := by decide

theorem positive_central_zero : ∀ a : OrbitIndex,
    coordinates a 1 = 0 ↔ ∃ k : Fin 3, a = Sum.inr (0,k) := by decide

theorem positive_outer_sum_zero : ∀ a : OrbitIndex,
    coordinates a 0 + coordinates a 2 + coordinates a 3 = 0 ↔ a = Sum.inl 0 := by decide

theorem short_complement_positive : ∀ a : OrbitIndex,
    0 < coordinates a 1 → ∀ i : Fin 4, 0 ≤ (shortStep *ᵥ coordinates a) i := by decide

theorem long_complement_positive : ∀ a : OrbitIndex,
    0 < coordinates a 0 + coordinates a 2 + coordinates a 3 →
      ∀ i : Fin 4, 0 ≤ (longStep *ᵥ coordinates a) i := by decide

end SymmetricSubgroupAsymptotics.CFSGTrialityD4RelativeComplementRoots
