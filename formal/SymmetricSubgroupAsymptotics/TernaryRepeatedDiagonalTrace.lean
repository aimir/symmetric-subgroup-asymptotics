import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin

/-! A selected diagonal receipt: on a ternary three-space, two equal
diagonal coordinates leave only four invertible diagonals. Trace
distinguishes both nonscalar ones from each other and from the scalars. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.TernaryRepeatedDiagonalTrace
open scoped BigOperators

theorem separation_receipt : ∀ (i j : Fin 3) (a b : Fin 3 → ZMod 3),i≠j →
    (∀ i,a i≠0) → (∀ i,b i≠0) →
    a i=a j → b i=b j →
    (¬∀ i,a i=a 0) →
    (∑ i,a i)=(∑ i,b i) → a=b := by decide +kernel

end SymmetricSubgroupAsymptotics.TernaryRepeatedDiagonalTrace
