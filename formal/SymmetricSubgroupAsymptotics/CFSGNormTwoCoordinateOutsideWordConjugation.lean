import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOutsideWordPositive
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateWeylRootMembership
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylWordAlgebra

/-! A positive coordinate outside a conjugating word certifies positive
membership of the literal conjugated root unit. All words and root units
use the same integral realization. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOutsideWordConjugation
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoGeckColumns
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckPositivePGroup
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylWordAlgebra
open CFSGNormTwoCoordinateWeylRootMembership CFSGNormTwoCoordinateOutsideWordPositive
open CFSGSerreQuadraticMatrix
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

theorem conjugate_rootWord_eq (K : Type) [Field K]
    (v w : List (Fin r)) (i : Fin r) (t : K) :
    wordUnit A hs hp b₀ s₀ K v*rootWord A hd hs hp ho K w i t*
      (wordUnit A hs hp b₀ s₀ K v)⁻¹=
        rootWord A hd hs hp ho K (v++w) i t := by
  dsimp only [rootWord]
  rw [wordUnit_append]
  group

theorem conjugate_rootWord_mem_positive (K : Type) [Field K]
    (v w : List (Fin r)) (i j : Fin r) (t : K)
    (hv : ∀a∈v,a≠j)
    (hj : 0<(wordRoot A hs hp b₀ s₀ w (s₀ i)).val j) :
    wordUnit A hs hp b₀ s₀ K v*rootWord A hd hs hp ho K w i t*
      (wordUnit A hs hp b₀ s₀ K v)⁻¹∈rootGroup A hs hp b₀ s₀ K false := by
  rw [conjugate_rootWord_eq]
  apply positive_word_mem A hd hs hp ho K (v++w) i t
  rw [wordRoot_append]
  exact wordRoot_nonnegative_of_outside_positive A hd hs hp ho v
    (wordRoot A hs hp b₀ s₀ w (s₀ i)) j hv hj

theorem conjugate_simple_mem_positive (K : Type) [Field K]
    (v : List (Fin r)) (i : Fin r) (t : K) (hv : ∀a∈v,a≠i) :
    wordUnit A hs hp b₀ s₀ K v*
      canonicalRoot (realizationData A hs hp b₀ s₀) K false i t*
        (wordUnit A hs hp b₀ s₀ K v)⁻¹∈rootGroup A hs hp b₀ s₀ K false := by
  have hj : 0<(wordRoot A hs hp b₀ s₀ [] (s₀ i)).val i := by
    change 0<(Pi.single i (1:ℤ) : Fin r→ℤ) i
    simp
  have h := conjugate_rootWord_mem_positive A hd hs hp ho K v [] i i t hv hj
  simpa only [rootWord,wordUnit,one_mul,inv_one,mul_one] using h

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOutsideWordConjugation
