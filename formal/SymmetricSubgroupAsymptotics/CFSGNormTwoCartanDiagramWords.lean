import SymmetricSubgroupAsymptotics.CFSGNormTwoCartanDiagramRoots
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateCartan
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylWordDegree
import SymmetricSubgroupAsymptotics.CFSGIntegerHeightSign

/-! Actual Cartan diagram permutations transport the integral reflection
words and preserve positive root heights. This supplies word-independent
root labels for diagram--field actions without a stable total root order. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCartanDiagramWords
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGCartanDiagramLinearAction
open CFSGNormTwoCartanDiagramRoots CFSGNormTwoGeckWeylWordDegree
open CFSGIntegerHeightSign
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀ i, A i i = 2)
    (hs : A.transpose = A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀ i j, i ≠ j → A i j ≤ 0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsIrreducible]
    (p : Equiv.Perm (Fin r)) (hA : ∀ i j, A (p i) (p j) = A i j)

local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => CFSGNormTwoRootPairing.coordinateIndexEquiv A hd hs hp ho

theorem reflection_rootPermutation (a x : Roots A) :
    rootPermutation A p hA ((rootPairing A hs hp).reflectionPerm a x) =
      (rootPairing A hs hp).reflectionPerm (rootPermutation A p hA a)
        (rootPermutation A p hA x) := by
  apply Subtype.ext
  change permutationLinear p (x.val - integerPairing A x.val a.val • a.val) =
    permutationLinear p x.val -
      integerPairing A (permutationLinear p x.val) (permutationLinear p a.val) •
        permutationLinear p a.val
  rw [map_sub, map_smul, pairing_permutation A p hA]

theorem simple_rootPermutation (i : Fin r) :
    rootPermutation A p hA (s₀ i : Roots A) = (s₀ (p i) : Roots A) := by
  change rootPermutation A p hA (coordinateRoot A hd i) = coordinateRoot A hd (p i)
  exact rootPermutation_simple A p hA hd i

theorem wordRoot_permutation (w : List (Fin r)) (k : Roots A) :
    rootPermutation A p hA (wordRoot A hs hp b₀ s₀ w k) =
      wordRoot A hs hp b₀ s₀ (w.map p) (rootPermutation A p hA k) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change rootPermutation A p hA
      ((rootPairing A hs hp).reflectionPerm (s₀ i) (wordRoot A hs hp b₀ s₀ w k)) =
        (rootPairing A hs hp).reflectionPerm (s₀ (p i))
          (wordRoot A hs hp b₀ s₀ (w.map p) (rootPermutation A p hA k))
    rw [reflection_rootPermutation A hs hp p hA, ih, simple_rootPermutation A hd hs hp ho p hA]

theorem rootPermutation_positive (k : Roots A) (hk : ∀ i, 0 ≤ k.val i) :
    ∀ i, 0 ≤ (rootPermutation A p hA k).val i := by
  intro i
  exact hk (p.symm i)

theorem rootPermutation_height (k : Roots A) :
    height (rootPermutation A p hA k).val = height k.val := by
  change (∑ i, k.val (p.symm i)) = ∑ i, k.val i
  exact Equiv.sum_comp p.symm (fun i => k.val i)

end SymmetricSubgroupAsymptotics.CFSGNormTwoCartanDiagramWords
