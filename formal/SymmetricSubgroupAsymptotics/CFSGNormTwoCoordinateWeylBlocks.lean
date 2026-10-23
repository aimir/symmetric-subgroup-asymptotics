import SymmetricSubgroupAsymptotics.CFSGNormTwoRootSeparatingWeight
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateCartan
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWordLatticeSupport
import Mathlib.Logic.Equiv.Option

/-! Actual Weyl words permute one block for each integral root and one
Cartan block in every finite coordinate norm-two lattice. The positive
separator is constructed generically; no exceptional root census occurs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateWeylBlocks
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoRootSeparatingWeight
open CFSGNormTwoGeckLatticeDegree CFSGNormTwoGeckHeightSupport
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylLatticeLinear
open CFSGNormTwoGeckWordLatticeSupport
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀j,A j j=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

abbrev GeckIndex := (b₀).support ⊕ Roots A

def geckBlock : GeckIndex A hd hs hp ho → WeightBlock A
  | Sum.inl _ => none
  | Sum.inr k => some k

omit [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible] in
theorem geckBlock_surjective (hr : 0 < r) :
    Function.Surjective (geckBlock A hd hs hp ho) := by
  intro a
  cases a with
  | none => exact ⟨Sum.inl (s₀ ⟨0,hr⟩),rfl⟩
  | some k => exact ⟨Sum.inr k,rfl⟩

omit [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible] in
theorem blockVector_geckBlock (i : GeckIndex A hd hs hp ho) :
    blockVector A (geckBlock A hd hs hp ho i) = latticeWeight A hs hp b₀ i := by
  cases i <;> rfl

omit [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible] in
theorem blockHeight_geckBlock (i : GeckIndex A hd hs hp ho) :
    blockHeight A (geckBlock A hd hs hp ho i) =
      -weight A hs hp b₀ (separatingHeight A) i := by
  cases i <;> simp only [blockHeight,geckBlock,blockVector,weight,map_zero]

def rootWordPermutation : List (Fin r) → Equiv.Perm (Roots A)
  | [] => Equiv.refl _
  | i::w => (rootWordPermutation w).trans ((rootPairing A hs hp).reflectionPerm (s₀ i))

omit [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible] in
theorem rootWordPermutation_apply (w : List (Fin r)) (k : Roots A) :
    rootWordPermutation A hd hs hp ho w k = wordRoot A hs hp b₀ s₀ w k := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change (rootPairing A hs hp).reflectionPerm (s₀ i)
      (rootWordPermutation A hd hs hp ho w k) = _
    rw [ih]
    rfl

def wordBlockPermutation (w : List (Fin r)) : Equiv.Perm (WeightBlock A) :=
  Equiv.optionCongr (rootWordPermutation A hd hs hp ho w)

theorem blockVector_wordBlockPermutation (w : List (Fin r)) (a : WeightBlock A) :
    blockVector A (wordBlockPermutation A hd hs hp ho w a) =
      wordLinear A hs hp b₀ s₀ w (blockVector A a) := by
  cases a with
  | none =>
    change (0 : Fin r → ℤ) = wordLinear A hs hp b₀ s₀ w 0
    exact (map_zero _).symm
  | some k =>
    change (rootWordPermutation A hd hs hp ho w k).val = wordLinear A hs hp b₀ s₀ w k.val
    rw [rootWordPermutation_apply]
    exact (wordLinear_root A hs hp b₀ s₀ w k).symm

theorem word_block_support (K : Type) [Field K] (w : List (Fin r))
    (i j : GeckIndex A hd hs hp ho)
    (hij : geckBlock A hd hs hp ho i ≠
      wordBlockPermutation A hd hs hp ho w (geckBlock A hd hs hp ho j)) :
    (wordUnit A hs hp b₀ s₀ K w : Matrix (GeckIndex A hd hs hp ho)
      (GeckIndex A hd hs hp ho) K) i j=0 := by
  apply word_lattice_support A hs hp b₀ s₀ K w i j
  intro he
  apply hij
  apply blockVector_injective A
  rw [blockVector_geckBlock,blockVector_wordBlockPermutation,blockVector_geckBlock]
  exact he

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateWeylBlocks
