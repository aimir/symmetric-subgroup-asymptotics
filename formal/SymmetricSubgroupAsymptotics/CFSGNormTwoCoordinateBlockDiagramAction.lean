import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateWeylBlocks
import SymmetricSubgroupAsymptotics.CFSGNormTwoCartanDiagramWords

/-! Actual block-cell invariance under a Cartan diagram permutation
forces the literal Weyl root action to commute with that diagram. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateBlockDiagramAction
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoCoordinateWeylBlocks
open CFSGNormTwoCartanDiagramRoots CFSGNormTwoCartanDiagramWords
open CFSGNormTwoGeckWeylLatticeLinear CFSGNormTwoGeckWeylWordDegree
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]

theorem block_equality_root_action (v w : List (Fin r))
    (he : wordBlockPermutation A hd hs hp ho v=wordBlockPermutation A hd hs hp ho w)
    (k : Roots A) :
    wordRoot A hs hp (coordinateBase A hd hs hp ho) (coordinateIndexEquiv A hd hs hp ho) v k=
      wordRoot A hs hp (coordinateBase A hd hs hp ho) (coordinateIndexEquiv A hd hs hp ho) w k := by
  have hh := congrArg (fun e : Equiv.Perm (CFSGNormTwoRootSeparatingWeight.WeightBlock A)=>e (some k)) he
  change some (rootWordPermutation A hd hs hp ho v k)=
    some (rootWordPermutation A hd hs hp ho w k) at hh
  simpa only [rootWordPermutation_apply] using Option.some.inj hh

theorem block_invariance_root_commutes (p : Equiv.Perm (Fin r))
    (hA : ∀i j,A (p i) (p j)=A i j) (w : List (Fin r))
    (he : wordBlockPermutation A hd hs hp ho (w.map p)=wordBlockPermutation A hd hs hp ho w)
    (k : Roots A) :
    rootPermutation A p hA
      (wordRoot A hs hp (coordinateBase A hd hs hp ho) (coordinateIndexEquiv A hd hs hp ho) w k)=
    wordRoot A hs hp (coordinateBase A hd hs hp ho) (coordinateIndexEquiv A hd hs hp ho) w
      (rootPermutation A p hA k) := by
  rw [wordRoot_permutation A hd hs hp ho p hA]
  exact block_equality_root_action A hd hs hp ho (w.map p) w he (rootPermutation A p hA k)

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateBlockDiagramAction
