import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeElementaryGroup
import SymmetricSubgroupAsymptotics.CFSGCommutingPairedWord
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDTerminalRootCommutation
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationForkAction
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDMatrixWeylParity

/-! The literal paired Weyl word is a product of four original sparse
coordinate rotations in every rank at least two. Only terminal-node
commutation is used, so the rank-three base is retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankPairedWeyl
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGOrthogonalDBinaryElements CFSGTwistedDRelativeElementaryGroup
open CFSGMatrixPairRotation

def weyl (n : ℕ) (q : CFSG.PrimePower) : relativeRootGroup n q :=
  ⟨pairedRoot n q false (-1) * pairedRoot n q true 1 * pairedRoot n q false (-1),
    (relativeRootGroup n q).mul_mem
      ((relativeRootGroup n q).mul_mem (paired_mem n q false (-1)) (paired_mem n q true 1))
      (paired_mem n q false (-1))⟩

theorem weyl_eq_nodes (n : ℕ) (q : CFSG.PrimePower) :
    (weyl n q).val = (simpleWeyl (q.Extension 2) (n + 2) (pen n) *
      simpleWeyl (q.Extension 2) (n + 2) (last n)).val := by
  let K := q.Extension 2
  let e : Fin 4 → Bool := ![false, true, false, false]
  let t : Fin 4 → K := ![-1, 1, -1, 0]
  let a : Fin 4 → elementaryRootGroup K (n + 2) :=
    fun i => rootElement K (n + 2) (e i) (pen n) (t i)
  let b : Fin 4 → elementaryRootGroup K (n + 2) :=
    fun i => rootElement K (n + 2) (e i) (last n) (t i)
  have hc (i j : Fin 4) : Commute (a i) (b j) := by
    change _ * _ = _ * _
    apply Subtype.ext
    exact (CFSGOrthogonalDTerminalRootCommutation.rootTransvection_commute
      K n (e i) (e j) (t i) (t j)).eq
  have h := congrArg (fun g : elementaryRootGroup K (n + 2) => g.val)
    (CFSGCommutingPairedWord.four_pairs a b hc)
  simpa [weyl, pairedRoot, a, b, e, t, simpleWeyl, map_neg, map_one] using h

theorem penWeyl_val (K : Type) [Field K] (n : ℕ) :
    ((simpleWeyl K (n + 2) (pen n)).val : Mat K (n + 2)) =
      chainWeylMatrix K (n + 1) (Fin.last n) := by
  change (1 + (-1 : K) • rootMatrix K (n + 2) false (pen n)) *
      (1 + (1 : K) • rootMatrix K (n + 2) true (pen n)) *
      (1 + (-1 : K) • rootMatrix K (n + 2) false (pen n)) = _
  simp only [rootMatrix, Bool.false_eq_true, if_false, if_true,
    neg_one_smul, one_smul, ← sub_eq_add_neg, chainWeylMatrix]
  rfl

theorem weyl_rotations (n : ℕ) (q : CFSG.PrimePower) :
    ((weyl n q).val : Mat (q.Extension 2) (n + 2)) =
      (rotation (q.Extension 2) (Sum.inl (pen n)) (Sum.inl (last n)) *
        rotation (q.Extension 2) (Sum.inr (pen n)) (Sum.inr (last n))) *
      (rotation (q.Extension 2) (Sum.inl (pen n)) (Sum.inr (last n)) *
        rotation (q.Extension 2) (Sum.inr (pen n)) (Sum.inl (last n))) := by
  rw [weyl_eq_nodes]
  change ((simpleWeyl (q.Extension 2) (n + 2) (pen n)).val : Mat (q.Extension 2) (n + 2)) *
    ((simpleWeyl (q.Extension 2) (n + 2) (last n)).val : Mat (q.Extension 2) (n + 2)) = _
  rw [penWeyl_val, CFSGOrthogonalDSerreMatrices.chainWeylMatrix_rotation,
    CFSGOrthogonalDGenerationForkAction.fork_rotations]
  rfl

end SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankPairedWeyl
