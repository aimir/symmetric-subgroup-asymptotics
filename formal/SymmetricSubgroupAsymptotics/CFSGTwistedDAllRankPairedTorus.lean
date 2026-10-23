import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeElementaryGroup
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDCommutingNodeTori
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDTerminalRootCommutation
import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeTorusParameters

/-! Actual paired-torus words in the literal relative subgroup already
in ranks two and three. Their two diagonal parameters remain the norm
and Frobenius quotient of the original extension-field unit. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankPairedTorus
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDBinaryElements
open CFSGOrthogonalDGenerationForkTorus CFSGOrthogonalDForkNodeTori
open CFSGTwistedDRelativeElementaryGroup CFSGSerreOrdinaryTwists
open CFSGTwistedDRelativeTorusParameters

def pairedTorus (n : ℕ) (q : CFSG.PrimePower) (c : (q.Extension 2)ˣ) :
    elementaryRootGroup (q.Extension 2) (n + 2) :=
  nodeTorus (q.Extension 2) n (pen n) c *
    nodeTorus (q.Extension 2) n (last n) (unitFrobenius q c)

theorem pairedTorus_mem (n : ℕ) (q : CFSG.PrimePower) (c : (q.Extension 2)ˣ) :
    (pairedTorus n q c).val ∈ relativeRootGroup n q := by
  let H := (relativeRootGroup n q).comap
    (elementaryRootGroup (q.Extension 2) (n + 2)).subtype
  have hp (e : Bool) (a : q.Extension 2) :
      rootElement (q.Extension 2) (n + 2) e (pen n) a *
        rootElement (q.Extension 2) (n + 2) e (last n) (definingFieldAutomorphism q 2 a) ∈ H :=
    CFSGTwistedDRelativeElementaryGroup.paired_mem n q e a
  have hc (e f : Bool) (a b : q.Extension 2) :
      Commute (rootElement (q.Extension 2) (n + 2) e (pen n) a)
        (rootElement (q.Extension 2) (n + 2) f (last n) b) := by
    change _ * _ = _ * _
    apply Subtype.ext
    exact (CFSGOrthogonalDTerminalRootCommutation.rootTransvection_commute
      (q.Extension 2) n e f a b).eq
  exact CFSGOrthogonalDCommutingNodeTori.nodeTorus_pair_mem
    (q.Extension 2) n H (pen n) (last n) (definingFieldAutomorphism q 2).toRingHom c hc hp

def diagonal (n : ℕ) (q : CFSG.PrimePower) (c : (q.Extension 2)ˣ) :
    Index (n + 2) → q.Extension 2 :=
  fun i => chainDiagonal (q.Extension 2) n c i *
    forkDiagonal (q.Extension 2) n (unitFrobenius q c) i

theorem pairedTorus_val (n : ℕ) (q : CFSG.PrimePower) (c : (q.Extension 2)ˣ) :
    ((pairedTorus n q c).val : Mat (q.Extension 2) (n + 2)) =
      Matrix.diagonal (diagonal n q c) := by
  change ((nodeTorus (q.Extension 2) n (pen n) c).val : Mat (q.Extension 2) (n + 2)) *
    ((nodeTorus (q.Extension 2) n (last n) (unitFrobenius q c)).val :
      Mat (q.Extension 2) (n + 2)) = _
  rw [nodeTorus_pen_val, nodeTorus_last_val, Matrix.diagonal_mul_diagonal]
  rfl

theorem positive_pen (n : ℕ) (q : CFSG.PrimePower) (c : (q.Extension 2)ˣ)
    (v : Index (n + 2) → q.Extension 2) :
    (((pairedTorus n q c).val : Mat (q.Extension 2) (n + 2)) *ᵥ v) (Sum.inl (pen n)) =
      ((normHom q c : CFSGTwistedA2FixedField.fixedField q) : q.Extension 2) *
        v (Sum.inl (pen n)) := by
  rw [pairedTorus_val, Matrix.mulVec_diagonal, normHom_val]
  simp only [diagonal, chainDiagonal, forkDiagonal, if_true, unitFrobenius_val]

theorem positive_last (n : ℕ) (q : CFSG.PrimePower) (c : (q.Extension 2)ˣ)
    (v : Index (n + 2) → q.Extension 2) :
    (((pairedTorus n q c).val : Mat (q.Extension 2) (n + 2)) *ᵥ v) (Sum.inl (last n)) =
      ((quotientHom q c).val : q.Extension 2) * v (Sum.inl (last n)) := by
  have hq : ((quotientHom q c).val : q.Extension 2) =
      (unitFrobenius q c : q.Extension 2) * (c : q.Extension 2)⁻¹ := by
    change ((unitFrobenius q c * c⁻¹ : (q.Extension 2)ˣ) : q.Extension 2) = _
    rw [Units.val_mul, Units.val_inv_eq_inv_val]
  rw [pairedTorus_val, Matrix.mulVec_diagonal, hq]
  simp only [diagonal, chainDiagonal, forkDiagonal,
    if_neg (Ne.symm (pen_ne_last n)), if_true]
  ring

end SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankPairedTorus
