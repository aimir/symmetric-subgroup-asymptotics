import SymmetricSubgroupAsymptotics.CFSGOrthogonalDCoordinateDiagonal
import SymmetricSubgroupAsymptotics.CFSGTwistedDFrameReduction
import SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankPairedTorus
import SymmetricSubgroupAsymptotics.CFSGTwistedDNormOneTorusIndex

/-! Literal final-pair diagonals are the actual frame residues. The
retained norm/quotient fibre is realized by the original paired-torus
words in the same relative-root subgroup. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDResidualDiagonal
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDCoordinateDiagonal
open CFSGOrthogonalDIndexTailCoordinates CFSGTwistedDFrameReduction
open CFSGOrthogonalDGenerationForkTorus CFSGTwistedDAllRankPairedTorus
open CFSGTwistedDRelativeTorusParameters CFSGTwistedDNormOneTorusIndex
open CFSGTwistedDNormOneUnits CFSGTwistedDRelativeElementaryGroup

def residualDiagonalHom (n : ℕ) (q : CFSG.PrimePower) :
    normOneUnits q →* (Mat (q.Extension 2) (n + 2))ˣ :=
  (pairDiagonalHom (q.Extension 2) (n + 2) (last n)).comp (normOneUnits q).subtype

theorem residualEmbedding_diagonal (K : Type) [Field K] (n : ℕ) (c : Kˣ) :
    residualEmbedding K n (pairDiagonalHom K 1 0 c) =
      pairDiagonalHom K (n + 2) (last n) c := by
  induction n with
  | zero =>
    rw [residualEmbedding_zero, tail_pairDiagonalHom]
    rfl
  | succ n ih =>
    rw [residualEmbedding_succ, ih, tail_pairDiagonalHom]
    rfl

theorem pairedTorus_norm_one (n : ℕ) (q : CFSG.PrimePower) (c : (q.Extension 2)ˣ)
    (hn : normHom q c = 1) :
    (pairedTorus n q c).val = residualDiagonalHom n q (quotientHom q c) := by
  have hnorm : (c : q.Extension 2) * (unitFrobenius q c : q.Extension 2) = 1 := by
    have h := congrArg (fun z : (CFSGTwistedA2FixedField.fixedField q)ˣ =>
      ((z : CFSGTwistedA2FixedField.fixedField q) : q.Extension 2)) hn
    simpa only [normHom_val, Units.val_one, OneMemClass.coe_one, unitFrobenius_val] using h
  have hσ : (unitFrobenius q c : q.Extension 2) = (c : q.Extension 2)⁻¹ := by
    apply mul_left_cancel₀ (Units.ne_zero c)
    rw [hnorm, mul_inv_cancel₀ (Units.ne_zero c)]
  have hquot : ((quotientHom q c).val : q.Extension 2) =
      (unitFrobenius q c : q.Extension 2) * (c : q.Extension 2)⁻¹ := by
    change ((unitFrobenius q c * c⁻¹ : (q.Extension 2)ˣ) : q.Extension 2) = _
    rw [Units.val_mul, Units.val_inv_eq_inv_val]
  apply Units.ext
  rw [pairedTorus_val]
  change Matrix.diagonal (diagonal n q c) =
    (pairDiagonalHom (q.Extension 2) (n + 2) (last n) (quotientHom q c).val : _)
  rw [pairDiagonalHom_val]
  congr 1
  funext x
  rcases x with i | i
  · by_cases hp : i = pen n
    · subst i
      simp [diagonal, chainDiagonal, forkDiagonal, pen_ne_last, hnorm]
    · by_cases hl : i = last n
      · subst i
        simp only [diagonal, chainDiagonal, forkDiagonal, hp, if_false, if_true,
          Sum.elim_inl, hquot]
        exact mul_comm _ _
      · simp [diagonal, chainDiagonal, forkDiagonal, hp, hl]
  · by_cases hp : i = pen n
    · subst i
      simp [diagonal, chainDiagonal, forkDiagonal, pen_ne_last, hσ, Units.ne_zero]
    · by_cases hl : i = last n
      · subst i
        simp only [diagonal, chainDiagonal, forkDiagonal, hp, if_false, if_true,
          Sum.elim_inr, hquot, mul_inv_rev, inv_inv]
      · simp [diagonal, chainDiagonal, forkDiagonal, hp, hl]

theorem retained_residual_diagonal_mem (n : ℕ) (q : CFSG.PrimePower)
    (z : normOneUnits q) (hz : z ∈ retainedResidual q) :
    residualDiagonalHom n q z ∈ relativeRootGroup n q := by
  obtain ⟨c, hn, hc⟩ := (mem_retainedResidual_iff q z).mp hz
  rw [← hc, ← pairedTorus_norm_one n q c hn]
  exact pairedTorus_mem n q c

end SymmetricSubgroupAsymptotics.CFSGTwistedDResidualDiagonal
