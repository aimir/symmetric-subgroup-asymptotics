import SymmetricSubgroupAsymptotics.CFSGTwistedDHyperbolicBlockOperators
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDTerminalRootCommutation

/-! Exact terminal-root coordinates for the block fixing the LAST pair,
already when the smaller original split-D space has genuine rank two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankBlockRootCoordinates
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGTwistedDHyperbolicBlockCoordinates CFSGTwistedDHyperbolicBlockMatrices
open CFSGTwistedDHyperbolicBlockOperators CFSGOrthogonalDTerminalRootCommutation

theorem block_terminal_positive (K : Type) [Field K] (n : ℕ) (a : K) :
    (blockUnitHom K (n + 2) (rootTransvection K (n + 2) false (last n) a) : Mat K (n + 3)) =
      1 + Matrix.single (Sum.inl (pen n).castSucc) (Sum.inr (last n).castSucc) a -
        Matrix.single (Sum.inl (last n).castSucc) (Sum.inr (pen n).castSucc) a := by
  rw [blockUnitHom_root_val]
  simp only [rootMatrix, Bool.false_eq_true, if_false, positive_last,
    map_sub, zeroBlockLinear_single, blockIndex, smul_sub, Matrix.smul_single,
    smul_eq_mul, mul_one]
  abel

theorem block_terminal_negative (K : Type) [Field K] (n : ℕ) (a : K) :
    (blockUnitHom K (n + 2) (rootTransvection K (n + 2) true (last n) a) : Mat K (n + 3)) =
      1 + Matrix.single (Sum.inr (last n).castSucc) (Sum.inl (pen n).castSucc) a -
        Matrix.single (Sum.inr (pen n).castSucc) (Sum.inl (last n).castSucc) a := by
  rw [blockUnitHom_root_val]
  simp only [rootMatrix, if_true, negative, positive_last, Matrix.transpose_sub,
    Matrix.transpose_single, map_sub, zeroBlockLinear_single, blockIndex,
    smul_sub, Matrix.smul_single, smul_eq_mul, mul_one]
  abel

end SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankBlockRootCoordinates
