import SymmetricSubgroupAsymptotics.CFSGTwistedDHyperbolicBlockOperators
import SymmetricSubgroupAsymptotics.CFSGTwistedDRetainedForkRoots

/-! Literal simple-root coordinates of the block fixing the last
hyperbolic pair. Its terminal fork is the smaller split-D fork, rather
than either of the two ambient terminal simple roots. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDHyperbolicBlockRootCoordinates
open CFSGOrthogonalDSerreMatrices CFSGTwistedDHyperbolicBlockCoordinates
open CFSGTwistedDHyperbolicBlockMatrices CFSGTwistedDHyperbolicBlockOperators
open CFSGTwistedDA2MatrixWitness CFSGTwistedDRetainedForkRoots

def beforeLast (s : ℕ) : Fin (s + 3) := (Fin.last (s + 1)).castSucc

theorem beforeLast_ne_last (s : ℕ) : beforeLast s ≠ Fin.last (s + 2) := by
  intro h
  have hh := congrArg Fin.val h
  change s + 1 = s + 2 at hh
  omega

theorem block_chain_positive (K : Type) [Field K] (n : ℕ)
    (i : Fin n) (hi : i.val + 1 < n) (a : K) :
    (blockUnitHom K n (rootTransvection K n false i a) : Mat K (n + 1)) =
      1 + Matrix.single (Sum.inl i.castSucc)
          (Sum.inl ((⟨i.val + 1, hi⟩ : Fin n).castSucc)) a -
        Matrix.single (Sum.inr ((⟨i.val + 1, hi⟩ : Fin n).castSucc))
          (Sum.inr i.castSucc) a := by
  rw [blockUnitHom_root_val]
  simp only [rootMatrix, Bool.false_eq_true, if_false, positive, dif_pos hi,
    map_sub, zeroBlockLinear_single, blockIndex, smul_sub, Matrix.smul_single, smul_eq_mul, mul_one]
  abel

theorem block_chain_negative (K : Type) [Field K] (n : ℕ)
    (i : Fin n) (hi : i.val + 1 < n) (a : K) :
    (blockUnitHom K n (rootTransvection K n true i a) : Mat K (n + 1)) =
      1 + Matrix.single (Sum.inl ((⟨i.val + 1, hi⟩ : Fin n).castSucc))
          (Sum.inl i.castSucc) a -
        Matrix.single (Sum.inr i.castSucc)
          (Sum.inr ((⟨i.val + 1, hi⟩ : Fin n).castSucc)) a := by
  rw [blockUnitHom_root_val]
  simp only [rootMatrix, if_true, negative, positive, dif_pos hi,
    Matrix.transpose_sub, Matrix.transpose_single, map_sub,
    zeroBlockLinear_single, blockIndex, smul_sub, Matrix.smul_single, smul_eq_mul, mul_one]
  abel

theorem block_fork_positive (K : Type) [Field K] (s : ℕ) (a : K) :
    (blockUnitHom K (s + 3)
      (rootTransvection K (s + 3) false (Fin.last (s + 2)) a) : Mat K (s + 4)) =
      1 + Matrix.single (Sum.inl (beforeLast s).castSucc)
          (Sum.inr (Fin.last (s + 2)).castSucc) a -
        Matrix.single (Sum.inl (Fin.last (s + 2)).castSucc)
          (Sum.inr (beforeLast s).castSucc) a := by
  have hi : ¬(Fin.last (s + 2)).val + 1 < s + 3 := by simp
  have hp : previous (s + 3) (Fin.last (s + 2)) = beforeLast s := by
    apply Fin.ext
    simp only [previous_val, Fin.val_last, beforeLast, Fin.val_castSucc]
    omega
  rw [blockUnitHom_root_val]
  simp only [rootMatrix, Bool.false_eq_true, if_false, positive, dif_neg hi, hp,
    map_sub, zeroBlockLinear_single, blockIndex, smul_sub, Matrix.smul_single, smul_eq_mul, mul_one]
  abel

theorem block_fork_negative (K : Type) [Field K] (s : ℕ) (a : K) :
    (blockUnitHom K (s + 3)
      (rootTransvection K (s + 3) true (Fin.last (s + 2)) a) : Mat K (s + 4)) =
      1 + Matrix.single (Sum.inr (Fin.last (s + 2)).castSucc)
          (Sum.inl (beforeLast s).castSucc) a -
        Matrix.single (Sum.inr (beforeLast s).castSucc)
          (Sum.inl (Fin.last (s + 2)).castSucc) a := by
  have hi : ¬(Fin.last (s + 2)).val + 1 < s + 3 := by simp
  have hp : previous (s + 3) (Fin.last (s + 2)) = beforeLast s := by
    apply Fin.ext
    simp only [previous_val, Fin.val_last, beforeLast, Fin.val_castSucc]
    omega
  rw [blockUnitHom_root_val]
  simp only [rootMatrix, if_true, negative, positive, dif_neg hi, hp,
    Matrix.transpose_sub, Matrix.transpose_single, map_sub,
    zeroBlockLinear_single, blockIndex, smul_sub, Matrix.smul_single, smul_eq_mul, mul_one]
  abel

end SymmetricSubgroupAsymptotics.CFSGTwistedDHyperbolicBlockRootCoordinates
