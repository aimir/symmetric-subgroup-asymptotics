import SymmetricSubgroupAsymptotics.CFSGOrthogonalBElementaryCenter
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDMatrixWeylParity
import SymmetricSubgroupAsymptotics.CFSGMatrixIdentityExtension
import SymmetricSubgroupAsymptotics.CFSGProjectiveLinearEvenOrder

/-! The actual long-chain Weyl word in the natural B group. Its
identity extension of the D word has fourth power one and is nonscalar.
In odd characteristic this proves parity of the actual central quotient. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreMatrices
open CFSGMatrixIdentityExtension
variable (K : Type) [Field K]

theorem chain_positive_block (r : ℕ) (i : Fin r) :
    positive K (r + 1) i.castSucc = Matrix.fromBlocks
      (CFSGOrthogonalDSerreMatrices.positive K (r + 1) i.castSucc) 0 0 0 := by
  have hi : i.castSucc.val + 1 < r + 1 := by simp
  simp only [positive, CFSGOrthogonalDSerreMatrices.positive, dif_pos hi]
  ext x y
  rcases x with ((x | x) | ⟨⟩) <;> rcases y with ((y | y) | ⟨⟩) <;>
    simp [Matrix.fromBlocks, Matrix.single, pos, neg]

theorem chain_negative_block (r : ℕ) (i : Fin r) :
    negative K (r + 1) i.castSucc = Matrix.fromBlocks
      (CFSGOrthogonalDSerreMatrices.negative K (r + 1) i.castSucc) 0 0 0 := by
  have hi : i.castSucc.val + 1 < r + 1 := by simp
  simp only [negative, CFSGOrthogonalDSerreMatrices.negative,
    CFSGOrthogonalDSerreMatrices.positive, dif_pos hi,
    Matrix.transpose_sub, Matrix.transpose_single]
  ext x y
  rcases x with ((x | x) | ⟨⟩) <;> rcases y with ((y | y) | ⟨⟩) <;>
    simp [Matrix.fromBlocks, Matrix.single, pos, neg]

def chainWeyl (r : ℕ) : elementaryRootGroup K (r + 2) :=
  ⟨rootTransvection K (r + 2) false (Fin.last r).castSucc (-1) *
      rootTransvection K (r + 2) true (Fin.last r).castSucc 1 *
      rootTransvection K (r + 2) false (Fin.last r).castSucc (-1),
    (elementaryRootGroup K (r + 2)).mul_mem
      ((elementaryRootGroup K (r + 2)).mul_mem
        (rootTransvection_mem K (r + 2) false (Fin.last r).castSucc (-1))
        (rootTransvection_mem K (r + 2) true (Fin.last r).castSucc 1))
      (rootTransvection_mem K (r + 2) false (Fin.last r).castSucc (-1))⟩

theorem chainWeyl_val (r : ℕ) :
    ((chainWeyl K r).val : Mat K (r + 2)) =
      extend K (CFSGOrthogonalDSerreMatrices.Index (r + 2)) Unit
        (CFSGOrthogonalDSerreMatrices.chainWeylMatrix K (r + 1) (Fin.last r)) := by
  change (1 + (-1 : K) • rootMatrix K (r + 2) false (Fin.last r).castSucc +
      (-1 : K)^2 • rootSecond K (r + 2) false (Fin.last r).castSucc) *
    (1 + (1 : K) • rootMatrix K (r + 2) true (Fin.last r).castSucc +
      (1 : K)^2 • rootSecond K (r + 2) true (Fin.last r).castSucc) *
    (1 + (-1 : K) • rootMatrix K (r + 2) false (Fin.last r).castSucc +
      (-1 : K)^2 • rootSecond K (r + 2) false (Fin.last r).castSucc) = _
  simp only [rootSecond, positiveSecond, negativeSecond, Bool.false_eq_true,
    if_false, if_true, show (Fin.last r).castSucc.val + 1 < r + 2 by simp,
    smul_zero, add_zero, rootMatrix, neg_one_smul, one_smul, ← sub_eq_add_neg]
  rw [chain_positive_block, chain_negative_block, one_sub_zeroExtension,
    one_add_zeroExtension, ← map_mul, ← map_mul]
  rfl

theorem chainWeyl_four (r : ℕ) : chainWeyl K r ^ 4 = 1 := by
  apply Subtype.ext
  apply Units.ext
  change (((chainWeyl K r).val : Mat K (r + 2)) ^ 4) = 1
  rw [chainWeyl_val, ← map_pow, CFSGOrthogonalDSerreMatrices.chainWeylMatrix_four, map_one]

theorem chainWeyl_not_center (r : ℕ) (h2 : (2 : K) ≠ 0) :
    chainWeyl K r ∉ Subgroup.center (elementaryRootGroup K (r + 2)) := by
  intro h
  obtain ⟨c, hc⟩ := (elementaryRootGroup_center_iff_scalar K (r + 1) h2 (chainWeyl K r)).mp h
  rw [chainWeyl_val] at hc
  exact CFSGOrthogonalDSerreMatrices.chainWeylMatrix_nonscalar K (r + 1) (Fin.last r) c
    (scalar_of_extension_scalar _ _ _ _ _ hc)

theorem elementaryProjective_even_card (r : ℕ) (h2 : (2 : K) ≠ 0) :
    Even (Nat.card (elementaryProjective K (r + 2))) := by
  let q := QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (r + 2)))
  apply CFSGProjectiveLinearEvenOrder.even_card_of_nontrivial_fourth_root (q (chainWeyl K r))
  · intro h
    exact chainWeyl_not_center K r h2 ((QuotientGroup.eq_one_iff _).mp h)
  · rw [← map_pow, chainWeyl_four, map_one]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreMatrices
