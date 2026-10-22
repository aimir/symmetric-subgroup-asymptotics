import SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotentCenterShear
import SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotentShortRoots
import SymmetricSubgroupAsymptotics.CFSGSymmetricUpperCentralizer

/-! Every actual central element of C-unipotent U has at most two
original field parameters. The second is annihilated by two. This is a
literal matrix theorem, with no abstract root-recognition premise. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotent
open CFSGSymplecticSerreMatrices
variable {K : Type} [Field K]

private theorem short_block (r : ℕ) (i j : Fin (r + 1)) :
    coordinateShortMatrix K r i j = Matrix.fromBlocks (Matrix.single i j 1) 0 0 (-Matrix.single j i 1) := by
  ext x y
  cases x <;> cases y <;>
    simp [coordinateShortMatrix, Matrix.fromBlocks, Matrix.single_apply] <;>
    split_ifs <;> simp_all

private theorem central_shear_short_condition (r : ℕ) (hr : 0 < r)
    (z : unipotent K (r + 1)) (hz : z ∈ Subgroup.center (unipotent K (r + 1)))
    (B : Matrix (Fin (r + 1)) (Fin (r + 1)) K)
    (hB : (z.val.val : Mat K (r + 1)) = Matrix.fromBlocks 1 B 0 1)
    (i j : Fin (r + 1)) (hij : i < j) :
    Matrix.single i j 1 * B + B * Matrix.single j i 1 = 0 := by
  have h := congrArg (fun u : unipotent K (r + 1) => (u.val.val : Mat K (r + 1)))
    (Subgroup.mem_center_iff.mp hz (coordinateShortInU K r hr i j hij 1)).symm
  change (z.val.val : Mat K (r + 1)) * (coordinateShortUnit K r i j (ne_of_lt hij) 1 : Mat K (r + 1)) =
    (coordinateShortUnit K r i j (ne_of_lt hij) 1 : Mat K (r + 1)) * (z.val.val : Mat K (r + 1)) at h
  rw [coordinateShortUnit_val, one_smul] at h
  simp only [mul_add, add_mul, mul_one, one_mul] at h
  have hX := add_left_cancel h
  rw [hB, short_block] at hX
  have hp := congrArg Matrix.toBlocks₁₂ hX
  simp only [Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₂,
    mul_zero, zero_mul, zero_add, add_zero, mul_one, one_mul, Matrix.mul_neg] at hp
  rw [← hp]
  exact neg_add_cancel _

theorem central_unipotent_two_parameters (r : ℕ) (hr : 0 < r)
    (z : unipotent K (r + 1)) (hz : z ∈ Subgroup.center (unipotent K (r + 1))) :
    let k : Fin (r + 1) := ⟨1, Nat.succ_lt_succ hr⟩
    ∃ a b : K, (2 : K) * b = 0 ∧
      (z.val.val : Mat K (r + 1)) = Matrix.fromBlocks 1
        (Matrix.single 0 0 a + Matrix.single 0 k b + Matrix.single k 0 b) 0 1 := by
  obtain ⟨B, hsym, hB⟩ := central_unipotent_is_symmetric_shear r hr z hz
  have hcomm := central_shear_short_condition r hr z hz B hB
  obtain ⟨hb, he⟩ := CFSGSymmetricUpperCentralizer.symmetric_upper_centralizer r hr B hsym hcomm
  refine ⟨B 0 0, B 0 ⟨1, Nat.succ_lt_succ hr⟩, hb, ?_⟩
  calc
    (z.val.val : Mat K (r + 1)) = Matrix.fromBlocks 1 B 0 1 := hB
    _ = _ := congrArg (fun C : Matrix (Fin (r + 1)) (Fin (r + 1)) K =>
      Matrix.fromBlocks (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) K) C 0 1) he

end SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotent
