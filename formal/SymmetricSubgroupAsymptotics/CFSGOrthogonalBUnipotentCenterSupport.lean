import SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotentCenterShear
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBUpperShearChain
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBIndexForm
import SymmetricSubgroupAsymptotics.CFSGSkewUpperCentralizer

/-! A central element of the actual odd-B unipotent group has only its
highest long-root parameter free. This is a necessary support theorem,
not an assumed root-recognition or automorphism statement. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotent
open CFSGOrthogonalBSerreMatrices
variable {K : Type} [Field K]

theorem central_unipotent_highest_root_support (h2 : (2 : K) ≠ 0) (s : ℕ)
    (z : unipotent K (s + 2)) (hz : z ∈ Subgroup.center (unipotent K (s + 2))) :
    let k : Fin (s + 2) := ⟨1, by omega⟩
    ∃ a : K, (z.val.val : Mat K (s + 2)) =
      upperShearMatrix (s + 2) (Matrix.single 0 k a - Matrix.single k 0 a) := by
  let k : Fin (s + 2) := ⟨1, by omega⟩
  change ∃ a : K, (z.val.val : Mat K (s + 2)) =
    upperShearMatrix (s + 2) (Matrix.single 0 k a - Matrix.single k 0 a)
  obtain ⟨B, hB⟩ := central_unipotent_is_shear h2 s z hz
  change (z.val.val : Mat K (s + 2)) = upperShearMatrix (s + 2) B at hB
  have hf := CFSGOrthogonalBIndexForm.elementary_le_formUnits h2 (s + 2) z.val.property
  change (z.val.val : Mat K (s + 2)).transpose * gram K (s + 2) *
    (z.val.val : Mat K (s + 2)) = gram K (s + 2) at hf
  rw [hB] at hf
  obtain ⟨hskew, hdiag⟩ := upperShear_alternating_of_form h2 (s + 2) B hf
  have hcomm (i j : Fin (s + 2)) (hij : i < j) :
      Matrix.single i j 1 * B + B * Matrix.single j i 1 = 0 := by
    have he := congrArg (fun u : unipotent K (s + 2) => (u.val.val : Mat K (s + 2)))
      (Subgroup.mem_center_iff.mp hz (chainInU K (s + 2) i j hij 1)).symm
    change (z.val.val : Mat K (s + 2)) *
        ((chainElement K (s + 2) i j (ne_of_lt hij) 1).val : Mat K (s + 2)) =
      ((chainElement K (s + 2) i j (ne_of_lt hij) 1).val : Mat K (s + 2)) *
        (z.val.val : Mat K (s + 2)) at he
    rw [chainElement_val, one_smul] at he
    simp only [mul_add, add_mul, mul_one, one_mul] at he
    have hc := add_left_cancel he
    rw [hB] at hc
    exact upperShear_chain_commutation (s + 2) B i j hc
  have hs := CFSGSkewUpperCentralizer.skew_upper_centralizer (s + 1)
    (Nat.succ_pos s) B hskew hdiag hcomm
  change B = Matrix.single 0 k (B 0 k) - Matrix.single k 0 (B 0 k) at hs
  exact ⟨B 0 k, hB.trans (congrArg (upperShearMatrix (s + 2)) hs)⟩

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotent
