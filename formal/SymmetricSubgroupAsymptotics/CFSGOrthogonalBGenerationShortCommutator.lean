import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationShortArrays

/-! The genuine B short/short root commutator, retaining its coefficient
two. Inverting that coefficient will be used only in odd characteristic;
the symbolic identity itself holds over every field. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationShortCommutator
open Matrix CFSGOrthogonalBSerreMatrices CFSGOrthogonalBGenerationShortArrays
variable (K : Type) [Field K] (r : ℕ)

def longArray (b c : Fin r ⊕ Fin r) : Mat K r :=
  Matrix.single (Sum.inl b) (Sum.inl (paired r c)) 1 -
    Matrix.single (Sum.inl c) (Sum.inl (paired r b)) 1

set_option maxHeartbeats 600000 in
private theorem short_commutator_matrix (b c : Fin r ⊕ Fin r)
    (hbc : b ≠ c) (hbp : b ≠ paired r c) (a d : K) :
    (1 + a • shortArray K r b + a ^ 2 • shortSecond K r b) *
      (1 + d • shortArray K r c + d ^ 2 • shortSecond K r c) *
      (1 - a • shortArray K r b + a ^ 2 • shortSecond K r b) *
      (1 - d • shortArray K r c + d ^ 2 • shortSecond K r c) =
      1 + (-2 * a * d) • longArray K r b c := by
  have hpc : paired r b ≠ c := by
    intro he
    apply hbp
    have hh := congrArg (paired r) he
    simpa only [paired_paired] using hh
  have hpp : paired r b ≠ paired r c := by
    intro he
    apply hbc
    have hh := congrArg (paired r) he
    simpa only [paired_paired] using hh
  simp [shortArray, shortSecond, longArray, middle,
    mul_add, add_mul, mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm,
    hbc, hbc.symm, hbp, hbp.symm, hpc, hpc.symm, hpp, hpp.symm,
    paired_ne, (paired_ne r b).symm, (paired_ne r c).symm]
  all_goals ext i j
  all_goals simp [Matrix.single, Matrix.smul_apply]
  all_goals try split_ifs
  all_goals ring

theorem short_commutator_val (b c : Fin r ⊕ Fin r)
    (hbc : b ≠ c) (hbp : b ≠ paired r c) (a d : K) :
    ((shortUnit K r b a * shortUnit K r c d * (shortUnit K r b a)⁻¹ *
        (shortUnit K r c d)⁻¹ : (Mat K r)ˣ) : Mat K r) =
      1 + (-2 * a * d) • longArray K r b c := by
  simp only [Units.val_mul, shortUnit_inv_val, shortUnit_val]
  exact short_commutator_matrix K r b c hbc hbp a d

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationShortCommutator
