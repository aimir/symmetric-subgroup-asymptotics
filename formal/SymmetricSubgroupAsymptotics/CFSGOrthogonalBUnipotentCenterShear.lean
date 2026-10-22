import SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotentCenterTests
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBShortCentralizer

/-! Every actual central element of the SAME odd-B Sylow unipotent
subgroup is an upper shear. The original quadratic short-root words
supply both coefficient commutation tests. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotent
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBGenerationShortArrays
variable {K : Type} [Field K]

theorem central_unipotent_is_shear (h2 : (2 : K) ≠ 0) (s : ℕ)
    (z : unipotent K (s + 2)) (hz : z ∈ Subgroup.center (unipotent K (s + 2))) :
    ∃ B : Matrix (Fin (s + 2)) (Fin (s + 2)) K,
      (z.val.val : Mat K (s + 2)) = Matrix.fromBlocks (Matrix.fromBlocks 1 B 0 1) 0 0 1 := by
  have hQ (i : Fin (s + 2)) :
      (z.val.val : Mat K (s + 2)) * Matrix.single (pos (s + 2) i) (neg (s + 2) i) 1 =
        Matrix.single (pos (s + 2) i) (neg (s + 2) i) 1 * (z.val.val : Mat K (s + 2)) := by
    have he := central_short_quadratic_commutes h2 (s + 1) z hz i
    have hs : shortSecond K (s + 2) (Sum.inl i) =
        -Matrix.single (pos (s + 2) i) (neg (s + 2) i) 1 := by
      ext x y
      simp only [shortSecond, paired, Sum.swap_inl, pos, neg, Matrix.single_apply, Matrix.neg_apply]
      split_ifs <;> simp
    rw [hs, mul_neg, neg_mul] at he
    exact neg_injective he
  refine ⟨(z.val.val : Mat K (s + 2)).submatrix (pos (s + 2)) (neg (s + 2)), ?_⟩
  exact shear_of_short_coefficient_commutation h2 s _ z.property.2 hQ
    (central_short_linear_commutes h2 (s + 1) z hz)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotent
