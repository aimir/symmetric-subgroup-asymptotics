import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeFixedGroup
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDTerminalRootCommutation
import Mathlib.Tactic.FinCases

/-! The literal paired Weyl word in the genuine rank-two carrier sends
the negative first pole to the negative of the positive first pole. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDRankTwoWeyl
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGTwistedDRelativeElementaryGroup CFSGSerreOrdinaryTwists

def weyl (q : CFSG.PrimePower) : relativeRootGroup 0 q :=
  ⟨pairedRoot 0 q false (-1) * pairedRoot 0 q true 1 * pairedRoot 0 q false (-1),
    (relativeRootGroup 0 q).mul_mem
      ((relativeRootGroup 0 q).mul_mem (paired_mem 0 q false (-1)) (paired_mem 0 q true 1))
      (paired_mem 0 q false (-1))⟩

theorem negative_axis (q : CFSG.PrimePower) :
    (↑(weyl q).val : Mat (q.Extension 2) 2) *ᵥ Pi.single (Sum.inr 0) 1 =
      -Pi.single (Sum.inl 0) 1 := by
  change ((↑(pairedRoot 0 q false (-1)) : Mat (q.Extension 2) 2) *
      (↑(pairedRoot 0 q true 1) : Mat (q.Extension 2) 2) *
      (↑(pairedRoot 0 q false (-1)) : Mat (q.Extension 2) 2)) *ᵥ _ = _
  have hn : previous 2 (1 : Fin 2) = (0 : Fin 2) := by decide
  funext x
  cases x with
  | inl i =>
    fin_cases i <;>
      simp [pairedRoot, rootTransvection, rootMatrix, negative, positive, pen, last,
        Units.val_mul, Matrix.mulVec, Matrix.mul_apply, dotProduct,
        Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.single_apply, Matrix.one_apply,
        Pi.single_apply, map_neg, map_one, hn]
  | inr i =>
    fin_cases i <;>
      simp [pairedRoot, rootTransvection, rootMatrix, negative, positive, pen, last,
        Units.val_mul, Matrix.mulVec, Matrix.mul_apply, dotProduct,
        Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.single_apply, Matrix.one_apply,
        Pi.single_apply, map_neg, map_one, hn]

theorem negative_axis_parameter (q : CFSG.PrimePower) (a : q.Extension 2) :
    (↑(weyl q).val : Mat (q.Extension 2) 2) *ᵥ Pi.single (Sum.inr 0) a =
      Pi.single (Sum.inl 0) (-a) := by
  have he : (Pi.single (Sum.inr 0) a : Index 2 → q.Extension 2) =
      a • Pi.single (Sum.inr 0) 1 := by
    funext x
    simp [Pi.single_apply, smul_eq_mul]
  rw [he, Matrix.mulVec_smul, negative_axis]
  funext x
  by_cases hx : x = Sum.inl 0 <;> simp [Pi.single_apply, smul_eq_mul, hx]

end SymmetricSubgroupAsymptotics.CFSGTwistedDRankTwoWeyl
