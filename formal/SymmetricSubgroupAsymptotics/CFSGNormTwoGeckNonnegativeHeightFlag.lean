import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylHeightBlocks
import SymmetricSubgroupAsymptotics.CFSGGradedMatrixTriangularUnits
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckPositivePGroup
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticWeylWord

/-! Every nonnegative simple-root grading gives a weak flag preserved
by the actual positive group. A word in zero-degree simple reflections
preserves every grading block. Both claims hold over arbitrary fields. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckNonnegativeHeightFlag
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckHeightSupport
open CFSGNormTwoGeckArbitraryHeightSupport CFSGNormTwoGeckWeylHeightBlocks
open CFSGNormTwoGeckPositivePGroup CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord
open CFSGGradedMatrixSubgroups CFSGGradedMatrixTriangularUnits
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

theorem positive_le_reverse_triangular (height : (n→ℤ)→ₗ[ℤ]ℤ)
    (hheight : ∀i : Fin r,0≤height (s i : Roots A).val) (K : Type) [Field K] :
    rootGroup A hs hp b s K false≤
      triangularUnits (fun j=> -weight A hs hp b height j) := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨⟨i,t⟩,rfl⟩
  rcases (hheight i).eq_or_lt with hz|hpos
  · intro x y hxy
    apply canonicalRoot_preserves A hs hp b s height K i t hz.symm x y
    change weight A hs hp b height x≠weight A hs hp b height y
    change -weight A hs hp b height y < -weight A hs hp b height x at hxy
    omega
  · exact strict_le_reverse_triangular _ (canonicalRoot_strict A hs hp b s height K i t hpos)

theorem zero_degree_word_preserving (height : (n→ℤ)→ₗ[ℤ]ℤ)
    (K : Type) [Field K] (w : List (Fin r))
    (hw : ∀i∈w,height (s i : Roots A).val=0) :
    canonicalWord (realizationData A hs hp b s) K w∈
      preservingUnits (weight A hs hp b height) := by
  induction w with
  | nil=>exact (preservingUnits _).one_mem
  | cons i w ih=>
    exact (preservingUnits _).mul_mem
      (weyl_preserves A hs hp b s height K i (hw i (by simp)))
      (ih (fun j hj=>hw j (by simp [hj])))

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckNonnegativeHeightFlag
