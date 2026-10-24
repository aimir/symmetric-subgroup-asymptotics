import SymmetricSubgroupAsymptotics.CFSGSymplecticGeneralLinearDouble
import SymmetricSubgroupAsymptotics.CFSGSymplecticSymmetricShearMembership
import SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryProjectiveEquiv
import SymmetricSubgroupAsymptotics.BinarySymmetricSquareAction
import Mathlib.Algebra.Group.TypeTags.Hom

/-! Literal rank-two Siegel upper shears and the actual GL2 congruence
normalizer in the SAME elementary C2 matrices. Characteristic two is
needed only for the final original central-quotient injection. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGSymplecticRankTwoSiegelEmbedding

open BinarySymmetricSquareAction CFSGSymplecticSerreMatrices
variable (K : Type) [Field K]

/-- Actual additive symmetric matrices map to literal original upper shears. -/
def upperHom : Multiplicative (Space (K := K)) →* elementaryRootGroup K 2 where
  toFun s := ⟨CFSGMatrixShearUnits.upper s.toAdd.val,
    symmetric_upper_mem K 1 (by decide) s.toAdd.val s.toAdd.property⟩
  map_one' := by
    apply Subtype.ext
    exact CFSGMatrixShearUnits.upper_zero
  map_mul' s t := by
    apply Subtype.ext
    exact CFSGMatrixShearUnits.upper_add s.toAdd.val t.toAdd.val

theorem upperHom_injective : Function.Injective (upperHom K) := by
  intro s t he
  have hv := congrArg (fun u : elementaryRootGroup K 2 =>
    Matrix.toBlocks₁₂ (u.val : Mat K 2)) he
  change s.toAdd.val = t.toAdd.val at hv
  apply Multiplicative.toAdd.injective
  exact Subtype.ext hv

/-- The actual GL double acts on these actual shears by matrix congruence. -/
theorem double_upper_conjugation (A : GeneralLinear (K := K))
    (s : Multiplicative (Space (K := K))) :
    CFSGSymplecticGeneralLinearDouble.doubleIntoElementary K 2 A * upperHom K s *
      (CFSGSymplecticGeneralLinearDouble.doubleIntoElementary K 2 A)⁻¹ =
        upperHom K (Multiplicative.ofAdd (congruenceLinearMap A s.toAdd)) := by
  apply Subtype.ext
  exact CFSGSymplecticGeneralLinearDouble.doubleHom_upper_conjugation K 2 A s.toAdd.val

/-- The off-diagonal line is literal, with parameter visible in entry (0,1). -/
def offDiagonal (t : K) : Space (K := K) :=
  coordinates (Pi.single (1 : Fin 3) t)

theorem offDiagonal_ne_zero (t : K) (ht : t ≠ 0) : offDiagonal K t ≠ 0 := by
  intro he
  have hv := congrArg (fun S : Space (K := K) => S.val 0 1) he
  change t = 0 at hv
  exact ht hv

/-- In characteristic two the already-proved actual scalar centre is
trivial, so these actual upper shears survive the original quotient. -/
def projectiveUpperHom [CharP K 2] :
    Multiplicative (Space (K := K)) →* elementaryProjective K 2 :=
  (binaryProjectiveEquiv K 1).toMonoidHom.comp (upperHom K)

theorem projectiveUpperHom_injective [CharP K 2] :
    Function.Injective (projectiveUpperHom K) :=
  (binaryProjectiveEquiv K 1).injective.comp (upperHom_injective K)

end SymmetricSubgroupAsymptotics.CFSGSymplecticRankTwoSiegelEmbedding
