import SymmetricSubgroupAsymptotics.CFSGGTwoSerreRepresentation
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDInvariantForm

/-! The SAME original G₂ rational image preserves the D4 hyperbolic form.
Consequently its quadratic fourth coefficient vanishes on the image, even
though this coefficient does not vanish on arbitrary eight by eight matrices. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoSerreMatrices
open CFSG.Models.Chevalley

 theorem positive_mem_orthogonal (i : Fin 2) : positive ℚ i∈
    skewAdjointMatricesLieSubalgebra (CFSGOrthogonalDSerreMatrices.gram ℚ 4) := by
  let S := skewAdjointMatricesLieSubalgebra (CFSGOrthogonalDSerreMatrices.gram ℚ 4)
  fin_cases i
  · change CFSGOrthogonalDSerreMatrices.positive ℚ 4 0+
        CFSGOrthogonalDSerreMatrices.positive ℚ 4 2+
        CFSGOrthogonalDSerreMatrices.positive ℚ 4 3∈S
    exact S.add_mem (S.add_mem
      (CFSGOrthogonalDSerreMatrices.positive_mem_orthogonal ℚ 4 0)
      (CFSGOrthogonalDSerreMatrices.positive_mem_orthogonal ℚ 4 2))
      (CFSGOrthogonalDSerreMatrices.positive_mem_orthogonal ℚ 4 3)
  · exact CFSGOrthogonalDSerreMatrices.positive_mem_orthogonal ℚ 4 1

 theorem negative_mem_orthogonal (i : Fin 2) : negative ℚ i∈
    skewAdjointMatricesLieSubalgebra (CFSGOrthogonalDSerreMatrices.gram ℚ 4) := by
  let S := skewAdjointMatricesLieSubalgebra (CFSGOrthogonalDSerreMatrices.gram ℚ 4)
  fin_cases i
  · change negative ℚ 0∈S
    rw [negative_zero]
    exact S.add_mem (S.add_mem
      (CFSGOrthogonalDSerreMatrices.negative_mem_orthogonal ℚ 4 0)
      (CFSGOrthogonalDSerreMatrices.negative_mem_orthogonal ℚ 4 2))
      (CFSGOrthogonalDSerreMatrices.negative_mem_orthogonal ℚ 4 3)
  · exact CFSGOrthogonalDSerreMatrices.negative_mem_orthogonal ℚ 4 1

 theorem rational_image_mem_orthogonal (x : RationalLie CartanMatrix.G₂) :
    rationalRepresentation x∈
      skewAdjointMatricesLieSubalgebra (CFSGOrthogonalDSerreMatrices.gram ℚ 4) := by
  let T := skewAdjointMatricesLieSubalgebra (CFSGOrthogonalDSerreMatrices.gram ℚ 4)
  let S := T.comap rationalRepresentation
  have hle : LieSubalgebra.lieSpan ℚ _ (Set.range (generator CartanMatrix.G₂))≤S := by
    apply LieSubalgebra.lieSpan_le.mpr
    rintro _ ⟨g,rfl⟩
    change rationalRepresentation (generator CartanMatrix.G₂ g)∈T
    cases g with
    | H i=>
      rw [rationalRepresentation_H]
      have he : ⁅positive ℚ i,negative ℚ i⁆=cartan ℚ i := by
        simpa only [if_pos rfl] using EF ℚ i i
      rw [←he]
      exact T.lie_mem (positive_mem_orthogonal i) (negative_mem_orthogonal i)
    | E i=>rw [rationalRepresentation_E];exact positive_mem_orthogonal i
    | F i=>rw [rationalRepresentation_F];exact negative_mem_orthogonal i
  rw [CFSGSerreLocalNilpotence.generator_lieSpan_eq_top] at hle
  exact hle (LieSubalgebra.mem_top x)

 theorem rational_image_fourth_coefficient_zero (x : RationalLie CartanMatrix.G₂)
    (negRoot : Bool) (i : Fin 2) :
    (if negRoot then negativeSecond ℚ i else positiveSecond ℚ i)*
      rationalRepresentation x*
      (if negRoot then negativeSecond ℚ i else positiveSecond ℚ i)=0 := by
  have hz := CFSGOrthogonalDSerreMatrices.orthogonal_opposite_entries_zero 4 _
    (rational_image_mem_orthogonal x) (2:Fin 4)
  by_cases hi : i=0
  · subst i
    cases negRoot
    · simp only [Bool.false_eq_true,if_false,positiveSecond,if_true,
        Matrix.single_mul_mul_single,hz.1,mul_zero,zero_mul,Matrix.single_zero]
    · simp only [if_true,negativeSecond,positiveSecond,Matrix.transpose_single,
        Matrix.single_mul_mul_single,hz.2,mul_zero,zero_mul,Matrix.single_zero]
  · cases negRoot <;>
      simp only [Bool.false_eq_true,if_false,if_true,negativeSecond,positiveSecond,
        if_neg hi,Matrix.transpose_zero,zero_mul,mul_zero]

end SymmetricSubgroupAsymptotics.CFSGGTwoSerreMatrices
