import SymmetricSubgroupAsymptotics.CFSGGradedMatrixGroupFirstLayer
import SymmetricSubgroupAsymptotics.CFSGGradedMatrixSingleDegreeSpan

/-! Products in the first two literal height layers. These identities
hold before imposing any root-space or characteristic assumptions. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGradedMatrixSecondLayerProducts
open CFSGGradedMatrixSupport CFSGGradedMatrixLieFirstLayer
open CFSGGradedMatrixSingleDegreeSpan
variable {I K : Type*} [Fintype I] [DecidableEq I] [Field K]

theorem firstPart_supported (weight : I→ℤ) (M : Matrix I I K) :
    Supported weight (fun z=>z+1) (firstPart weight M) := by
  intro i j hij
  change weight i≠weight j+1 at hij
  rw [firstPart_apply,if_neg hij]

theorem firstParts_product_supported (weight : I→ℤ) (M N : Matrix I I K) :
    Supported weight (fun z=>z+2) (firstPart weight M*firstPart weight N) := by
  apply supported_congr (supported_mul (firstPart_supported weight M) (firstPart_supported weight N))
  intro z
  dsimp only [Function.comp_apply]
  omega

theorem secondPart_positive_product (weight : I→ℤ) (M N : Matrix I I K)
    (hM : Positive weight M) (hN : Positive weight N) :
    degreePart weight (2:ℤ) (M*N)=firstPart weight M*firstPart weight N := by
  apply Matrix.ext
  intro i j
  change (if weight i=weight j+2 then (M*N) i j else 0)= _
  by_cases hij : weight i=weight j+2
  · rw [if_pos hij,Matrix.mul_apply,Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro k hk
    rw [firstPart_apply,firstPart_apply]
    by_cases hik : weight i=weight k+1
    · have hkj : weight k=weight j+1 := by omega
      rw [if_pos hik,if_pos hkj]
    · rw [if_neg hik,zero_mul]
      by_cases hle : weight i≤weight k
      · rw [hM i k hle,zero_mul]
      · have hkj : weight k≤weight j := by omega
        rw [hN k j hkj,mul_zero]
  · rw [if_neg hij]
    exact (firstParts_product_supported weight M N i j hij).symm

theorem secondPart_height_two_times_positive_zero (weight : I→ℤ) (M N : Matrix I I K)
    (hM : ∀i j,weight i≤weight j+1→M i j=0) (hN : Positive weight N) :
    degreePart weight (2:ℤ) (M*N)=0 := by
  apply Matrix.ext
  intro i j
  change (if weight i=weight j+2 then (M*N) i j else 0)=0
  by_cases hij : weight i=weight j+2
  · rw [if_pos hij,Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k hk
    by_cases hik : weight i≤weight k+1
    · rw [hM i k hik,zero_mul]
    · have hkj : weight k≤weight j := by omega
      rw [hN k j hkj,mul_zero]
  · rw [if_neg hij]

end SymmetricSubgroupAsymptotics.CFSGGradedMatrixSecondLayerProducts
