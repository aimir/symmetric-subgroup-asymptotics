import SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentWeyl

/-! Literal inverse-Weyl and opposite upper-array matrices. These retain
all parameters in the actual natural elementary group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentArrays
open CFSGTwistedANaturalMatrices
variable (K : Type) [Field K]

theorem weylNatural_inv_array (t : K) (ht : t ≠ 0) :
    (↑((weylNatural K t).val⁻¹) : Mat K 2) =
      !![0, 0, -t; 0, 1, 0; t⁻¹, 0, 0] := by
  let A : Mat K 2 := !![0, 0, -t; 0, 1, 0; t⁻¹, 0, 0]
  have hm : ((weylNatural K t).val : Mat K 2) * A = 1 := by
    rw [weylNatural_array K t ht]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply,
        Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] <;>
      field_simp [ht] <;> (try ring) <;> simp_all
  have hh := congrArg (fun B : Mat K 2 =>
    (↑((weylNatural K t).val⁻¹) : Mat K 2) * B) hm
  change (↑((weylNatural K t).val⁻¹) : Mat K 2) *
    (((weylNatural K t).val : Mat K 2) * A) =
      (↑((weylNatural K t).val⁻¹) : Mat K 2) * 1 at hh
  rw [← mul_assoc, Units.inv_mul, one_mul, mul_one] at hh
  exact hh.symm

def oppositeNatural (σ : K ≃+* K) (t a b : K) : NaturalElementary K 2 :=
  weylNatural K t * upperNatural K σ a b * (weylNatural K t)⁻¹

theorem oppositeNatural_array (σ : K ≃+* K) (t : K) (ht : t ≠ 0) (a b : K) :
    ((oppositeNatural K σ t a b).val : Mat K 2) =
      !![1, 0, 0; σ a / t, 1, 0; -b / t ^ 2, -a / t, 1] := by
  change (((weylNatural K t).val : Mat K 2) *
    ((upperNatural K σ a b).val : Mat K 2)) *
      (↑((weylNatural K t).val⁻¹) : Mat K 2) = _
  rw [weylNatural_array K t ht, upperNatural_val, weylNatural_inv_array K t ht]
  simp only [upperArray]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] <;>
    field_simp [ht]

end SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentArrays
