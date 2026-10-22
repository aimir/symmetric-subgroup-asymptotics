import SymmetricSubgroupAsymptotics.CFSGTwistedA2TriangularSimilitude
import SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentArrays
import Mathlib.Tactic.LinearCombination

/-! Unitriangular signed-form similitudes in dimension three are exactly
the literal norm-constrained arrays. This entry calculation is valid in
all characteristics, including two and three. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentArrays
open CFSGTwistedANaturalMatrices CFSGTwistedA2TriangularSimilitude
variable (K : Type) [Field K]

def generalUpperArray (a b d : K) : Mat K 2 := !![1, a, b; 0, 1, d; 0, 0, 1]

theorem signedReversal_two_array :
    (signedReversalUnit K 2 : Mat K 2) = !![0, 0, 1; 0, -1, 0; 1, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [signedReversalUnit_apply, signWeight, Fin.rev, Fin.ext_iff]

theorem generalUpper_form_entries (σ : K ≃+* K) (a b d c : K)
    (hform : (σ.toRingHom.mapMatrix (generalUpperArray K a b d)).transpose *
        (!![0, 0, 1; 0, -1, 0; 1, 0, 0] : Mat K 2) * generalUpperArray K a b d =
      c • (!![0, 0, 1; 0, -1, 0; 1, 0, 0] : Mat K 2)) :
    d = σ a ∧ σ b + b = σ d * d := by
  have hmapT : (σ.toRingHom.mapMatrix (generalUpperArray K a b d)).transpose =
      (!![1, 0, 0; σ a, 1, 0; σ b, σ d, 1] : Mat K 2) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [generalUpperArray, Matrix.transpose_apply, Matrix.map_apply,
        Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  have hprod : (σ.toRingHom.mapMatrix (generalUpperArray K a b d)).transpose *
        (!![0, 0, 1; 0, -1, 0; 1, 0, 0] : Mat K 2) * generalUpperArray K a b d =
      (!![0, 0, 1; 0, -1, -d + σ a; 1, a - σ d, b - σ d * d + σ b] : Mat K 2) := by
    rw [hmapT]
    simp only [generalUpperArray, Matrix.mul_fin_three]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] <;> ring
  rw [hprod] at hform
  have h12 := congrArg (fun A : Mat K 2 => A 1 2) hform
  have h22 := congrArg (fun A : Mat K 2 => A 2 2) hform
  change -d + σ a = c * 0 at h12
  change b - σ d * d + σ b = c * 0 at h22
  rw [mul_zero] at h12 h22
  constructor
  · linear_combination -h12
  · linear_combination h22

theorem upperArray_of_unitriangular_similitude (σ : K ≃+* K)
    (hσ : Function.Involutive σ) (M : Mat K 2) (c : K)
    (hu : M.BlockTriangular id) (hd : ∀ i, M i i = 1)
    (hform : (σ.toRingHom.mapMatrix M).transpose *
        (↑((signedReversalUnit K 2)⁻¹) : Mat K 2) * M =
      c • (↑((signedReversalUnit K 2)⁻¹) : Mat K 2)) :
    ∃ a b, NormCondition σ a b ∧ M = upperArray σ a b := by
  let a := M 0 1
  let b := M 0 2
  let d := M 1 2
  have h10 : M 1 0 = 0 := hu (by decide)
  have h20 : M 2 0 = 0 := hu (by decide)
  have h21 : M 2 1 = 0 := hu (by decide)
  have hm : M = generalUpperArray K a b d := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [generalUpperArray, a, b, d, h10, h20, h21, hd]
  rw [signedReversal_two_inv, signedReversal_two_array, hm] at hform
  obtain ⟨hd', hb⟩ := generalUpper_form_entries K σ a b d c hform
  rw [hd', hσ a] at hb
  refine ⟨a, b, ?_, ?_⟩
  · change b + σ b = a * σ a
    exact (add_comm b (σ b)).trans hb
  · rw [hm, hd']
    rfl

end SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentArrays
