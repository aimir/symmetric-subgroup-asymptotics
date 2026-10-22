import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexProjectiveRootLift
import Mathlib.Data.Fin.VecNotation

/-! Original D root-product and commutation relations lift faithfully
through the actual scalar centre: at most six original polar forms have
a common nonzero fixed vector in dimension at least eight. This lifts
specific actual root relations, not arbitrary projective automorphisms. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexProjectiveRootProducts
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexFlagVectors
open CFSGOrthogonalDIndexPairOperator CFSGOrthogonalDIndexBundledQuadratic
open CFSGOrthogonalDIndexPositiveSpace CFSGOrthogonalDIndexProjectiveUnipotent
open CFSGOrthogonalDIndexProjectiveRootLift CFSGOrthogonalDIndexProjectiveFixedVector
open CFSGOrthogonalDIndexJointKernel
variable (K : Type) [Field K]

theorem exists_joint_fixed_roots {I : Type*} [Fintype I] (s : ℕ)
    (g : I → elementaryRootGroup K (s + 4)) (a : I → K)
    (hd : Fintype.card I * 2 < 2 * (s + 4)) :
    ∃ v : Index (s + 4) → K, v ≠ 0 ∧
      ∀ i, (((g i * highestRoot K s (a i) * (g i)⁻¹).val : Mat K (s + 4)) *ᵥ v) = v := by
  let B := (splitQuadraticForm K (s + 4)).polarBilin
  let f : (I × Fin 2) → Module.Dual K (Index (s + 4) → K) := fun i =>
    if i.2 = 0 then B (((g i.1).val : Mat K (s + 4)) *ᵥ firstVector K s)
    else B (((g i.1).val : Mat K (s + 4)) *ᵥ secondVector K s)
  obtain ⟨v, hv, hz⟩ := exists_nonzero_joint_kernel f (by
    rw [Fintype.card_prod, Fintype.card_fin, naturalSpace_finrank]
    exact hd)
  refine ⟨v, hv, ?_⟩
  intro i
  apply conjugate_highestRoot_fixed_of_two_forms_zero K s (g i) (a i) v
  · simpa only [f, if_pos rfl] using hz (i, (0 : Fin 2))
  · simpa [f] using hz (i, (1 : Fin 2))

theorem commute_of_projective_commute (s : ℕ)
    (g h : elementaryRootGroup K (s + 4)) (a b : K)
    (hc : Commute (projection K s (g * highestRoot K s a * g⁻¹))
      (projection K s (h * highestRoot K s b * h⁻¹))) :
    Commute (g * highestRoot K s a * g⁻¹) (h * highestRoot K s b * h⁻¹) := by
  let x := g * highestRoot K s a * g⁻¹
  let y := h * highestRoot K s b * h⁻¹
  obtain ⟨v, hv, hf⟩ := exists_joint_fixed_roots K s ![g, h] ![a, b] (by
    rw [Fintype.card_fin]
    omega)
  have hx : (x.val : Mat K (s + 4)) *ᵥ v = v := by simpa [x] using hf 0
  have hy : (y.val : Mat K (s + 4)) *ᵥ v = v := by simpa [y] using hf 1
  have he : projection K s (x * y) = projection K s (y * x) := by
    rw [map_mul, map_mul]
    exact hc.eq
  change x * y = y * x
  apply eq_of_projective_eq_of_joint_fixed K s _ _ he v hv
  · change ((x.val : Mat K (s + 4)) * (y.val : Mat K (s + 4))) *ᵥ v = v
    rw [← Matrix.mulVec_mulVec, hy, hx]
  · change ((y.val : Mat K (s + 4)) * (x.val : Mat K (s + 4))) *ᵥ v = v
    rw [← Matrix.mulVec_mulVec, hx, hy]

theorem product_eq_of_projective_eq (s : ℕ)
    (g h k : elementaryRootGroup K (s + 4)) (a b c : K)
    (he : projection K s ((g * highestRoot K s a * g⁻¹) * (h * highestRoot K s b * h⁻¹)) =
      projection K s (k * highestRoot K s c * k⁻¹)) :
    (g * highestRoot K s a * g⁻¹) * (h * highestRoot K s b * h⁻¹) =
      k * highestRoot K s c * k⁻¹ := by
  let x := g * highestRoot K s a * g⁻¹
  let y := h * highestRoot K s b * h⁻¹
  let z := k * highestRoot K s c * k⁻¹
  obtain ⟨v, hv, hf⟩ := exists_joint_fixed_roots K s ![g, h, k] ![a, b, c] (by
    rw [Fintype.card_fin]
    omega)
  have hx : (x.val : Mat K (s + 4)) *ᵥ v = v := by simpa [x] using hf 0
  have hy : (y.val : Mat K (s + 4)) *ᵥ v = v := by simpa [y] using hf 1
  have hz : (z.val : Mat K (s + 4)) *ᵥ v = v := by simpa [z] using hf 2
  apply eq_of_projective_eq_of_joint_fixed K s _ _ he v hv
  · change ((x.val : Mat K (s + 4)) * (y.val : Mat K (s + 4))) *ᵥ v = v
    rw [← Matrix.mulVec_mulVec, hy, hx]
  · exact hz

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexProjectiveRootProducts
