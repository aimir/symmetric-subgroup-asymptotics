import SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryCenterCoordinates
import SymmetricSubgroupAsymptotics.CFSGSymplecticMixedRootWeights
import SymmetricSubgroupAsymptotics.CFSGSymplecticBorelFirstColumns
import Mathlib.Tactic.Group

/-! The actual C-Borel acts on the two literal characteristic-two
centre coordinates by the distinct weights λ0² and λ0*λ1. No diagonal
or Borel decomposition premise is used. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotent
open CFSGSymplecticSerreMatrices CFSGSymplecticTransvectionGeometry
variable {K : Type} [Field K]

private theorem highestLong_as_natural (r : ℕ) (hr : 0 < r) (a : K) :
    (highestLongInU (K := K) r hr a).val =
      actualNaturalRootElement r hr (Pi.single (Sum.inl (0 : Fin (r + 1))) 1) a := by
  rw [highestLongInU_val]
  apply elementary_eq_of_mulVec_eq
  intro x
  rw [firstLongRoot_mulVec_eq_transvection, actualNaturalRootElement_apply]

theorem borel_highestLong_conjugation (r : ℕ) (hr : 0 < r)
    (g : borel K (r + 1)) (a : K) :
    g.val * (highestLongInU r hr a).val * g.val⁻¹ =
      (highestLongInU r hr (a *
        ((g.val.val : Mat K (r + 1)) (Sum.inl 0) (Sum.inl 0)) ^ 2)).val := by
  simp only [highestLong_as_natural r hr, actualNaturalRootElement_conjugation r hr,
    borel_first_vector r g, actualNaturalRootElement_smul]

theorem borel_highestShort_conjugation (r : ℕ) (hr : 0 < r)
    (g : borel K (r + 1)) (b : K) (hb : (2 : K) * b = 0) :
    let k : Fin (r + 1) := ⟨1, by omega⟩
    g.val * (highestShortInU r hr b).val * g.val⁻¹ =
      (highestShortInU r hr (b *
        ((g.val.val : Mat K (r + 1)) (Sum.inl 0) (Sum.inl 0)) *
        ((g.val.val : Mat K (r + 1)) (Sum.inl k) (Sum.inl k)))).val := by
  dsimp only
  let k : Fin (r + 1) := ⟨1, by omega⟩
  let v : Index (r + 1) → K := Pi.single (Sum.inl 0) 1
  let w : Index (r + 1) → K := Pi.single (Sum.inl k) 1
  have hvw : pairing (r + 1) v w = 0 := by
    simp [v, w, pairing_pos_basis_left]
  rw [highestShortInU_eq_mixedRootWord r hr, highestShortInU_eq_mixedRootWord r hr,
    mixedRootWord_conjugation r hr, borel_first_vector r g, borel_second_vector r hr g]
  exact mixedRootWord_two_weights r hr v w hvw
    ((g.val.val : Mat K (r + 1)) (Sum.inl 0) (Sum.inl 0))
    ((g.val.val : Mat K (r + 1)) (Sum.inl k) (Sum.inl k))
    ((g.val.val : Mat K (r + 1)) (Sum.inl 0) (Sum.inl k)) b hb

theorem borel_centerParameter_conjugation [CharP K 2] (r : ℕ) (hr : 0 < r)
    (g : borel K (r + 1)) (a b : K) :
    let k : Fin (r + 1) := ⟨1, by omega⟩
    g.val * (centerParameterElement r hr a b).val * g.val⁻¹ =
      (centerParameterElement r hr
        (a * ((g.val.val : Mat K (r + 1)) (Sum.inl 0) (Sum.inl 0)) ^ 2)
        (b * ((g.val.val : Mat K (r + 1)) (Sum.inl 0) (Sum.inl 0)) *
          ((g.val.val : Mat K (r + 1)) (Sum.inl k) (Sum.inl k)))).val := by
  have hb : (2 : K) * b = 0 := by rw [CharTwo.two_eq_zero, zero_mul]
  dsimp only
  change g.val * ((highestLongInU r hr a).val * (highestShortInU r hr b).val) * g.val⁻¹ = _
  calc
    _ = (g.val * (highestLongInU r hr a).val * g.val⁻¹) *
        (g.val * (highestShortInU r hr b).val * g.val⁻¹) := by group
    _ = _ := by rw [borel_highestLong_conjugation r hr, borel_highestShort_conjugation r hr g b hb]; rfl

end SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotent
