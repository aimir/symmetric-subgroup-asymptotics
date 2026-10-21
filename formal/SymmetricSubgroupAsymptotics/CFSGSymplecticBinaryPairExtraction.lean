import SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryArrayMembership

/-! The actual rotation/Coxeter pair recovers a pure short and a pure
long root in the same matrix-unit subgroup, uniformly from rank three. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryPairExtraction
open Matrix CFSGSymplecticSerreMatrices CFSGSymplecticBinaryRotationArrays
open CFSGSymplecticBinaryCoxeterMatrix CFSGSymplecticBinaryPairElements
open CFSGSymplecticBinaryArrayMembership
variable {K : Type} [Field K] [CharP K 2]

theorem short_twelve_mem (s : ℕ) (H : Subgroup ((Mat K (s+3))ˣ))
    (hX : (binaryFirst K s).val∈H) :
    HasArray H (shortArray (coord1 (s+3) (by omega)) (coord2 (s+3) (by omega))) := by
  have hx : HasArray H (pairArray (s+3) (by omega)) :=
    ⟨(binaryFirst K s).val,hX,binaryFirst_array K s⟩
  have hp := hasArray_pow hx 3
  rw [pair_cube] at hp
  exact hp

theorem rotation_mem (s : ℕ) (H : Subgroup ((Mat K (s+3))ˣ))
    (hX : (binaryFirst K s).val∈H) : HasArray H (rotationArray (s+3) (by omega)) := by
  have hx : HasArray H (pairArray (s+3) (by omega)) :=
    ⟨(binaryFirst K s).val,hX,binaryFirst_array K s⟩
  have hp := hasArray_pow hx 4
  rw [pair_four] at hp
  exact hp

theorem short_zero_one_mem (s : ℕ) (H : Subgroup ((Mat K (s+3))ˣ))
    (hX : (binaryFirst K s).val∈H) (hW : (binarySecond K s).val∈H) :
    HasArray H (shortArray (coord0 (s+3) (by omega)) (coord1 (s+3) (by omega))) := by
  have h01 : cyclePerm (s+2) (coord0 (s+3) (by omega))=coord1 (s+3) (by omega) := by
    simpa only [coord0,coord1,Bool.false_eq_true,if_false] using
      cyclePerm_shift (s+2) false 0 (by omega)
  have h12 : cyclePerm (s+2) (coord1 (s+3) (by omega))=coord2 (s+3) (by omega) := by
    simpa only [coord1,coord2,Bool.false_eq_true,if_false] using
      cyclePerm_shift (s+2) false 1 (by omega)
  have h0 : (cyclePerm (s+2)).symm (coord1 (s+3) (by omega))=coord0 (s+3) (by omega) := by
    rw [←h01,Equiv.symm_apply_apply]
  have h1 : (cyclePerm (s+2)).symm (coord2 (s+3) (by omega))=coord1 (s+3) (by omega) := by
    rw [←h12,Equiv.symm_apply_apply]
  have hp := hasArray_inverse_conjugate_short (s+2) H hW _ _ (short_twelve_mem s H hX)
  rw [h0,h1] at hp
  exact hp

theorem long_negative_one_mem (s : ℕ) (H : Subgroup ((Mat K (s+3))ˣ))
    (hX : (binaryFirst K s).val∈H) (hW : (binarySecond K s).val∈H) :
    HasArray H (longArray (paired (coord1 (s+3) (by omega)))) := by
  have hR := rotation_mem s H hX
  have hA := short_zero_one_mem s H hX hW
  have hR2 := hasArray_pow hR 2
  have hB := hasArray_mul (hasArray_mul hR hA) hR2
  have hC := hasArray_mul (hasArray_mul hR2 hA) hR
  have hL := hasArray_mul (hasArray_mul hC hA) hB
  rw [recover_long] at hL
  exact hL

end SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryPairExtraction
