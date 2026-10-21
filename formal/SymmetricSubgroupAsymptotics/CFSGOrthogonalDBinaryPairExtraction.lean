import SymmetricSubgroupAsymptotics.CFSGOrthogonalDBinaryArrayMembership

/-! The binary D pair recovers both first star roots, with the two
possible last-coordinate signs. The argument is uniform in rank parity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDBinaryPairExtraction
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDBinaryElements
open CFSGOrthogonalDBinaryRotationArrays CFSGOrthogonalDBinaryPairElements
open CFSGOrthogonalDBinaryArrayMembership CFSGOrthogonalDBinaryConjugation
open CFSGOrthogonalDBinaryCyclePermutation CFSGSymplecticBinaryArrayMembership
variable {K : Type} [Field K] [CharP K 2]

private theorem indices_distinct (s : ℕ) :
    firstIndex s ≠ secondIndex s ∧ penultimateIndex s ≠ lastIndex s ∧
      firstIndex s ≠ penultimateIndex s ∧ firstIndex s ≠ lastIndex s ∧
      secondIndex s ≠ penultimateIndex s ∧ secondIndex s ≠ lastIndex s := by
  have hzero : (firstIndex s).val = 0 := Fin.val_zero _
  have hone : (secondIndex s).val = 1 := rfl
  have hpen : (penultimateIndex s).val = s + 2 := rfl
  have hlast : (lastIndex s).val = s + 3 := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;>
    have hh := congrArg Fin.val h <;>
    simp only [hzero, hone, hpen, hlast] at hh <;> omega

theorem last_chain_mem (s : ℕ) (H : Subgroup ((Mat K (s + 4))ˣ))
    (hx : (binaryFirst K s).val ∈ H) :
    HasArray H (rootArray (Sum.inl (penultimateIndex s)) (Sum.inl (lastIndex s))) := by
  have hp := hasArray_pow
    (show HasArray H (pairArray (firstIndex s) (secondIndex s) (penultimateIndex s) (lastIndex s))
      from ⟨_, hx, binaryFirst_array K s⟩) 3
  obtain ⟨hab, hcd, hac, had, hbc, hbd⟩ := indices_distinct s
  rw [pair_cube _ _ _ _ hab hcd hac had hbc hbd] at hp
  exact hp

theorem rotation_mem (s : ℕ) (H : Subgroup ((Mat K (s + 4))ˣ))
    (hx : (binaryFirst K s).val ∈ H) :
    HasArray H (rotationArray (firstIndex s) (secondIndex s)) := by
  have hp := hasArray_pow
    (show HasArray H (pairArray (firstIndex s) (secondIndex s) (penultimateIndex s) (lastIndex s))
      from ⟨_, hx, binaryFirst_array K s⟩) 4
  obtain ⟨hab, hcd, hac, had, hbc, hbd⟩ := indices_distinct s
  rw [pair_four _ _ _ _ hab hcd hac had hbc hbd] at hp
  exact hp

theorem first_star_mem (s : ℕ) (H : Subgroup ((Mat K (s + 4))ˣ))
    (hx : (binaryFirst K s).val ∈ H) (hW : (binarySecond K s).val ∈ H) :
    HasArray H (rootArray (Sum.inl (lastIndex s)) (Sum.inl (firstIndex s))) := by
  have hp := hasArray_conjugate (s + 2) H hW _ _ (last_chain_mem s H hx)
  change HasArray H (rootArray
    (cyclePerm (s + 2) (Sum.inl (Fin.last (s + 2)).castSucc))
    (cyclePerm (s + 2) (Sum.inl (Fin.last (s + 3))))) at hp
  rw [cyclePerm_positive_penultimate, cyclePerm_positive_last, rootArray_paired] at hp
  exact hp

theorem second_star_mem (s : ℕ) (H : Subgroup ((Mat K (s + 4))ˣ))
    (hx : (binaryFirst K s).val ∈ H) (hW : (binarySecond K s).val ∈ H) :
    HasArray H (rootArray (Sum.inl (lastIndex s)) (Sum.inl (secondIndex s))) := by
  have hr := rotation_mem s H hx
  have ha := first_star_mem s H hx hW
  change HasArray H (shortArray (lastIndex s) (firstIndex s)) at ha
  have hp := hasArray_mul (hasArray_mul (hasArray_pow hr 2) ha) hr
  obtain ⟨hab, _, _, had, _, hbd⟩ := indices_distinct s
  rw [rotation_star _ _ _ hab had hbd] at hp
  exact hp

theorem opposite_first_star_mem (s : ℕ) (H : Subgroup ((Mat K (s + 4))ˣ))
    (hx : (binaryFirst K s).val ∈ H) (hW : (binarySecond K s).val ∈ H) :
    HasArray H (rootArray (Sum.inr (lastIndex s)) (Sum.inl (firstIndex s))) := by
  have hp := hasArray_inverse_conjugate (s + 2) H hW _ _ (second_star_mem s H hx hW)
  have hfirst : cyclePerm (s + 2) (Sum.inl (firstIndex s)) = Sum.inl (secondIndex s) := by
    simpa only [firstIndex, secondIndex, Bool.false_eq_true, if_false] using
      cyclePerm_shift (s + 2) false 0 (by omega)
  have hlast : cyclePerm (s + 2) (Sum.inr (lastIndex s)) = Sum.inl (lastIndex s) :=
    cyclePerm_negative_last (s + 2)
  rw [← hfirst, ← hlast, Equiv.symm_apply_apply, Equiv.symm_apply_apply] at hp
  exact hp

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDBinaryPairExtraction
