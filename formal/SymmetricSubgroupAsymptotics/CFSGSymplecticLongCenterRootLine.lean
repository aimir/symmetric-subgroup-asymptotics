import SymmetricSubgroupAsymptotics.CFSGSymplecticBorelCenterAxes

/-! The first intrinsic centre axis is exactly the original natural
long-root subgroup, with its original field parameters and action. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotent
open CFSGSymplecticSerreMatrices CFSGSymplecticTransvectionGeometry
variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem highestShortInU_zero (r : ℕ) (hr : 0 < r) :
    highestShortInU (K := K) r hr 0 = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  change (Matrix.fromBlocks 1 (Matrix.single 0 (⟨1, by omega⟩ : Fin (r + 1)) (0 : K) +
    Matrix.single (⟨1, by omega⟩ : Fin (r + 1)) 0 0) 0 1 : Mat K (r + 1)) = 1
  simp only [Matrix.single_zero, add_zero, Matrix.fromBlocks_one]

theorem centerParameterElement_long_eq_actual (r : ℕ) (hr : 0 < r) (a : K) :
    (centerParameterElement r hr a 0).val = actualNaturalRootElement r hr
      (Pi.single (Sum.inl (0 : Fin (r + 1))) 1) a := by
  have he : centerParameterElement r hr a 0 = highestLongInU r hr a := by
    change highestLongInU r hr a * highestShortInU r hr 0 = _
    rw [highestShortInU_zero, mul_one]
  rw [he, highestLongInU_val]
  apply elementary_eq_of_mulVec_eq
  intro x
  rw [firstLongRoot_mulVec_eq_transvection, actualNaturalRootElement_apply]

theorem longCenterAxis_eq_actualNaturalRootLine (r : ℕ) (hr : 0 < r) :
    longCenterAxis (K := K) r hr = actualNaturalRootLine r hr
      (Pi.single (Sum.inl (0 : Fin (r + 1))) 1) := by
  ext g
  constructor
  · intro hg
    obtain ⟨a, ha⟩ := (mem_longCenterAxis_iff r hr g).mp hg
    refine ⟨Multiplicative.ofAdd a, ?_⟩
    exact (ha.trans (centerParameterElement_long_eq_actual r hr a)).symm
  · rintro ⟨a, ha⟩
    apply (mem_longCenterAxis_iff r hr g).mpr
    exact ⟨a.toAdd, ha.symm.trans (centerParameterElement_long_eq_actual r hr a.toAdd).symm⟩

end SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotent
