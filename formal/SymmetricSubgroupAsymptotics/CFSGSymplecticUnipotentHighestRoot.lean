import SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotentCenterParameters
import SymmetricSubgroupAsymptotics.CFSGSymplecticActualRootStabilizers

/-! The actual highest long-root group is central in C-unipotent U.
In characteristic different from two it is the entire centre. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotent
open CFSGSymplecticSerreMatrices CFSGSymplecticTransvectionGeometry
variable {K : Type} [Field K]

def highestLongInU (r : ℕ) (hr : 0 < r) (a : K) : unipotent K (r + 1) :=
  upperShearInU K r hr (Matrix.diagonal (Pi.single 0 a)) (Matrix.isSymm_diagonal _)

theorem highestLongInU_val (r : ℕ) (hr : 0 < r) (a : K) :
    (highestLongInU (K := K) r hr a).val = firstLongRoot K r a := by
  apply Subtype.ext
  apply Units.ext
  rw [firstLongRoot_coe]
  change Matrix.fromBlocks 1 (Matrix.diagonal (Pi.single 0 a)) 0 1 = _
  rw [Matrix.diagonal_single]
  ext x y
  cases x <;> cases y <;>
    simp [Matrix.fromBlocks, Matrix.transvection, Matrix.one_apply, Matrix.single_apply]

theorem unipotent_fixes_first_vector (r : ℕ) (g : unipotent K (r + 1)) :
    (g.val.val : Mat K (r + 1)) *ᵥ Pi.single (Sum.inl (0 : Fin (r + 1))) 1 =
      Pi.single (Sum.inl (0 : Fin (r + 1))) 1 := by
  rw [Matrix.mulVec_single_one]
  funext x
  cases x with
  | inl i =>
    by_cases hi : i = 0
    · subst i
      simpa only [Matrix.col_apply, Pi.single_eq_same] using g.property.2 (Sum.inl 0)
    · have hi' : flagEquiv (r + 1) (Sum.inl (0 : Fin (r + 1))) < flagEquiv (r + 1) (Sum.inl i) := by
        change 0 < i.val
        have hz : i.val ≠ 0 := by intro h; exact hi (Fin.ext h)
        omega
      have hz := g.property.1 hi'
      simpa [Matrix.col_apply, Pi.single_apply, hi, Ne.symm hi] using hz
  | inr i =>
    simpa [Matrix.col_apply, Pi.single_apply] using unipotent_lower_left_zero K (r + 1) g i 0

theorem highestLongInU_mem_center (r : ℕ) (hr : 0 < r) (a : K) :
    highestLongInU (K := K) r hr a ∈ Subgroup.center (unipotent K (r + 1)) := by
  apply Subgroup.mem_center_iff.mpr
  intro g
  let e : Index (r + 1) → K := Pi.single (Sum.inl (0 : Fin (r + 1))) 1
  have he : actualNaturalRootElement r hr e a = firstLongRoot K r a := by
    apply elementary_eq_of_mulVec_eq
    intro x
    rw [actualNaturalRootElement_apply, firstLongRoot_mulVec_eq_transvection]
  have hj := actualNaturalRootElement_conjugation r hr g.val e a
  rw [show (g.val.val : Mat K (r + 1)) *ᵥ e = e from unipotent_fixes_first_vector r g, he] at hj
  apply Subtype.ext
  change g.val * (highestLongInU r hr a).val = (highestLongInU r hr a).val * g.val
  rw [highestLongInU_val]
  calc
    _ = (g.val * firstLongRoot K r a * g.val⁻¹) * g.val := by
      simp only [mul_assoc, inv_mul_cancel, mul_one]
    _ = _ := by rw [hj]

theorem center_eq_highestLong_of_two_ne_zero (r : ℕ) (hr : 0 < r)
    (htwo : (2 : K) ≠ 0) (z : unipotent K (r + 1))
    (hz : z ∈ Subgroup.center (unipotent K (r + 1))) :
    ∃ a : K, z = highestLongInU r hr a := by
  obtain ⟨a, b, hb, hmat⟩ := central_unipotent_two_parameters r hr z hz
  have hb0 : b = 0 := (mul_eq_zero.mp hb).resolve_left htwo
  refine ⟨a, ?_⟩
  apply Subtype.ext
  rw [highestLongInU_val]
  apply Subtype.ext
  apply Units.ext
  rw [firstLongRoot_coe, hmat, hb0]
  simp only [Matrix.single_zero, add_zero]
  ext x y
  cases x <;> cases y <;>
    simp [Matrix.fromBlocks, Matrix.transvection, Matrix.one_apply, Matrix.single_apply]

end SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotent
