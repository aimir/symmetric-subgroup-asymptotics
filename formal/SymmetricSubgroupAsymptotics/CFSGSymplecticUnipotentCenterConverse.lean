import SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotentHighestRoot
import SymmetricSubgroupAsymptotics.CFSGSymplecticMixedRootWord

/-! The converse to the literal two-parameter centre calculation.
The highest short root is central precisely when its doubled
parameter vanishes. Thus this includes the actual two-dimensional
Sylow centre in characteristic two without importing recognition. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotent
open CFSGSymplecticSerreMatrices CFSGSymplecticTransvectionGeometry
variable {K : Type} [Field K]

theorem unipotent_second_vector (r : ℕ) (hr : 0 < r) (g : unipotent K (r + 1)) :
    let k : Fin (r + 1) := ⟨1, by omega⟩
    (g.val.val : Mat K (r + 1)) *ᵥ Pi.single (Sum.inl k) 1 =
      Pi.single (Sum.inl k) 1 +
        ((g.val.val : Mat K (r + 1)) (Sum.inl 0) (Sum.inl k)) • Pi.single (Sum.inl 0) 1 := by
  dsimp only
  let k : Fin (r + 1) := ⟨1, by omega⟩
  rw [Matrix.mulVec_single_one]
  funext x
  change (g.val.val : Mat K (r + 1)) x (Sum.inl k) =
    ((Pi.single (Sum.inl k) 1 +
      ((g.val.val : Mat K (r + 1)) (Sum.inl 0) (Sum.inl k)) • Pi.single (Sum.inl 0) 1) :
        Index (r + 1) → K) x
  cases x with
  | inl i =>
    by_cases hi0 : i = 0
    · subst i
      simp [Matrix.col_apply, Pi.single_apply, k]
    · by_cases hik : i = k
      · subst i
        have hdiag := g.property.2 (Sum.inl k)
        simpa [Matrix.col_apply, Pi.single_apply, k] using hdiag
      · have hi : k.val < i.val := by
          have hne0 : i.val ≠ 0 := fun h => hi0 (Fin.ext h)
          have hne1 : i.val ≠ 1 := fun h => hik (Fin.ext h)
          dsimp only [k]
          omega
        have hflag : flagEquiv (r + 1) (Sum.inl k) < flagEquiv (r + 1) (Sum.inl i) := hi
        have hz := g.property.1 hflag
        simpa [Matrix.col_apply, Pi.single_apply, hi0, hik, Ne.symm hi0, Ne.symm hik] using hz
  | inr i =>
    simpa [Matrix.col_apply, Pi.single_apply] using
      unipotent_lower_left_zero K (r + 1) g i k

def highestShortInU (r : ℕ) (hr : 0 < r) (b : K) : unipotent K (r + 1) :=
  let k : Fin (r + 1) := ⟨1, by omega⟩
  upperShearInU K r hr (Matrix.single 0 k b + Matrix.single k 0 b) (by
    change (Matrix.single 0 k b + Matrix.single k 0 b).transpose = _
    simp only [Matrix.transpose_add, Matrix.transpose_single, add_comm])

theorem highestShortInU_eq_mixedRootWord (r : ℕ) (hr : 0 < r) (b : K) :
    let k : Fin (r + 1) := ⟨1, by omega⟩
    (highestShortInU (K := K) r hr b).val = mixedRootWord r hr
      (Pi.single (Sum.inl (0 : Fin (r + 1))) 1) (Pi.single (Sum.inl k) 1) b := by
  dsimp only
  let k : Fin (r + 1) := ⟨1, by omega⟩
  have hvw : pairing (r + 1)
      (Pi.single (Sum.inl (0 : Fin (r + 1))) (1 : K)) (Pi.single (Sum.inl k) 1) = 0 := by
    simp [pairing_pos_basis_left, Pi.single_apply]
  apply elementary_eq_of_mulVec_eq
  intro x
  rw [mixedRootWord_apply r hr _ _ hvw]
  change ((Matrix.fromBlocks 1 (Matrix.single 0 k b + Matrix.single k 0 b) 0 1 :
    Mat K (r + 1)) *ᵥ x) = _
  funext i
  cases i <;>
    simp [Matrix.fromBlocks_mulVec, Matrix.add_mulVec, Matrix.single_mulVec,
      pairing_pos_basis_left, Pi.single_apply, Function.update_apply, Pi.smul_apply,
      smul_eq_mul, add_comm, add_left_comm]

theorem highestShortInU_mem_center (r : ℕ) (hr : 0 < r) (b : K) (hb : (2 : K) * b = 0) :
    highestShortInU (K := K) r hr b ∈ Subgroup.center (unipotent K (r + 1)) := by
  let k : Fin (r + 1) := ⟨1, by omega⟩
  let v : Index (r + 1) → K := Pi.single (Sum.inl 0) 1
  let w : Index (r + 1) → K := Pi.single (Sum.inl k) 1
  have hvw : pairing (r + 1) v w = 0 := by
    simp [v, w, pairing_pos_basis_left, Pi.single_apply]
  apply Subgroup.mem_center_iff.mpr
  intro g
  have he : g.val * (highestShortInU r hr b).val * g.val⁻¹ =
      (highestShortInU r hr b).val := by
    rw [highestShortInU_eq_mixedRootWord r hr b, mixedRootWord_conjugation r hr,
      unipotent_fixes_first_vector r g, unipotent_second_vector r hr g]
    exact mixedRootWord_add_smul r hr v w hvw b
      ((g.val.val : Mat K (r + 1)) (Sum.inl 0) (Sum.inl k)) hb
  apply Subtype.ext
  change g.val * (highestShortInU r hr b).val = (highestShortInU r hr b).val * g.val
  calc
    _ = (g.val * (highestShortInU r hr b).val * g.val⁻¹) * g.val := by
      simp only [mul_assoc, inv_mul_cancel, mul_one]
    _ = _ := by rw [he]

theorem center_two_parameter_iff (r : ℕ) (hr : 0 < r) (z : unipotent K (r + 1)) :
    z ∈ Subgroup.center (unipotent K (r + 1)) ↔
      ∃ a b : K, (2 : K) * b = 0 ∧ z = highestLongInU r hr a * highestShortInU r hr b := by
  constructor
  · intro hz
    obtain ⟨a, b, hb, hmat⟩ := central_unipotent_two_parameters r hr z hz
    refine ⟨a, b, hb, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    change (z.val.val : Mat K (r + 1)) =
      Matrix.fromBlocks 1 (Matrix.diagonal (Pi.single 0 a)) 0 1 *
        Matrix.fromBlocks 1 (Matrix.single 0 ⟨1, by omega⟩ b + Matrix.single ⟨1, by omega⟩ 0 b) 0 1
    rw [hmat, Matrix.fromBlocks_multiply, Matrix.diagonal_single]
    simp only [mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add]
    apply congrArg (fun B : Matrix (Fin (r + 1)) (Fin (r + 1)) K =>
      (Matrix.fromBlocks 1 B 0 1 : Mat K (r + 1)))
    abel
  · rintro ⟨a, b, hb, rfl⟩
    exact (Subgroup.center (unipotent K (r + 1))).mul_mem
      (highestLongInU_mem_center r hr a) (highestShortInU_mem_center r hr b hb)

end SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotent
