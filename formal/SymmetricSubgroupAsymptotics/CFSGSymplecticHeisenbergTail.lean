import SymmetricSubgroupAsymptotics.CFSGSymplecticHeisenbergEmbedding
import SymmetricSubgroupAsymptotics.CFSGTypeASLTwoWeyl
import Mathlib.Tactic.FieldSimp

/-! Literal tail SL2 matrices in the original elementary C2 group.
Their actual conjugation normalizes the embedded Heisenberg group in
odd characteristic. The quotient coordinates transform by inverse
transpose, and the raw long-root entry is unchanged. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticHeisenbergTail

open CFSGHeisenbergCoordinateGroup CFSGSymplecticSerreMatrices
open CFSGSymplecticStabilizerCoordinates CFSGSymplecticHeisenbergEmbedding
open CFSGTypeASLTwoWeyl
variable (K : Type) [Field K]

def tailMatrix (A : SL2 (F := K)) : Mat K 2 :=
  Matrix.fromBlocks !![1, 0; 0, A.val 0 0] !![0, 0; 0, A.val 0 1]
    !![0, 0; 0, A.val 1 0] !![1, 0; 0, A.val 1 1]

theorem tailMatrix_one : tailMatrix K 1 = 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [tailMatrix, Matrix.one_apply]

theorem tailMatrix_mul (A B : SL2 (F := K)) :
    tailMatrix K (A * B) = tailMatrix K A * tailMatrix K B := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [tailMatrix, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fintype.sum_sum_type, Fin.sum_univ_two]

def tailMatrixHom : SL2 (F := K) →* Mat K 2 where
  toFun := tailMatrix K
  map_one' := tailMatrix_one K
  map_mul' := tailMatrix_mul K

theorem tailMatrix_preserves_pairing (A : SL2 (F := K)) :
    PreservesPairing 2 (tailMatrix K A) := by
  intro v w
  have hd : A.val 0 0 * A.val 1 1 - A.val 0 1 * A.val 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using A.property
  calc
    CFSGSymplecticTransvectionGeometry.pairing 2 (tailMatrix K A *ᵥ v) (tailMatrix K A *ᵥ w) =
        (v (Sum.inl 0) * w (Sum.inr 0) - v (Sum.inr 0) * w (Sum.inl 0)) +
          (A.val 0 0 * A.val 1 1 - A.val 0 1 * A.val 1 0) *
            (v (Sum.inl 1) * w (Sum.inr 1) - v (Sum.inr 1) * w (Sum.inl 1)) := by
      simp [CFSGSymplecticTransvectionGeometry.pairing, tailMatrix, Matrix.mulVec,
        dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two]
      ring
    _ = CFSGSymplecticTransvectionGeometry.pairing 2 v w := by
      rw [hd]
      simp only [one_mul, CFSGSymplecticTransvectionGeometry.pairing, Fin.sum_univ_two]

def tailHom : SL2 (F := K) →* elementaryRootGroup K 2 where
  toFun A := ⟨(tailMatrixHom K).toHomUnits A,
    all_formPreserving_elementary K 2 _ (tailMatrix_preserves_pairing K A)⟩
  map_one' := Subtype.ext ((tailMatrixHom K).toHomUnits.map_one)
  map_mul' A B := Subtype.ext ((tailMatrixHom K).toHomUnits.map_mul A B)

theorem tailHom_val (A : SL2 (F := K)) :
    ((tailHom K A).val : Mat K 2) = tailMatrix K A := rfl

def transform (A : SL2 (F := K)) (g : Element K 1) : Element K 1 :=
  let x := A.val 1 1 * g.a 0 - A.val 1 0 * g.b 0
  let y := A.val 0 0 * g.b 0 - A.val 0 1 * g.a 0
  ⟨fun _ => x, fun _ => y, g.c + (x * y - g.a 0 * g.b 0) / 2⟩

theorem tailMatrix_intertwine (hTwo : (2 : K) ≠ 0)
    (A : SL2 (F := K)) (g : Element K 1) :
    tailMatrix K A * matrix K (g.a 0) (g.b 0) g.c =
      matrix K ((transform K A g).a 0) ((transform K A g).b 0) (transform K A g).c *
        tailMatrix K A := by
  let x := A.val 1 1 * g.a 0 - A.val 1 0 * g.b 0
  let y := A.val 0 0 * g.b 0 - A.val 0 1 * g.a 0
  have hd : A.val 0 0 * A.val 1 1 - A.val 0 1 * A.val 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using A.property
  have hx : x * A.val 0 0 + y * A.val 1 0 = g.a 0 := by
    calc
      _ = (A.val 0 0 * A.val 1 1 - A.val 0 1 * A.val 1 0) * g.a 0 := by dsimp [x, y]; ring
      _ = g.a 0 := by rw [hd, one_mul]
  have hy : x * A.val 0 1 + y * A.val 1 1 = g.b 0 := by
    calc
      _ = (A.val 0 0 * A.val 1 1 - A.val 0 1 * A.val 1 0) * g.b 0 := by dsimp [x, y]; ring
      _ = g.b 0 := by rw [hd, one_mul]
  have hc : x * y - 2 * (g.c + (x * y - g.a 0 * g.b 0) / 2) =
      g.a 0 * g.b 0 - 2 * g.c := by
    field_simp [hTwo]
    ring
  change tailMatrix K A * matrix K (g.a 0) (g.b 0) g.c =
    matrix K x y (g.c + (x * y - g.a 0 * g.b 0) / 2) * tailMatrix K A
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [tailMatrix, matrix, Matrix.mul_apply, Fintype.sum_sum_type,
      Fin.sum_univ_two, hx, hy, hc] <;> dsimp [x, y] <;> ring

theorem tailHom_conjugation (hTwo : (2 : K) ≠ 0)
    (A : SL2 (F := K)) (g : Element K 1) :
    tailHom K A * elementaryHom K g * (tailHom K A)⁻¹ =
      elementaryHom K (transform K A g) := by
  apply (mul_inv_eq_iff_eq_mul).mpr
  apply Subtype.ext
  apply Units.ext
  exact tailMatrix_intertwine K hTwo A g

theorem tailHom_range_normalizes (hTwo : (2 : K) ≠ 0) :
    (tailHom K).range ≤ Subgroup.normalizer
      ((elementaryHom K).range : Set (elementaryRootGroup K 2)) := by
  have hforward (A : SL2 (F := K)) (g : elementaryRootGroup K 2)
      (hg : g ∈ (elementaryHom K).range) :
      tailHom K A * g * (tailHom K A)⁻¹ ∈ (elementaryHom K).range := by
    obtain ⟨h, rfl⟩ := hg
    exact ⟨transform K A h, (tailHom_conjugation K hTwo A h).symm⟩
  rintro t ⟨A, rfl⟩
  apply Subgroup.mem_normalizer_iff.mpr
  intro g
  constructor
  · exact hforward A g
  · intro hg
    have hh := hforward A⁻¹ _ hg
    simpa only [map_inv, inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hh

end SymmetricSubgroupAsymptotics.CFSGSymplecticHeisenbergTail
