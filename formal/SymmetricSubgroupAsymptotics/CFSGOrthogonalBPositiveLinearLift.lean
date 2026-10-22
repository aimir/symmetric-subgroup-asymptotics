import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGeneralLinearForm
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBOpposedGraphShear

/-! An actual injective linear representative on the positive space,
with that SAME positive space as range, extends to a literal paired
GL lift in the original determinant-one isometry group. The opposite
negative space is preserved. No polar recognition hypothesis is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBPositiveLinearLift
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBPositiveSubspace
open CFSGOrthogonalBOpposedGraphShear CFSGOrthogonalBGeneralLinearLift
open CFSGOrthogonalBGeneralLinearForm CFSGOrthogonalBSpecialFormGroup
variable (K : Type) [Field K]

def coordinates (n : ℕ) : (Fin n → K) ≃ₗ[K] positiveSubspace K n :=
  LinearEquiv.ofInjective (positiveEmbedding K n) (positiveEmbedding_injective K n)

theorem coordinates_reconstruct (n : ℕ) (v : positiveSubspace K n) :
    positiveEmbedding K n ((coordinates K n).symm v) = v.val :=
  congrArg Subtype.val ((coordinates K n).apply_symm_apply v)

def positiveAutomorphism (n : ℕ) (L : positiveSubspace K n →ₗ[K] (Index n → K))
    (hL : Function.Injective L) (hRange : L.range = positiveSubspace K n) :
    positiveSubspace K n ≃ₗ[K] positiveSubspace K n :=
  LinearEquiv.ofBijective
    (L.codRestrict (positiveSubspace K n) (fun v => by
      have hv : L v ∈ L.range := ⟨v, rfl⟩
      rw [hRange] at hv
      exact hv))
    ⟨fun x y h => hL (congrArg Subtype.val h), by
      intro y
      have hy : y.val ∈ L.range := by
        rw [hRange]
        exact y.property
      obtain ⟨x, hx⟩ := hy
      exact ⟨x, Subtype.ext hx⟩⟩

def matrixOfEquiv (n : ℕ) (e : (Fin n → K) ≃ₗ[K] (Fin n → K)) :
    Matrix.GeneralLinearGroup (Fin n) K where
  val := LinearMap.toMatrix' e.toLinearMap
  inv := LinearMap.toMatrix' e.symm.toLinearMap
  val_inv := by
    rw [← LinearMap.toMatrix'_comp]
    have he : e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id := by
      apply LinearMap.ext
      intro x
      exact e.apply_symm_apply x
    rw [he, LinearMap.toMatrix'_id]
  inv_val := by
    rw [← LinearMap.toMatrix'_comp]
    have he : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by
      apply LinearMap.ext
      intro x
      exact e.symm_apply_apply x
    rw [he, LinearMap.toMatrix'_id]

theorem matrixOfEquiv_action (n : ℕ) (e : (Fin n → K) ≃ₗ[K] (Fin n → K))
    (x : Fin n → K) : (matrixOfEquiv K n e : Matrix (Fin n) (Fin n) K) *ᵥ x = e x :=
  LinearMap.toMatrix'_mulVec e.toLinearMap x

theorem paired_positive_action (n : ℕ) (A : Matrix.GeneralLinearGroup (Fin n) K)
    (x : Fin n → K) :
    (generalLinearLift K n A : Mat K n) *ᵥ positiveEmbedding K n x =
      positiveEmbedding K n ((A : Matrix (Fin n) (Fin n) K) *ᵥ x) := by
  rw [generalLinearLift_val]
  funext i
  rcases i with (i | i) | ⟨⟩ <;>
    simp [Matrix.fromBlocks_mulVec, positiveEmbedding, Function.comp_def]
  all_goals exact congrFun (Matrix.mulVec_zero _) i

theorem paired_negative_action (n : ℕ) (A : Matrix.GeneralLinearGroup (Fin n) K)
    (x : Fin n → K) :
    (generalLinearLift K n A : Mat K n) *ᵥ negativeEmbedding K n x =
      negativeEmbedding K n
        (((A⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K).transpose *ᵥ x) := by
  rw [generalLinearLift_val]
  funext i
  rcases i with (i | i) | ⟨⟩ <;>
    simp [Matrix.fromBlocks_mulVec, negativeEmbedding, Function.comp_def]
  all_goals exact congrFun (Matrix.mulVec_zero _) i

theorem negativeSubspace_preserved (n : ℕ) (A : Matrix.GeneralLinearGroup (Fin n) K) :
    (negativeSubspace K n).map (generalLinearLift K n A : Mat K n).mulVecLin =
      negativeSubspace K n := by
  have hmem (B : Matrix.GeneralLinearGroup (Fin n) K) (x : Index n → K)
      (hx : x ∈ negativeSubspace K n) :
      (generalLinearLift K n B : Mat K n) *ᵥ x ∈ negativeSubspace K n := by
    obtain ⟨y, rfl⟩ := hx
    rw [paired_negative_action]
    exact ⟨_, rfl⟩
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    exact hmem A y hy
  · intro x hx
    let u := generalLinearLift K n A
    have hi : (((u⁻¹ : (Mat K n)ˣ) : Mat K n) *ᵥ x) ∈ negativeSubspace K n := by
      change (((generalLinearLift K n A)⁻¹ : (Mat K n)ˣ) : Mat K n) *ᵥ x ∈ _
      rw [← map_inv]
      exact hmem A⁻¹ x hx
    refine ⟨(((u⁻¹ : (Mat K n)ˣ) : Mat K n) *ᵥ x), hi, ?_⟩
    change (u : Mat K n) *ᵥ (((u⁻¹ : (Mat K n)ˣ) : Mat K n) *ᵥ x) = x
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]

theorem exists_special_extension (n : ℕ)
    (L : positiveSubspace K n →ₗ[K] (Index n → K))
    (hL : Function.Injective L) (hRange : L.range = positiveSubspace K n) :
    ∃ g : specialFormUnits K n,
      (∀ v : positiveSubspace K n, (g.val : Mat K n) *ᵥ v.val = L v) ∧
      (negativeSubspace K n).map (g.val : Mat K n).mulVecLin = negativeSubspace K n := by
  let c := coordinates K n
  let e := positiveAutomorphism K n L hL hRange
  let d := c.trans (e.trans c.symm)
  let A := matrixOfEquiv K n d
  refine ⟨⟨generalLinearLift K n A, generalLinearLift_mem_special K n A⟩, ?_,
    negativeSubspace_preserved K n A⟩
  intro v
  have hd : d (c.symm v) = c.symm (e v) := by
    change c.symm (e (c (c.symm v))) = c.symm (e v)
    rw [c.apply_symm_apply]
  calc
    (generalLinearLift K n A : Mat K n) *ᵥ v.val =
        (generalLinearLift K n A : Mat K n) *ᵥ positiveEmbedding K n (c.symm v) :=
      congrArg (fun x => (generalLinearLift K n A : Mat K n) *ᵥ x)
        (coordinates_reconstruct K n v).symm
    _ = positiveEmbedding K n ((A : Matrix (Fin n) (Fin n) K) *ᵥ c.symm v) :=
      paired_positive_action K n A _
    _ = positiveEmbedding K n (d (c.symm v)) :=
      congrArg (positiveEmbedding K n) (matrixOfEquiv_action K n d _)
    _ = positiveEmbedding K n (c.symm (e v)) := congrArg (positiveEmbedding K n) hd
    _ = (e v).val := coordinates_reconstruct K n (e v)
    _ = L v := rfl

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBPositiveLinearLift
