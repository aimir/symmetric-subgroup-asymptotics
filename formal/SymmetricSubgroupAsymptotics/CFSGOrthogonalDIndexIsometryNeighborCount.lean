import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexResidualNeighborCount

/-! Actual Q-preserving original linear equivalences transport the
SAME common-neighbour set bijectively. Only literal submodule images
are used; no full orthogonal-group recognition is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexIsometryNeighborCount
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexBundledQuadratic
open CFSGOrthogonalDIndexResidualNeighborCount
variable (K : Type) [Field K]

private theorem image_inverse_image (r : ℕ)
    (e : (Index r → K) ≃ₗ[K] (Index r → K)) (P : Submodule K (Index r → K)) :
    (P.map e.toLinearMap).map e.symm.toLinearMap = P := by
  rw [← Submodule.map_comp]
  have h : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro x
    exact e.symm_apply_apply x
  rw [h, Submodule.map_id]

theorem inverse_preserves_quadratic (r : ℕ)
    (e : (Index r → K) ≃ₗ[K] (Index r → K))
    (he : ∀ x, splitQuadraticForm K r (e x) = splitQuadraticForm K r x)
    (x : Index r → K) : splitQuadraticForm K r (e.symm x) = splitQuadraticForm K r x := by
  simpa only [e.apply_symm_apply] using (he (e.symm x)).symm

theorem quadraticAdjacent_map (r : ℕ)
    (e : (Index r → K) ≃ₗ[K] (Index r → K))
    (he : ∀ x, splitQuadraticForm K r (e x) = splitQuadraticForm K r x)
    (P R : Submodule K (Index r → K)) (h : QuadraticAdjacent K r P R) :
    QuadraticAdjacent K r (P.map e.toLinearMap) (R.map e.toLinearMap) := by
  refine ⟨?_, ?_, ?_⟩
  · exact fun hr => h.1 ((Submodule.map_injective_of_injective e.injective) hr)
  · have hd := e.finrank_map_eq (P ⊓ R : Submodule K (Index r → K))
    rw [Submodule.map_inf e.toLinearMap e.injective] at hd
    exact hd.trans h.2.1
  · rw [← Submodule.map_sup]
    rintro x ⟨y, hy, rfl⟩
    exact (he y).trans (h.2.2 y hy)

def commonNeighborMap (r : ℕ)
    (e : (Index r → K) ≃ₗ[K] (Index r → K))
    (he : ∀ x, splitQuadraticForm K r (e x) = splitQuadraticForm K r x)
    (P Q : Submodule K (Index r → K)) :
    CommonNeighborPlanes K r P Q →
      CommonNeighborPlanes K r (P.map e.toLinearMap) (Q.map e.toLinearMap) := by
  intro R
  refine ⟨R.val.map e.toLinearMap, (e.finrank_map_eq R.val).trans R.property.1, ?_,
    quadraticAdjacent_map K r e he P R.val R.property.2.2.1,
    quadraticAdjacent_map K r e he Q R.val R.property.2.2.2⟩
  rintro x ⟨y, hy, rfl⟩
  exact (he y).trans (R.property.2.1 y hy)

theorem commonNeighborMap_bijective (r : ℕ)
    (e : (Index r → K) ≃ₗ[K] (Index r → K))
    (he : ∀ x, splitQuadraticForm K r (e x) = splitQuadraticForm K r x)
    (P Q : Submodule K (Index r → K)) :
    Function.Bijective (commonNeighborMap K r e he P Q) := by
  constructor
  · intro R S h
    apply Subtype.ext
    exact (Submodule.map_injective_of_injective e.injective) (congrArg Subtype.val h)
  · intro S
    have hi := inverse_preserves_quadratic K r e he
    have hP := quadraticAdjacent_map K r e.symm hi (P.map e.toLinearMap) S.val S.property.2.2.1
    have hQ := quadraticAdjacent_map K r e.symm hi (Q.map e.toLinearMap) S.val S.property.2.2.2
    rw [image_inverse_image K r e P] at hP
    rw [image_inverse_image K r e Q] at hQ
    let R : CommonNeighborPlanes K r P Q :=
      ⟨S.val.map e.symm.toLinearMap, (e.symm.finrank_map_eq S.val).trans S.property.1,
        (by rintro x ⟨y, hy, rfl⟩; exact (hi y).trans (S.property.2.1 y hy)), hP, hQ⟩
    refine ⟨R, ?_⟩
    apply Subtype.ext
    exact image_inverse_image K r e.symm S.val

theorem isometry_common_neighbors_card (r : ℕ)
    (e : (Index r → K) ≃ₗ[K] (Index r → K))
    (he : ∀ x, splitQuadraticForm K r (e x) = splitQuadraticForm K r x)
    (P Q : Submodule K (Index r → K)) :
    Nat.card (CommonNeighborPlanes K r (P.map e.toLinearMap) (Q.map e.toLinearMap)) =
      Nat.card (CommonNeighborPlanes K r P Q) :=
  (Nat.card_congr (Equiv.ofBijective _ (commonNeighborMap_bijective K r e he P Q))).symm

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexIsometryNeighborCount
