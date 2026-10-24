import SymmetricSubgroupAsymptotics.BinaryQuadraticStabilizerClassComparison
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexSingularComponents

/-! The actual full quadratic isometry group is a point stabilizer in
the literal full polar-preserver group. This binds the affine-refinement
class comparison to the same isometry-group definition used by the
original split and twisted orthogonal models. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.QuadraticIsometryPolarStabilizer
open BinaryQuadraticRefinementTorsor BinaryQuadraticRefinementAction
open CFSGOrthogonalDIndexSingularComponents (isometryGroup)

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def polarPreservers (B : LinearMap.BilinForm K V) : Subgroup (V ≃ₗ[K] V) where
  carrier := {T | ∀ x y : V, B (T x) (T y) = B x y}
  one_mem' := fun _ _ => rfl
  mul_mem' {S T} hS hT x y := by
    change B (S (T x)) (S (T y)) = B x y
    rw [hS, hT]
  inv_mem' {T} hT x y := by
    change B (T.symm x) (T.symm y) = B x y
    simpa only [T.apply_symm_apply] using (hT (T.symm x) (T.symm y)).symm

def polarRepresentation (Q : QuadraticForm K V) :
    polarPreservers Q.polarBilin →* (V ≃ₗ[K] V) :=
  (polarPreservers Q.polarBilin).subtype

theorem polarRepresentation_preserves (Q : QuadraticForm K V)
    (g : polarPreservers Q.polarBilin) (x y : V) :
    Q.polarBilin (polarRepresentation Q g x) (polarRepresentation Q g y) =
      Q.polarBilin x y := g.property x y

theorem isometry_preserves_polar (Q : QuadraticForm K V) (g : isometryGroup Q) :
    g.val ∈ polarPreservers Q.polarBilin := by
  intro x y
  change Q (g.val x + g.val y) - Q (g.val x) - Q (g.val y) =
    Q (x + y) - Q x - Q y
  rw [← map_add, g.property, g.property, g.property]

def isometryStabilizerEquiv (Q : QuadraticForm K V) :
    letI := refinementAction Q (polarRepresentation Q) (polarRepresentation_preserves Q)
    isometryGroup Q ≃* MulAction.stabilizer (polarPreservers Q.polarBilin)
      (⟨Q, rfl⟩ : Refinement Q) := by
  letI := refinementAction Q (polarRepresentation Q) (polarRepresentation_preserves Q)
  refine {
    toFun := fun g => ⟨⟨g.val, isometry_preserves_polar Q g⟩, ?_⟩
    invFun := fun g => ⟨g.val.val, ?_⟩
    left_inv := fun _ => Subtype.ext rfl
    right_inv := fun _ => Subtype.ext (Subtype.ext rfl)
    map_mul' := fun _ _ => Subtype.ext (Subtype.ext rfl) }
  · exact (stabilizer_mem_iff Q (polarRepresentation Q) (polarRepresentation_preserves Q)
      ⟨Q, rfl⟩ _).mpr g.property
  · exact (stabilizer_mem_iff Q (polarRepresentation Q) (polarRepresentation_preserves Q)
      ⟨Q, rfl⟩ _).mp g.property

theorem class_card_le [Finite K] [Finite V] (hK : Nat.card K = 2)
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate) (v : V)
    (htrans : ∀ w : V, w ≠ 0 →
      ∃ g : polarPreservers Q.polarBilin, polarRepresentation Q g v = w) :
    letI := BilinearContragredientDuality.naturalAction (polarRepresentation Q)
    Nat.card (ConjClasses (isometryGroup Q)) ≤
      Nat.card (ConjClasses (polarPreservers Q.polarBilin)) +
        Nat.card (ConjClasses (MulAction.stabilizer (polarPreservers Q.polarBilin) v)) := by
  letI : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun T : V ≃ₗ[K] V => (T : V → V)) LinearEquiv.coe_injective
  letI := BilinearContragredientDuality.naturalAction (polarRepresentation Q)
  letI := refinementAction Q (polarRepresentation Q) (polarRepresentation_preserves Q)
  let S := MulAction.stabilizer (polarPreservers Q.polarBilin) (⟨Q, rfl⟩ : Refinement Q)
  letI : Finite (ConjClasses S) :=
    Finite.of_surjective ConjClasses.mk ConjClasses.mk_surjective
  have h := BinaryQuadraticStabilizerClassComparison.stabilizer_class_card_le
    hK Q hQ (polarRepresentation Q) (polarRepresentation_preserves Q) v htrans ⟨Q, rfl⟩
  have hs : Nat.card (ConjClasses (isometryGroup Q)) ≤ Nat.card (ConjClasses S) :=
    Nat.card_le_card_of_surjective
      (ConjClasses.map (isometryStabilizerEquiv Q).symm.toMonoidHom)
      (ConjClasses.map_surjective (isometryStabilizerEquiv Q).symm.surjective)
  exact hs.trans h

end SymmetricSubgroupAsymptotics.QuadraticIsometryPolarStabilizer
