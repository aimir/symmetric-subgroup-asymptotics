import SymmetricSubgroupAsymptotics.CFSGProjectiveLinearPointAction
import SymmetricSubgroupAsymptotics.CFSGOrbitCoverCardinality

/-! The actual PGL frame alignment bounds the whole collineation group
by PGL times its actual coordinate-frame stabilizer. The scalar quotient
is taken before counting, so no spurious field-unit factor is charged. -/
set_option autoImplicit false
noncomputable section
open scoped Classical LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGProjectiveFrameOrbitCount
open CFSGProjectiveFrameCoordinates CFSGProjectiveLinearPointAction
variable {F n : Type*} [Field F] [Fintype n] [DecidableEq n] [Finite F]

theorem collineation_card_le_projective_mul_frame (b : n) :
    Nat.card (collineationGroup (F := F) (n := n)) ≤
      Nat.card (Matrix.ProjGenLinGroup n F) * Nat.card (frameStabilizer (F := F) b) := by
  letI : Finite (Matrix.ProjGenLinGroup n F) := Finite.of_surjective
    (Matrix.ProjGenLinGroup.mk : Matrix.GeneralLinearGroup n F → Matrix.ProjGenLinGroup n F)
    Matrix.ProjGenLinGroup.mk_surjective
  letI : MulAction (Matrix.ProjGenLinGroup n F) (Points (F := F) (n := n)) :=
    MulAction.compHom _ projectivePointHom
  let frame : (n ⊕ Unit) → Points (F := F) (n := n) :=
    Sum.elim (basisPoint (F := F)) (fun _ => sumPoint (F := F) b)
  have hcover : ∀ f : collineationGroup (F := F) (n := n),
      ∃ a : Matrix.ProjGenLinGroup n F, f • frame = a • frame := by
    intro f
    obtain ⟨a, ha, hs⟩ := exists_projective_frame_alignment f b
    refine ⟨a, ?_⟩
    funext x
    cases x with
    | inl i => exact (ha i).symm
    | inr u => cases u; exact hs.symm
  have hstab : MulAction.stabilizer (collineationGroup (F := F) (n := n)) frame =
      frameStabilizer (F := F) b := by
    ext f
    change (f • frame = frame) ↔ f ∈ frameStabilizer (F := F) b
    rw [mem_frameStabilizer_iff]
    constructor
    · intro h
      exact ⟨fun i => congrFun h (.inl i), congrFun h (.inr ())⟩
    · rintro ⟨hB, hS⟩
      funext x
      cases x with
      | inl i => exact hB i
      | inr u => cases u; exact hS
  have h := CFSGOrbitCoverCardinality.card_le_cover_mul_stabilizer
    (G := Matrix.ProjGenLinGroup n F) (H := collineationGroup (F := F) (n := n)) frame hcover
  simpa only [hstab] using h

end SymmetricSubgroupAsymptotics.CFSGProjectiveFrameOrbitCount
