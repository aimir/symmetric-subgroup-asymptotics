import SymmetricSubgroupAsymptotics.CFSGProjectiveFrameImageCoordinates
import SymmetricSubgroupAsymptotics.CFSGProjectiveFrameNormalization

/-! Every original collineation sends the coordinate frame to the frame
of an actual invertible linear map. The map is constructed from its
literal image basis and the proved nonzero final coordinates. -/
set_option autoImplicit false
noncomputable section
open scoped Classical LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGProjectiveFrameAlignment
open CFSGProjectiveFrameCoordinates CFSGProjectiveFrameNormalization
variable {F n : Type*} [Field F] [Fintype n] [DecidableEq n]

theorem exists_frame_alignment (f : collineationGroup (F := F) (n := n)) (b : n) :
    ∃ a : (n → F) ≃ₗ[F] (n → F),
      (∀ i : n, a • basisPoint (F := F) i = f.val (basisPoint i)) ∧
        a • sumPoint (F := F) b = f.val (sumPoint b) := by
  obtain ⟨a, ha, hw⟩ := exists_normalized_linearEquiv
    (imageBasis f) (f.val (sumPoint b)).rep (image_final_coordinate_ne_zero f b)
  refine ⟨a, ?_, ?_⟩
  · intro i
    change a • Projectivization.mk F (Pi.single i 1) _ = f.val (basisPoint i)
    rw [Projectivization.smul_mk, ← Projectivization.mk_rep (f.val (basisPoint i))]
    apply (Projectivization.mk_eq_mk_iff F _ _ _ _).mpr
    refine ⟨Units.mk0 ((imageBasis f).repr (f.val (sumPoint b)).rep i)
      (image_final_coordinate_ne_zero f b i), ?_⟩
    change ((imageBasis f).repr (f.val (sumPoint b)).rep i) •
      (f.val (basisPoint i)).rep = a (Pi.single i 1)
    simpa only [imageBasis_apply] using (ha i).symm
  · change a • Projectivization.mk F (fun _ : n => (1 : F)) _ = f.val (sumPoint b)
    rw [Projectivization.smul_mk]
    change Projectivization.mk F (a (fun _ : n => (1 : F))) _ = f.val (sumPoint b)
    simp only [hw, Projectivization.mk_rep]

end SymmetricSubgroupAsymptotics.CFSGProjectiveFrameAlignment
