import SymmetricSubgroupAsymptotics.CFSGProjectiveFrameFieldSurjectivity
import SymmetricSubgroupAsymptotics.CFSGProjectiveFrameAlignment

/-! Every actual finite-field collineation is the composite of an
actual linear point map and a coordinate field automorphism. This is
derived from the proved frame alignment and exact frame stabilizer. -/
set_option autoImplicit false
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGProjectiveSemilinearDecomposition
open CFSGProjectiveFrameCoordinates CFSGProjectiveFieldAction
variable {F n : Type*} [Field F] [Fintype n] [DecidableEq n] [Finite F]

def linearCollineation (a : (n → F) ≃ₗ[F] (n → F)) :
    collineationGroup (F := F) (n := n) := ⟨linearPointEquiv a, onLine_linearPointEquiv a⟩

theorem exists_decomposition (f : collineationGroup (F := F) (n := n))
    (b i j : n) (hbi : b ≠ i) (hbj : b ≠ j) (hij : i ≠ j) :
    ∃ (a : (n → F) ≃ₗ[F] (n → F)) (s : F ≃+* F),
      ∀ p, f.val p = linearPointEquiv a (pointEquiv s p) := by
  obtain ⟨a, ha, hs⟩ := CFSGProjectiveFrameAlignment.exists_frame_alignment f b
  have hpoint (p : Points (F := F) (n := n)) : a • p = linearPointEquiv a p := by
    induction p using Projectivization.ind with
    | h v hv => rfl
  simp only [hpoint] at ha hs
  let l := linearCollineation a
  have hframe : l⁻¹ * f ∈ frameStabilizer (F := F) b := by
    apply (mem_frameStabilizer_iff b _).mpr
    constructor
    · intro k
      change (linearPointEquiv a).symm (f.val (basisPoint k)) = basisPoint k
      rw [← ha k]
      exact (linearPointEquiv a).symm_apply_apply _
    · change (linearPointEquiv a).symm (f.val (sumPoint b)) = sumPoint b
      rw [← hs]
      exact (linearPointEquiv a).symm_apply_apply _
  obtain ⟨s, h⟩ := frameMap_surjective b i j hbi hbj hij ⟨l⁻¹ * f, hframe⟩
  have he : collineation s = l⁻¹ * f := congrArg Subtype.val h
  refine ⟨a, s, ?_⟩
  intro p
  have hh := congrArg (fun k : collineationGroup (F := F) (n := n) =>
    (linearPointEquiv a) (k.val p)) he
  change (linearPointEquiv a) (pointEquiv s p) =
    (linearPointEquiv a) ((linearPointEquiv a).symm (f.val p)) at hh
  simpa only [Equiv.apply_symm_apply] using hh.symm

end SymmetricSubgroupAsymptotics.CFSGProjectiveSemilinearDecomposition
