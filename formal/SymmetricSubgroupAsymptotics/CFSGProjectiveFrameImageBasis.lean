import SymmetricSubgroupAsymptotics.CFSGProjectiveCoordinateHyperplanes
import SymmetricSubgroupAsymptotics.CFSGProjectiveSpanRepresentatives
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-! The original images of the coordinate points of a collineation have
representatives forming an actual linear basis. This follows from the
proved projective span transport and equality of dimension and cardinality. -/
set_option autoImplicit false
noncomputable section
open scoped Classical LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGProjectiveFrameAlignment
open CFSGProjectiveFrameCoordinates CFSGProjectiveSpanRepresentatives
variable {F n : Type*} [Field F] [Fintype n] [DecidableEq n]

theorem basisPoint_span_top :
    Projectivization.Subspace.span (Set.range (basisPoint (F := F) (n := n))) = ⊤ := by
  have hlinear : Submodule.span F (Set.range (fun i : n => (Pi.single i 1 : n → F))) = ⊤ := by
    have he : (fun i : n => (Pi.single i 1 : n → F)) = (Pi.basisFun F n : n → n → F) := by
      funext i
      exact (Pi.basisFun_apply F n i).symm
    rw [he]
    exact (Pi.basisFun F n).span_eq
  have h := basisPoint_span (F := F) (Set.univ : Set n)
  simpa only [Set.image_univ, hlinear, OrderIso.map_top] using h

theorem image_basisPoint_span_top (f : collineationGroup (F := F) (n := n)) :
    Projectivization.Subspace.span (Set.range (fun i : n => f.val (basisPoint i))) = ⊤ := by
  rw [Set.range_comp', ← mapSubspace_span, basisPoint_span_top]
  exact (subspaceOrderIso f).map_top

theorem image_representatives_span_top (f : collineationGroup (F := F) (n := n)) :
    Submodule.span F (Set.range (fun i : n => (f.val (basisPoint i)).rep)) = ⊤ := by
  apply (Submodule.projectivization (K := F) (V := n → F)).injective
  rw [projectivization_span_representatives, image_basisPoint_span_top]
  exact (Submodule.projectivization (K := F) (V := n → F)).map_top.symm

def imageBasis (f : collineationGroup (F := F) (n := n)) : Module.Basis n F (n → F) :=
  basisOfTopLeSpanOfCardEqFinrank (fun i : n => (f.val (basisPoint i)).rep)
    (by rw [image_representatives_span_top])
    (Module.finrank_fintype_fun_eq_card F).symm

@[simp] theorem imageBasis_apply (f : collineationGroup (F := F) (n := n)) (i : n) :
    imageBasis f i = (f.val (basisPoint i)).rep := by
  simp only [imageBasis, coe_basisOfTopLeSpanOfCardEqFinrank]

end SymmetricSubgroupAsymptotics.CFSGProjectiveFrameAlignment
