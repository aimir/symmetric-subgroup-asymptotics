import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSingularPairOrbit
import SymmetricSubgroupAsymptotics.CFSGTwoDimensionalSubmoduleBasis
import Mathlib.LinearAlgebra.Span.Basic

/-! Every actual totally singular two-dimensional B submodule is the
plane of an actual original conjugate long-root subgroup. The proof
uses original elementary words and keeps the original submodule. It
asserts no reconstruction of projective points from polar lines. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotent
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBVectorCoordinates
variable {K : Type} [Field K]

theorem exists_conjugateRootPlane_of_totallySingular (h2 : (2 : K) ≠ 0) (s : ℕ)
    (P : Submodule K (Index (s + 3) → K)) (hdim : Module.finrank K P = 2)
    (hs : IsTotallySingular (K := K) s P) :
    ∃ g : elementaryRootGroup K (s + 3), P = conjugateRootPlane (K := K) s g := by
  obtain ⟨v, hv, w, hw, hv0, hnot, hspan⟩ :=
    CFSGTwoDimensionalSubmoduleBasis.exists_pair P hdim
  obtain ⟨a, c, hav, haw⟩ := exists_singular_pair_frame K h2 s v w hv0
    (hs v hv v hv) (hs w hw w hw) (hs v hv w hw) hnot
  have hmap : P.map (Matrix.mulVecLin (a.val : Mat K (s + 3))) =
      standardRootPlane (K := K) s := by
    rw [← hspan, Submodule.map_span, Set.image_pair]
    change Submodule.span K {(a.val : Mat K (s + 3)) *ᵥ v,
      (a.val : Mat K (s + 3)) *ᵥ w} = standardRootPlane (K := K) s
    rw [hav, haw]
    exact CFSGTwoDimensionalSubmoduleBasis.span_pair_shear
      (positiveVector (K := K) s 0) (positiveVector (K := K) s (secondIndex s)) c
  refine ⟨a⁻¹, ?_⟩
  change P = (standardRootPlane (K := K) s).map
    (Matrix.mulVecLin (↑(a.val⁻¹) : Mat K (s + 3)))
  rw [← hmap, ← Submodule.map_comp, ← Matrix.mulVecLin_mul,
    Units.inv_mul, Matrix.mulVecLin_one, Submodule.map_id]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotent
