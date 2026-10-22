import SymmetricSubgroupAsymptotics.CFSGQuadraticPolarSemilinearPiece
import SymmetricSubgroupAsymptotics.CFSGPolarCommonPlane
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDMaximalOverlapConstancy
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDFieldNormalization

/-! ONE global field component for literal split-Q singular point/plane
bijections of rank at least four. The two actual maximal-space components
are joined by original codimension-one overlaps. Characteristic two keeps
quadratic zero throughout; no orthogonal recognition or field-coherence
input is assumed. Removing the field part gives actual linear pieces. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDGlobalField
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexPositiveSpace
open CFSGOrthogonalDIndexBundledQuadratic CFSGOrthogonalDIndexQuadraticSubspacePoints
variable (K : Type) [Field K] [Finite K]

theorem exists_global_field (s : ℕ)
    (f : Points (splitQuadraticForm K (s+4))≃Points (splitQuadraticForm K (s+4)))
    (l : Planes (splitQuadraticForm K (s+4))≃Planes (splitQuadraticForm K (s+4)))
    (hinc : ∀P L,(f P).val≤(l L).val ↔ P.val≤L.val) :
    ∃σ : K≃+*K,∀W : Subspaces (splitQuadraticForm K (s+4)),
      Module.finrank K W.val=s+4 → Nonempty (SemilinearPiece (splitQuadraticForm K (s+4)) f W σ) := by
  classical
  let q := splitQuadraticForm K (s+4)
  have hall : ∀W : Subspaces q,∃σ : K≃+*K,
      Module.finrank K W.val=s+4 → Nonempty (SemilinearPiece q f W σ) := by
    intro W
    by_cases hd : Module.finrank K W.val=s+4
    · obtain ⟨σ,hσ⟩ := exists_semilinearPiece q f l hinc W (s+1) hd
      exact ⟨σ,fun _=>hσ⟩
    · exact ⟨RingEquiv.refl K,fun h=>False.elim (hd h)⟩
  choose φ hφ using hall
  have hlocal : ∀W Z : Subspaces q,Module.finrank K W.val=s+4 →
      Module.finrank K Z.val=s+4 →
      s+4≤Module.finrank K (W.val⊓Z.val : Submodule K (Index (s+4)→K))+2 → φ W=φ Z := by
    intro W Z hdW hdZ hint
    have hlo : 2≤Module.finrank K (W.val⊓Z.val : Submodule K (Index (s+4)→K)) := by omega
    obtain ⟨T,hT,hTW,hTZ⟩ := CFSGPolarSubspacePoints.exists_common_plane W.val Z.val hlo
    exact fields_eq_of_common_plane q f W Z (φ W) (φ Z)
      (Classical.choice (hφ W hdW)) (Classical.choice (hφ Z hdZ)) T hT hTW hTZ
  let P : Subspaces q :=
    ⟨positiveSpace K (s+4),fun x hx=>positiveSpace_singular K (s+4) ⟨x,hx⟩⟩
  refine ⟨φ P,?_⟩
  intro W hdW
  have he : φ W=φ P := CFSGOrthogonalDMaximalOverlapConstancy.constant_on_maximal_spaces
    K (s+4) (by omega) φ hlocal W hdW
  exact he ▸ hφ W hdW

theorem exists_linear_normalization (s : ℕ)
    (f : Points (splitQuadraticForm K (s+4))≃Points (splitQuadraticForm K (s+4)))
    (l : Planes (splitQuadraticForm K (s+4))≃Planes (splitQuadraticForm K (s+4)))
    (hinc : ∀P L,(f P).val≤(l L).val ↔ P.val≤L.val) :
    ∃σ : K≃+*K,∀W : Subspaces (splitQuadraticForm K (s+4)),
      Module.finrank K W.val=s+4 → Nonempty (SemilinearPiece (splitQuadraticForm K (s+4))
        (CFSGOrthogonalDFieldGeometry.normalizedPoints (s+4) f σ) W (RingEquiv.refl K)) := by
  obtain ⟨σ,hσ⟩ := exists_global_field K s f l hinc
  exact ⟨σ,fun W hd=>⟨CFSGOrthogonalDFieldGeometry.normalizedPiece
    (s+4) f W σ (Classical.choice (hσ W hd))⟩⟩

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDGlobalField
