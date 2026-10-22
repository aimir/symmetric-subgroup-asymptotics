import SymmetricSubgroupAsymptotics.CFSGPolarSemilinearPiece
import SymmetricSubgroupAsymptotics.CFSGPolarCommonPlane
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBMaximalOverlapConstancy

/-! Every original odd-B polar point/plane automorphism has ONE field
component on all maximal singular subspaces. Local representatives are
constructed by the proved projective theorem. Overlap uniqueness and
actual root-word connectivity prove global coherence, rather than
retaining it as an assumption. Whole-space linear gluing is separate. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBGlobalField
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBPositiveSubspace
open CFSGPolarSubspacePoints CFSGSingularPlaneTriangle
variable (K : Type) [Field K] [Finite K]

theorem exists_global_field (h2 : (2 : K) ≠ 0) (s : ℕ)
    (f : Points (gram K (s+3)).toBilin'≃Points (gram K (s+3)).toBilin')
    (l : Planes (gram K (s+3)).toBilin'≃Planes (gram K (s+3)).toBilin')
    (hinc : ∀P L,(f P).val≤(l L).val ↔ P.val≤L.val)
    (horth : ∀P Q,ZeroOn (gram K (s+3)).toBilin' (f P).val (f Q).val ↔
      ZeroOn (gram K (s+3)).toBilin' P.val Q.val) :
    ∃σ : K≃+*K,∀W : Subspaces (gram K (s+3)).toBilin',
      Module.finrank K W.val=s+3 → Nonempty (SemilinearPiece (gram K (s+3)).toBilin' f W σ) := by
  classical
  let B := (gram K (s+3)).toBilin'
  have hall : ∀W : Subspaces B,∃σ : K≃+*K,
      Module.finrank K W.val=s+3 → Nonempty (SemilinearPiece B f W σ) := by
    intro W
    by_cases hd : Module.finrank K W.val=s+3
    · obtain ⟨σ,hσ⟩ := exists_semilinearPiece B f l hinc horth W s hd
      exact ⟨σ,fun _=>hσ⟩
    · exact ⟨RingEquiv.refl K,fun h=>False.elim (hd h)⟩
  choose φ hφ using hall
  have hlocal : ∀W Z : Subspaces B,Module.finrank K W.val=s+3 →
      Module.finrank K Z.val=s+3 →
      s+3≤Module.finrank K (W.val⊓Z.val : Submodule K (Index (s+3)→K))+1 → φ W=φ Z := by
    intro W Z hdW hdZ hint
    have hlo : 2≤Module.finrank K (W.val⊓Z.val : Submodule K (Index (s+3)→K)) := by omega
    obtain ⟨T,hT,hTW,hTZ⟩ := exists_common_plane W.val Z.val hlo
    exact fields_eq_of_common_plane B f W Z (φ W) (φ Z)
      (Classical.choice (hφ W hdW)) (Classical.choice (hφ Z hdZ)) T hT hTW hTZ
  let P : Subspaces B := ⟨positiveSubspace K (s+3),positiveSubspace_singular K (s+3)⟩
  refine ⟨φ P,?_⟩
  intro W hdW
  have he : φ W=φ P := CFSGOrthogonalBMaximalOverlapConstancy.constant_on_maximal_spaces
    K h2 (s+3) φ hlocal W hdW
  exact he ▸ hφ W hdW

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBGlobalField
