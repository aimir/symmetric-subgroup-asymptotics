import SymmetricSubgroupAsymptotics.CFSGQuadraticMaximalSingularGallery
import SymmetricSubgroupAsymptotics.CFSGQuadraticPolarSemilinearPiece

/-! Genuine semilinear representatives on all maximal singular spaces
restrict to every actual singular subspace. The extension to a maximal
space is proved by the quadratic gallery infrastructure, not provided
as a new projective-recognition premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGQuadraticMaximalPieceRestriction
open CFSGQuadraticMaximalSingularGallery CFSGOrthogonalDIndexQuadraticSubspacePoints
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def restrictPiece (Q : QuadraticForm K V) (f : Points Q ≃ Points Q)
    (W T : Subspaces Q) (hWT : W.val ≤ T.val) (sigma : K ≃+* K)
    (F : SemilinearPiece Q f T sigma) : SemilinearPiece Q f W sigma where
  map := F.map.comp (Submodule.inclusion hWT)
  injective := F.injective.comp (Submodule.inclusion_injective hWT)
  point x hx := by
    let y : T.val := ⟨x.val, hWT x.property⟩
    have hy : y ≠ 0 := by
      intro he
      have hz : (y : V) = 0 := congrArg (fun z : T.val => (z : V)) he
      apply hx
      apply Subtype.ext
      exact hz
    exact F.point y hy

theorem exists_piece_on_subspace [Module.Finite K V]
    (Q : QuadraticForm K V) (f : Points Q ≃ Points Q) (sigma : K ≃+* K)
    (hmax : ∀ M : MaximalSpaces Q,
      Nonempty (SemilinearPiece Q f ⟨M.val, M.property.1⟩ sigma))
    (W : Subspaces Q) : Nonempty (SemilinearPiece Q f W sigma) := by
  obtain ⟨M, hWM, hM⟩ := exists_maximal_ge Q W.val W.property
  let F := Classical.choice (hmax ⟨M, hM⟩)
  exact ⟨restrictPiece Q f W ⟨M, hM.1⟩ hWM sigma F⟩

end SymmetricSubgroupAsymptotics.CFSGQuadraticMaximalPieceRestriction
