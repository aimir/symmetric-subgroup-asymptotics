import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPointStars
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Original quadratic point incidence recovers the original polar
relation in every characteristic. Quadratic singularity of a sum is
proved from Q on the two summands and their cross-pairing, rather than
identified with polar self-orthogonality in characteristic two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPlaneFamilyAction
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexBundledQuadratic
open CFSGOrthogonalDIndexQuadraticCorrection CFSGOrthogonalDIndexQuadraticNeighborPlane
open CFSGSingularPlaneTriangle CFSGIncidenceStarReconstruction
variable (K : Type) [Field K]

def PointOrthogonal (s : ℕ) (U V : SingularPoints K s) : Prop :=
  ZeroOn (splitQuadraticForm K (s + 5)).polarBilin U.val V.val

theorem pointOrthogonal_iff_same_or_plane (s : ℕ) (U V : SingularPoints K s) :
    PointOrthogonal K s U V ↔ U = V ∨
      ∃ P : SingularPlanes K (s + 1), U.val ≤ P.val ∧ V.val ≤ P.val := by
  constructor
  · intro h
    by_cases he : U = V
    · exact Or.inl he
    have hbot : (U.val ⊓ V.val : Submodule K (Index (s + 5) → K)) = ⊥ := by
      by_contra hn
      have hlo : 1 ≤ Module.finrank K ↥(U.val ⊓ V.val) := Submodule.one_le_finrank_iff.mpr hn
      have hU : U.val ⊓ V.val = U.val := Submodule.eq_of_le_of_finrank_le inf_le_left
        (by rw [U.property.1]; exact hlo)
      have hV : U.val ⊓ V.val = V.val := Submodule.eq_of_le_of_finrank_le inf_le_right
        (by rw [V.property.1]; exact hlo)
      exact he (Subtype.ext (hU.symm.trans hV))
    have hd := Submodule.finrank_sup_add_finrank_inf_eq U.val V.val
    rw [hbot, finrank_bot, U.property.1, V.property.1, add_zero] at hd
    exact Or.inr ⟨⟨U.val ⊔ V.val, hd,
      singular_sup _ U.val V.val U.property.2 V.property.2 h⟩, le_sup_left, le_sup_right⟩
  · rintro (rfl | ⟨P, hU, hV⟩)
    · exact fun x hx y hy => polar_zero_of_singular _ U.val U.property.2 x y hx hy
    · exact fun x hx y hy => polar_zero_of_singular _ P.val P.property.2 x y (hU hx) (hV hy)

theorem pointStarAction_preserves_orthogonal (s : ℕ)
    (f : relationAut (IntersectingNonadjacent K (s + 1))) (U V : SingularPoints K s) :
    PointOrthogonal K s (pointAction (pointStarGeometry K s) f U)
      (pointAction (pointStarGeometry K s) f V) ↔ PointOrthogonal K s U V := by
  let g := pointAction (pointStarGeometry K s) f
  have hinc : ∀ (W : SingularPoints K s) (P : SingularPlanes K (s + 1)),
      (g W).val ≤ (f.val P).val ↔ W.val ≤ P.val :=
    pointAction_incidence (pointStarGeometry K s) f
  rw [pointOrthogonal_iff_same_or_plane, pointOrthogonal_iff_same_or_plane]
  constructor
  · rintro (he | ⟨P, hU, hV⟩)
    · exact Or.inl (g.injective he)
    · obtain ⟨Q, rfl⟩ := f.val.surjective P
      exact Or.inr ⟨Q, (hinc U Q).mp hU, (hinc V Q).mp hV⟩
  · rintro (rfl | ⟨P, hU, hV⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨f.val P, (hinc U P).mpr hU, (hinc V P).mpr hV⟩

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPlaneFamilyAction
