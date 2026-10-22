import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4PointTypeIncidence
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticNeighborPlane
import SymmetricSubgroupAsymptotics.CFSGSingularPlaneTriangle
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! The actual index-three point action preserves the original polar
relation. Quadratic zero on a sum is checked separately, so this
argument applies to characteristic two as well. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexPlaneFamilyAction
open CFSGOrthogonalDIndexBundledQuadratic CFSGOrthogonalDIndexQuadraticCorrection
open CFSGOrthogonalDIndexQuadraticNeighborPlane CFSGSingularPlaneTriangle
variable (K : Type) [Field K]

def PointTypeOrthogonal (U V : OriginalPoints K) : Prop :=
  ZeroOn (splitQuadraticForm K 4).polarBilin U.val V.val

theorem pointTypeOrthogonal_iff_same_or_plane (U V : OriginalPoints K) :
    PointTypeOrthogonal K U V ↔ U = V ∨
      ∃ P : SingularPlanes K 0, U.val ≤ P.val ∧ V.val ≤ P.val := by
  constructor
  · intro h
    by_cases he : U = V
    · exact Or.inl he
    have hbot : (U.val ⊓ V.val : Submodule K (Index 4 → K)) = ⊥ := by
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

theorem pointTypeAction_preserves_orthogonal [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (f : naturalPointTypeStabilizer K p) (U V : OriginalPoints K) :
    PointTypeOrthogonal K (pointTypeAction K p f U) (pointTypeAction K p f V) ↔
      PointTypeOrthogonal K U V := by
  rw [pointTypeOrthogonal_iff_same_or_plane, pointTypeOrthogonal_iff_same_or_plane]
  constructor
  · rintro (he | ⟨P, hU, hV⟩)
    · exact Or.inl ((pointTypeAction K p f).injective he)
    · obtain ⟨Q, rfl⟩ := (singularActionHom K p 0 f.val).surjective P
      exact Or.inr ⟨Q, (pointTypeAction_incidence K p f U Q).mp hU,
        (pointTypeAction_incidence K p f V Q).mp hV⟩
  · rintro (rfl | ⟨P, hU, hV⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨singularActionHom K p 0 f.val P,
        (pointTypeAction_incidence K p f U P).mpr hU,
        (pointTypeAction_incidence K p f V P).mpr hV⟩

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
