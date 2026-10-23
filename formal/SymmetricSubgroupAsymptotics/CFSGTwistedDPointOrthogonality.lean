import SymmetricSubgroupAsymptotics.CFSGTwistedDPointAction
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Actual point/plane incidence recovers the actual fixed-field polar
relation, retaining Q-singularity in characteristic two. The faithful
original automorphism action consequently preserves this relation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDPointOrthogonality
open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDPlaneFamilyAction CFSGTwistedDPointStars
open CFSGTwistedDPointAction CFSGTwistedDR11CommonNeighbours CFSGTwistedDProjectiveUnipotent
open CFSGTwistedA2FixedField CFSGSingularPlaneTriangle CFSGIncidenceStarReconstruction
open CFSGOrthogonalDIndexQuadraticCorrection CFSGOrthogonalDIndexQuadraticNeighborPlane

local instance (n : ℕ) (q : CFSG.PrimePower) :
    Module.Finite (fixedField q) (fixedSpace n q) := Module.Finite.of_finite

def PointOrthogonal (s : ℕ) (q : CFSG.PrimePower) (U V : SingularPoints s q) : Prop :=
  ZeroOn (fixedQuadraticForm (s + 2) q).polarBilin U.val V.val

theorem pointOrthogonal_iff_same_or_plane (s : ℕ) (q : CFSG.PrimePower)
    (U V : SingularPoints s q) :
    PointOrthogonal s q U V ↔ U = V ∨
      ∃ P : SingularPlanes s q, U.val ≤ P.val ∧ V.val ≤ P.val := by
  constructor
  · intro h
    by_cases he : U = V
    · exact Or.inl he
    have hbot : (U.val ⊓ V.val : Submodule (fixedField q) (fixedSpace (s + 2) q)) = ⊥ := by
      by_contra hn
      have hlo : 1 ≤ Module.finrank (fixedField q)
        (U.val ⊓ V.val : Submodule (fixedField q) (fixedSpace (s + 2) q)) :=
        Submodule.one_le_finrank_iff.mpr hn
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

theorem pointStarAction_preserves_orthogonal (s : ℕ) (q : CFSG.PrimePower)
    (f : relationAut (IntersectingNonadjacent s q)) (U V : SingularPoints s q) :
    PointOrthogonal s q (pointAction (pointStarGeometry s q) f U)
      (pointAction (pointStarGeometry s q) f V) ↔ PointOrthogonal s q U V := by
  let g := pointAction (pointStarGeometry s q) f
  have hinc : ∀ (W : SingularPoints s q) (P : SingularPlanes s q),
      (g W).val ≤ (f.val P).val ↔ W.val ≤ P.val := pointAction_incidence (pointStarGeometry s q) f
  rw [pointOrthogonal_iff_same_or_plane, pointOrthogonal_iff_same_or_plane]
  constructor
  · rintro (he | ⟨P, hU, hV⟩)
    · exact Or.inl (g.injective he)
    · obtain ⟨Q, rfl⟩ := f.val.surjective P
      exact Or.inr ⟨Q, (hinc U Q).mp hU, (hinc V Q).mp hV⟩
  · rintro (rfl | ⟨P, hU, hV⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨f.val P, (hinc U P).mpr hU, (hinc V P).mpr hV⟩

theorem projectivePointAction_preserves_orthogonal (s : ℕ) (q : CFSG.PrimePower)
    (f : MulAut (Projective s q)) (U V : SingularPoints s q) :
    PointOrthogonal s q (projectivePointActionHom s q f U) (projectivePointActionHom s q f V) ↔
      PointOrthogonal s q U V :=
  pointStarAction_preserves_orthogonal s q (relationActionHom s q f) U V

theorem originalPointAction_preserves_orthogonal (s : ℕ) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedD (s + 4) q)]
    (f : MulAut (CFSG.Models.TwistedD (s + 4) q)) (U V : SingularPoints s q) :
    PointOrthogonal s q (originalPointActionHom s q f U) (originalPointActionHom s q f V) ↔
      PointOrthogonal s q U V :=
  projectivePointAction_preserves_orthogonal s q _ U V

end SymmetricSubgroupAsymptotics.CFSGTwistedDPointOrthogonality
