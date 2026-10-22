import SymmetricSubgroupAsymptotics.CFSGOrthogonalBPointStars
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Incidence with original singular two-planes recovers orthogonality
on the original singular points. Consequently the constructed point
action preserves the original polar relation, without assuming a
semilinear realization or a polar automorphism theorem. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBPlaneFamilyAction
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBUnipotent
open CFSGOrthogonalBIntrinsicLongRoots CFSGSingularPlaneTriangle
open CFSGIncidenceStarReconstruction
variable {K : Type} [Field K] [Finite K]

def PointOrthogonal (s : ℕ) (U V : SingularPoints (K:=K) s) : Prop :=
  ZeroOn (gram K (s+3)).toBilin' U.val V.val

theorem pointOrthogonal_iff_same_or_plane (s : ℕ) (U V : SingularPoints (K:=K) s) :
    PointOrthogonal s U V ↔ U=V ∨ ∃P : SingularPlanes (K:=K) s,U.val≤P.val ∧ V.val≤P.val := by
  constructor
  · intro h
    by_cases he : U=V
    · exact Or.inl he
    have hbot : (U.val⊓V.val : Submodule K (Index (s+3) → K))=⊥ := by
      by_contra hn
      have hlo : 1≤Module.finrank K (U.val⊓V.val : Submodule K (Index (s+3) → K)) :=
        Submodule.one_le_finrank_iff.mpr hn
      have hU : U.val⊓V.val=U.val := Submodule.eq_of_le_of_finrank_le inf_le_left
        (by rw [U.property.1];exact hlo)
      have hV : U.val⊓V.val=V.val := Submodule.eq_of_le_of_finrank_le inf_le_right
        (by rw [V.property.1];exact hlo)
      exact he (Subtype.ext (hU.symm.trans hV))
    have hd := Submodule.finrank_sup_add_finrank_inf_eq U.val V.val
    rw [hbot,finrank_bot,U.property.1,V.property.1,add_zero] at hd
    refine Or.inr ⟨⟨U.val⊔V.val,hd,?_⟩,le_sup_left,le_sup_right⟩
    exact CFSGSingularPairSpan.zeroOn_sup (gram K (s+3)).toBilin'
      (gram_pairing_symmetric (s+3)) U.val V.val U.property.2 V.property.2 h
  · rintro (rfl|⟨P,hU,hV⟩)
    · exact U.property.2
    · exact fun x hx y hy=>P.property.2 x (hU hx) y (hV hy)

theorem pointStarAction_preserves_orthogonal (h2 : (2 : K) ≠ 0) (s : ℕ)
    (f : relationAut (IntersectingNonadjacent (K:=K) s))
    (U V : SingularPoints (K:=K) s) :
    PointOrthogonal s (pointAction (pointStarGeometry h2 s) f U)
      (pointAction (pointStarGeometry h2 s) f V) ↔ PointOrthogonal s U V := by
  let g := pointAction (pointStarGeometry (K:=K) h2 s) f
  have hinc : ∀ (W : SingularPoints (K:=K) s) (P : SingularPlanes (K:=K) s),
      (g W).val≤(f.val P).val ↔ W.val≤P.val :=
    pointAction_incidence (pointStarGeometry h2 s) f
  rw [pointOrthogonal_iff_same_or_plane,pointOrthogonal_iff_same_or_plane]
  constructor
  · rintro (he|⟨P,hU,hV⟩)
    · exact Or.inl (g.injective he)
    · obtain ⟨Q,rfl⟩ := f.val.surjective P
      exact Or.inr ⟨Q,(hinc U Q).mp hU,(hinc V Q).mp hV⟩
  · rintro (rfl|⟨P,hU,hV⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨f.val P,(hinc U P).mpr hU,(hinc V P).mpr hV⟩

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBPlaneFamilyAction
