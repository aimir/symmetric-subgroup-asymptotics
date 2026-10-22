import SymmetricSubgroupAsymptotics.CFSGOrthogonalBNaturalPlaneCompatibility
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSingularSubspaceAction

/-! Inner automorphisms act on reconstructed original B points by the
literal natural matrix. Uniqueness comes from the proved original star
geometry, and compatibility on planes comes from actual root labels. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBPlaneFamilyAction
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBUnipotent
open CFSGOrthogonalBSingularVectorCount CFSGPolarSubspacePoints
variable {K : Type} [Field K] [Finite K]

def naturalSingularPoint (h2 : (2 : K) ≠ 0) (s : ℕ)
    (g : elementaryRootGroup K (s+3)) (U : SingularPoints (K:=K) s) : SingularPoints (K:=K) s :=
  ⟨U.val.map (naturalLinearEquiv K (s+3) g).toLinearMap,
    ((naturalLinearEquiv K (s+3) g).finrank_map_eq U.val).trans U.property.1,by
    rintro x ⟨x',hx,rfl⟩ y ⟨y',hy,rfl⟩
    exact (natural_pairing_invariant h2 (s+3) g x' y').trans (U.property.2 x' hx y' hy)⟩

theorem originalPointAction_inner (p : ℕ) [Fact p.Prime] [CharP K p]
    (h2 : (2 : K) ≠ 0) (s : ℕ) (g : elementaryRootGroup K (s+3))
    (U : SingularPoints (K:=K) s) :
    (originalPointAction p h2 s (MulAut.conj (naturalProjection s g))).val U=
      naturalSingularPoint h2 s g U := by
  let c := MulAut.conj (naturalProjection s g)
  obtain ⟨P,Q,hUP,hUQ,hPQ⟩ := (pointStarGeometry (K:=K) h2 s).seed U
  have hr := (singularAction_preserves_intersectingNonadjacent p h2 s
    (r11_common_neighbours_large h2 s) c P Q).mpr hPQ
  apply (pointStarGeometry (K:=K) h2 s).uniquePoint hr
    ((originalPointAction_incidence p h2 s c U P).mpr hUP)
    ((originalPointAction_incidence p h2 s c U Q).mpr hUQ)
  · change (naturalSingularPoint h2 s g U).val≤(singularActionHom p h2 s c P).val
    rw [singularAction_inner_map]
    exact Submodule.map_mono hUP
  · change (naturalSingularPoint h2 s g U).val≤(singularActionHom p h2 s c Q).val
    rw [singularAction_inner_map]
    exact Submodule.map_mono hUQ

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBPlaneFamilyAction
