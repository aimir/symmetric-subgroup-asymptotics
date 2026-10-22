import SymmetricSubgroupAsymptotics.CFSGOrthogonalBStarBridge
import SymmetricSubgroupAsymptotics.CFSGSingularPlaneTriangle
import SymmetricSubgroupAsymptotics.CFSGIncidenceStarAction

/-! Original singular points are recovered from the intersecting,
nonadjacent relation on original singular two-planes. Every local star
axiom is proved from the original Gram form. Preservation of this plane
relation by an arbitrary group automorphism is a separate count step. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBPlaneFamilyAction
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBUnipotent
open CFSGOrthogonalBVectorCoordinates CFSGOrthogonalBIntrinsicLongRoots
open CFSGIncidenceStarReconstruction CFSGSingularPlaneTriangle
variable {K : Type} [Field K] [Finite K]

abbrev SingularPoints (s : ℕ) := {U : Submodule K (Index (s+3) → K) //
  Module.finrank K U=1 ∧ IsTotallySingular (K:=K) s U}

theorem point_span (s : ℕ) (U : SingularPoints (K:=K) s)
    (u : Index (s+3) → K) (huU : u∈U.val) (hu : u≠0) :
    Submodule.span K {u}=U.val := by
  exact Submodule.eq_of_le_of_finrank_le
    ((Submodule.span_singleton_le_iff_mem _ _).mpr huU)
    (by rw [U.property.1,finrank_span_singleton hu])

omit [Finite K] in
theorem exists_plane_at_axis (h2 : (2 : K) ≠ 0) (s : ℕ)
    (u : Index (s+3) → K) (hu : u≠0) (zu : (gram K (s+3)).toBilin' u u=0) :
    ∃ P : SingularPlanes (K:=K) s,u∈P.val := by
  obtain ⟨g,hg⟩ := exists_normalize_singular K h2 (s+1) u hu zu
  refine ⟨⟨conjugateRootPlane s g⁻¹,conjugateRootPlane_finrank s g⁻¹,
    conjugateRootPlane_totallySingular h2 s g⁻¹⟩,?_⟩
  refine ⟨positiveVector s 0,Submodule.subset_span (by simp),?_⟩
  change (↑(g.val⁻¹) : Mat K (s+3)) *ᵥ Pi.single (pos (s+3) 0) 1=u
  rw [←hg,Matrix.mulVec_mulVec,Units.inv_mul,Matrix.one_mulVec]

private theorem point_nonzero (s : ℕ) (U : SingularPoints (K:=K) s) :
    ∃ u∈U.val,u≠0 := by
  apply Submodule.exists_mem_ne_zero_of_ne_bot
  intro he
  have hz := congrArg (fun P : Submodule K (Index (s+3) → K)=>Module.finrank K P) he
  change Module.finrank K U.val=Module.finrank K (⊥ : Submodule K (Index (s+3) → K)) at hz
  rw [U.property.1,finrank_bot] at hz
  omega

def pointStarGeometry (h2 : (2 : K) ≠ 0) (s : ℕ) :
    Geometry (P:=SingularPoints (K:=K) s) (IntersectingNonadjacent (K:=K) s) where
  incident U P := U.val≤P.val
  symmetric := by
    intro P Q h
    refine ⟨?_,?_⟩
    · change Module.finrank K (Q.val⊓P.val : Submodule K (Index (s+3) → K))=1
      rw [inf_comm]
      exact h.1
    · change ¬IsTotallySingular (K:=K) s (Q.val⊔P.val)
      rw [sup_comm]
      exact h.2
  seed := by
    intro U
    obtain ⟨u,huU,hu⟩ := point_nonzero s U
    obtain ⟨P,huP⟩ := exists_plane_at_axis h2 s u hu (U.property.2 u huU u huU)
    obtain ⟨Q,huQ,hPQ,_,_⟩ := exists_star_bridge h2 s u hu P P P huP huP huP
    have hPU : U.val≤P.val := by
      rw [←point_span s U u huU hu]
      exact (Submodule.span_singleton_le_iff_mem _ _).mpr huP
    have hQU : U.val≤Q.val := by
      rw [←point_span s U u huU hu]
      exact (Submodule.span_singleton_le_iff_mem _ _).mpr huQ
    exact ⟨P,Q,hPU,hQU,hPQ⟩
  edgePoint := by
    intro P Q h
    exact ⟨⟨P.val⊓Q.val,h.1,fun x hx y hy=>P.property.2 x hx.1 y hy.1⟩,
      inf_le_left,inf_le_right⟩
  uniquePoint := by
    intro U V P Q h hUP hUQ hVP hVQ
    have hU : U.val=P.val⊓Q.val := Submodule.eq_of_le_of_finrank_le
      (le_inf hUP hUQ) (by rw [U.property.1,h.1])
    have hV : V.val=P.val⊓Q.val := Submodule.eq_of_le_of_finrank_le
      (le_inf hVP hVQ) (by rw [V.property.1,h.1])
    exact Subtype.ext (hU.trans hV.symm)
  triangle := by
    intro U P Q R hUP hUQ hPQ hPR hQR
    have hn : ¬ZeroOn (gram K (s+3)).toBilin' P.val Q.val := by
      intro hc
      exact hPQ.2 (CFSGSingularPairSpan.zeroOn_sup (gram K (s+3)).toBilin'
        (gram_pairing_symmetric (s+3)) P.val Q.val P.property.2 Q.property.2 hc)
    have hle := common_point_of_nonorthogonal (gram K (s+3)).toBilin'
      P.val Q.val R.val P.property.1 Q.property.1 hPQ.1 hPR.1 hQR.1
      P.property.2 Q.property.2 R.property.2 hn
    exact (le_inf hUP hUQ).trans hle
  bridge := by
    intro U P Q T hUP hUQ hUT _ _
    obtain ⟨u,huU,hu⟩ := point_nonzero s U
    obtain ⟨R,huR,hPR,hQR,hTR⟩ := exists_star_bridge h2 s u hu P Q T
      (hUP huU) (hUQ huU) (hUT huU)
    refine ⟨R,?_,hPR,hQR,hTR⟩
    rw [←point_span s U u huU hu]
    exact (Submodule.span_singleton_le_iff_mem _ _).mpr huR

theorem plane_ext_of_point_incidence (s : ℕ) {P Q : SingularPlanes (K:=K) s}
    (h : ∀U : SingularPoints (K:=K) s,U.val≤P.val ↔ U.val≤Q.val) : P=Q := by
  have hle : ∀ A B : SingularPlanes (K:=K) s,
      (∀U : SingularPoints (K:=K) s,U.val≤A.val → U.val≤B.val) → A.val≤B.val := by
    intro A B hab v hv
    by_cases hz : v=0
    · exact hz ▸ B.val.zero_mem
    have hs : Submodule.span K {v}≤A.val := (Submodule.span_singleton_le_iff_mem _ _).mpr hv
    let U : SingularPoints (K:=K) s := ⟨Submodule.span K {v},finrank_span_singleton hz,
      fun x hx y hy=>A.property.2 x (hs hx) y (hs hy)⟩
    exact hab U hs (Submodule.subset_span (by simp))
  exact Subtype.ext (le_antisymm (hle P Q (fun U=>(h U).mp))
    (hle Q P (fun U=>(h U).mpr)))

theorem pointStarAction_injective (h2 : (2 : K) ≠ 0) (s : ℕ) :
    Function.Injective (pointAction (pointStarGeometry (K:=K) h2 s)) := by
  apply pointAction_injective
  intro P Q h
  exact plane_ext_of_point_incidence s h

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBPlaneFamilyAction
