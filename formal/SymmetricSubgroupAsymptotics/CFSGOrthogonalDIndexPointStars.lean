import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexStarSeed
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexStarPlaneBridge
import SymmetricSubgroupAsymptotics.CFSGSingularPlaneTriangle
import SymmetricSubgroupAsymptotics.CFSGIncidenceStarAction

/-! Original quadratic singular points are recovered from the original
R11 plane relation in ranks>=5. The bridge uses the actual quadratic
shell and the exact not-both-R11 premise, so the proof includes F2.
Rank-four triality is not included in this endpoint. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPlaneFamilyAction
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexBundledQuadratic
open CFSGOrthogonalDIndexQuadraticNeighborPlane CFSGOrthogonalDIndexQuadraticCorrection
open CFSGIncidenceStarReconstruction CFSGSingularPlaneTriangle
variable (K : Type) [Field K]

abbrev SingularPoints (s : ℕ) := {U : Submodule K (Index (s + 5) → K) //
  Module.finrank K U = 1 ∧ ∀ x ∈ U, splitQuadraticForm K (s + 5) x = 0}

theorem point_span (s : ℕ) (U : SingularPoints K s)
    (u : Index (s + 5) → K) (huU : u ∈ U.val) (hu : u ≠ 0) :
    Submodule.span K {u} = U.val :=
  Submodule.eq_of_le_of_finrank_le ((Submodule.span_singleton_le_iff_mem _ _).mpr huU)
    (by rw [U.property.1, finrank_span_singleton hu])

theorem point_nonzero (s : ℕ) (U : SingularPoints K s) : ∃ u ∈ U.val, u ≠ 0 := by
  apply Submodule.exists_mem_ne_zero_of_ne_bot
  intro he
  have hz := congrArg (fun P : Submodule K (Index (s + 5) → K) => Module.finrank K P) he
  change Module.finrank K U.val = Module.finrank K (⊥ : Submodule K (Index (s + 5) → K)) at hz
  rw [U.property.1, finrank_bot] at hz
  omega

def pointStarGeometry (s : ℕ) :
    Geometry (P := SingularPoints K s) (IntersectingNonadjacent K (s + 1)) where
  incident U P := U.val ≤ P.val
  symmetric := by
    intro P Q h
    refine ⟨?_, ?_⟩
    · change Module.finrank K ↥(Q.val ⊓ P.val) = 1
      rw [inf_comm]
      exact h.1
    · change ¬∀ x ∈ Q.val ⊔ P.val, splitQuadraticForm K (s + 5) x = 0
      rw [sup_comm]
      exact h.2
  seed := by
    intro U
    obtain ⟨u, huU, hu⟩ := point_nonzero K s U
    obtain ⟨P, Q, huP, huQ, hPQ⟩ := exists_R11_seed_at_axis K s u hu (U.property.2 u huU)
    have hUP : U.val ≤ P.val := by
      rw [← point_span K s U u huU hu]
      exact (Submodule.span_singleton_le_iff_mem _ _).mpr huP
    have hUQ : U.val ≤ Q.val := by
      rw [← point_span K s U u huU hu]
      exact (Submodule.span_singleton_le_iff_mem _ _).mpr huQ
    exact ⟨P, Q, hUP, hUQ, hPQ⟩
  edgePoint := by
    intro P Q h
    exact ⟨⟨P.val ⊓ Q.val, h.1, fun x hx => P.property.2 x hx.1⟩, inf_le_left, inf_le_right⟩
  uniquePoint := by
    intro U V P Q h hUP hUQ hVP hVQ
    have hU : U.val = P.val ⊓ Q.val := Submodule.eq_of_le_of_finrank_le
      (le_inf hUP hUQ) (by rw [U.property.1, h.1])
    have hV : V.val = P.val ⊓ Q.val := Submodule.eq_of_le_of_finrank_le
      (le_inf hVP hVQ) (by rw [V.property.1, h.1])
    exact Subtype.ext (hU.trans hV.symm)
  triangle := by
    intro U P Q R hUP hUQ hPQ hPR hQR
    let A := splitQuadraticForm K (s + 5)
    have hn : ¬ZeroOn A.polarBilin P.val Q.val := by
      intro hc
      exact hPQ.2 (singular_sup A P.val Q.val P.property.2 Q.property.2 hc)
    have zP : ZeroOn A.polarBilin P.val P.val :=
      fun x hx y hy => polar_zero_of_singular A P.val P.property.2 x y hx hy
    have zQ : ZeroOn A.polarBilin Q.val Q.val :=
      fun x hx y hy => polar_zero_of_singular A Q.val Q.property.2 x y hx hy
    have zR : ZeroOn A.polarBilin R.val R.val :=
      fun x hx y hy => polar_zero_of_singular A R.val R.property.2 x y hx hy
    have hle := common_point_of_nonorthogonal A.polarBilin P.val Q.val R.val
      P.property.1 Q.property.1 hPQ.1 hPR.1 hQR.1 zP zQ zR hn
    exact (le_inf hUP hUQ).trans hle
  bridge := by
    intro U P Q T hUP hUQ hUT hPQ hnot
    obtain ⟨u, huU, hu⟩ := point_nonzero K s U
    obtain ⟨R, huR, hPR, hQR, hTR⟩ := exists_star_bridge K s u hu P Q T
      (hUP huU) (hUQ huU) (hUT huU) hPQ hnot
    refine ⟨R, ?_, hPR, hQR, hTR⟩
    rw [← point_span K s U u huU hu]
    exact (Submodule.span_singleton_le_iff_mem _ _).mpr huR

theorem plane_ext_of_point_incidence (s : ℕ) {P Q : SingularPlanes K (s + 1)}
    (h : ∀ U : SingularPoints K s, U.val ≤ P.val ↔ U.val ≤ Q.val) : P = Q := by
  have hle : ∀ A B : SingularPlanes K (s + 1),
      (∀ U : SingularPoints K s, U.val ≤ A.val → U.val ≤ B.val) → A.val ≤ B.val := by
    intro A B hab v hv
    by_cases hz : v = 0
    · exact hz ▸ B.val.zero_mem
    have hs : Submodule.span K {v} ≤ A.val := (Submodule.span_singleton_le_iff_mem _ _).mpr hv
    let U : SingularPoints K s := ⟨Submodule.span K {v}, finrank_span_singleton hz,
      fun x hx => A.property.2 x (hs hx)⟩
    exact hab U hs (Submodule.subset_span (by simp))
  exact Subtype.ext (le_antisymm (hle P Q (fun U => (h U).mp)) (hle Q P (fun U => (h U).mpr)))

theorem pointStarAction_injective (s : ℕ) :
    Function.Injective (pointAction (pointStarGeometry K s)) := by
  apply pointAction_injective
  intro P Q h
  exact plane_ext_of_point_incidence K s h

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPlaneFamilyAction
