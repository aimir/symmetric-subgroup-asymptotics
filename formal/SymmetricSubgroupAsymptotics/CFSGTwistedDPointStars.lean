import SymmetricSubgroupAsymptotics.CFSGTwistedDStarSeed
import SymmetricSubgroupAsymptotics.CFSGSingularPlaneTriangle
import SymmetricSubgroupAsymptotics.CFSGIncidenceStarAction

/-! The actual fixed-field singular points are reconstructed from R11
on the SAME singular two-planes. Every local seed, triangle and bridge
condition is proved from actual quadratic geometry in all characteristics,
including original rank four. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDPointStars
open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDPlaneFamilyAction
open CFSGTwistedDR11CommonNeighbours CFSGTwistedDStarSeed CFSGTwistedDStarPlaneBridge
open CFSGTwistedA2FixedField CFSGIncidenceStarReconstruction CFSGSingularPlaneTriangle
open CFSGOrthogonalDIndexQuadraticNeighborPlane CFSGOrthogonalDIndexQuadraticCorrection

local instance (n : ℕ) (q : CFSG.PrimePower) :
    Module.Finite (fixedField q) (fixedSpace n q) := Module.Finite.of_finite

abbrev SingularPoints (s : ℕ) (q : CFSG.PrimePower) :=
  {U : Submodule (fixedField q) (fixedSpace (s + 2) q) //
    Module.finrank (fixedField q) U = 1 ∧ ∀ x ∈ U, fixedQuadraticForm (s + 2) q x = 0}

theorem point_span (s : ℕ) (q : CFSG.PrimePower) (U : SingularPoints s q)
    (u : fixedSpace (s + 2) q) (huU : u ∈ U.val) (hu : u ≠ 0) :
    Submodule.span (fixedField q) {u} = U.val :=
  Submodule.eq_of_le_of_finrank_le ((Submodule.span_singleton_le_iff_mem _ _).mpr huU)
    (by rw [U.property.1, finrank_span_singleton hu])

theorem point_nonzero (s : ℕ) (q : CFSG.PrimePower) (U : SingularPoints s q) :
    ∃ u ∈ U.val, u ≠ 0 := by
  apply Submodule.exists_mem_ne_zero_of_ne_bot
  intro he
  have hz := congrArg
    (fun P : Submodule (fixedField q) (fixedSpace (s + 2) q) => Module.finrank (fixedField q) P) he
  dsimp only at hz
  rw [U.property.1, finrank_bot] at hz
  omega

def pointStarGeometry (s : ℕ) (q : CFSG.PrimePower) :
    Geometry (P := SingularPoints s q) (IntersectingNonadjacent s q) where
  incident U P := U.val ≤ P.val
  symmetric := by
    intro P Q h
    refine ⟨?_, ?_⟩
    · change Module.finrank (fixedField q) (Q.val ⊓ P.val : Submodule (fixedField q) _) = 1
      rw [inf_comm]
      exact h.1
    · change ¬∀ x ∈ Q.val ⊔ P.val, fixedQuadraticForm (s + 2) q x = 0
      rw [sup_comm]
      exact h.2
  seed := by
    intro U
    obtain ⟨u, huU, hu⟩ := point_nonzero s q U
    obtain ⟨P, Q, huP, huQ, hPQ⟩ := exists_axis_seed s q u hu (U.property.2 u huU)
    refine ⟨P, Q, ?_, ?_, hPQ⟩
    · rw [← point_span s q U u huU hu]
      exact (Submodule.span_singleton_le_iff_mem _ _).mpr huP
    · rw [← point_span s q U u huU hu]
      exact (Submodule.span_singleton_le_iff_mem _ _).mpr huQ
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
    let A := fixedQuadraticForm (s + 2) q
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
    obtain ⟨u, huU, hu⟩ := point_nonzero s q U
    obtain ⟨R, huR, hPR, hQR, hTR⟩ := exists_star_bridge s q u hu P Q T
      (hUP huU) (hUQ huU) (hUT huU) hPQ hnot
    refine ⟨R, ?_, hPR, hQR, hTR⟩
    rw [← point_span s q U u huU hu]
    exact (Submodule.span_singleton_le_iff_mem _ _).mpr huR

theorem plane_ext_of_point_incidence (s : ℕ) (q : CFSG.PrimePower) {P Q : SingularPlanes s q}
    (h : ∀ U : SingularPoints s q, U.val ≤ P.val ↔ U.val ≤ Q.val) : P = Q := by
  have hle : ∀ A B : SingularPlanes s q,
      (∀ U : SingularPoints s q, U.val ≤ A.val → U.val ≤ B.val) → A.val ≤ B.val := by
    intro A B hab v hv
    by_cases hz : v = 0
    · exact hz ▸ B.val.zero_mem
    have hs : Submodule.span (fixedField q) {v} ≤ A.val :=
      (Submodule.span_singleton_le_iff_mem _ _).mpr hv
    let U : SingularPoints s q := ⟨Submodule.span (fixedField q) {v}, finrank_span_singleton hz,
      fun x hx => A.property.2 x (hs hx)⟩
    exact hab U hs (Submodule.subset_span (Set.mem_singleton _))
  exact Subtype.ext (le_antisymm (hle P Q (fun U => (h U).mp)) (hle Q P (fun U => (h U).mpr)))

theorem pointStarAction_injective (s : ℕ) (q : CFSG.PrimePower) :
    Function.Injective (pointAction (pointStarGeometry s q)) := by
  apply pointAction_injective
  intro P Q h
  exact plane_ext_of_point_incidence s q h

end SymmetricSubgroupAsymptotics.CFSGTwistedDPointStars
