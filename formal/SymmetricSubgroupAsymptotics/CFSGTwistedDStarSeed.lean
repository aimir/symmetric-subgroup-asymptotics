import SymmetricSubgroupAsymptotics.CFSGTwistedDStarPlaneBridge
import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativePlaneTransport

/-! Every actual nonzero fixed-field singular axis lies in an actual
R11 seed. A literal hyperbolic pair in its smaller fixed tail supplies
the standard seed, then an actual relative word transports it. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDStarSeed
open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDFixedQuadraticAction
open CFSGTwistedDPlaneRootLine CFSGTwistedDSingularDimensionBound
open CFSGTwistedDFixedTailLinear CFSGTwistedDDoubleTailEmbedding
open CFSGTwistedDHyperbolicTripleBridge CFSGTwistedDFixedTailOrthogonality
open CFSGTwistedDPlaneFamilyAction CFSGTwistedDR11CommonNeighbours CFSGTwistedDR11Recognition
open CFSGTwistedDProjectiveUnipotent CFSGTwistedDRelativePlaneTransport CFSGTwistedA2FixedField
open CFSGOrthogonalDIndexQuadraticCorrection CFSGOrthogonalDIndexQuadraticStarPairs
open CFSGPolarCommonPointPlanes

local instance (n : ℕ) (q : CFSG.PrimePower) :
    Module.Finite (fixedField q) (fixedSpace n q) := Module.Finite.of_finite

private theorem positive_axis_norm (n : ℕ) (q : CFSG.PrimePower) :
    fixedQuadraticForm n q (firstAxis n q) = 0 := by
  apply Subtype.ext
  rw [fixedQuadraticForm_apply]
  exact CFSGSplitQuadraticBasisParameters.positive_norm (q.Extension 2) 0 1

private theorem negative_axis_norm (n : ℕ) (q : CFSG.PrimePower) :
    fixedQuadraticForm (n + 1) q (negativeAxis n q) = 0 := by
  apply Subtype.ext
  rw [fixedQuadraticForm_apply]
  exact CFSGSplitQuadraticBasisParameters.negative_norm (q.Extension 2) 0 1

private theorem axes_pairing (n : ℕ) (q : CFSG.PrimePower) :
    (fixedQuadraticForm (n + 1) q).polarBilin (firstAxis (n + 1) q) (negativeAxis n q) = 1 := by
  rw [positive_axis_polar]
  apply Subtype.ext
  change (Pi.single (Sum.inr (0 : Fin (n + 3))) (1 : q.Extension 2) :
    CFSGOrthogonalDSerreMatrices.Index (n + 3) → q.Extension 2) (Sum.inr 0) = 1
  rw [Pi.single_eq_same]

theorem standard_axis_seed (s : ℕ) (q : CFSG.PrimePower) :
    ∃ P Q : SingularPlanes s q, firstAxis (s + 2) q ∈ P.val ∧
      firstAxis (s + 2) q ∈ Q.val ∧ IntersectingNonadjacent s q P Q := by
  let A := fixedQuadraticForm (s + 2) q
  let u := firstAxis (s + 2) q
  let v := tailEmbed (s + 1) q (firstAxis (s + 1) q)
  let w := tailEmbed (s + 1) q (negativeAxis s q)
  have hu : u ≠ 0 := firstAxis_nonzero (s + 2) q
  have huQ : A u = 0 := positive_axis_norm (s + 2) q
  have hvQ : A v = 0 := (tailEmbed_quadratic (s + 1) q _).trans (positive_axis_norm (s + 1) q)
  have hwQ : A w = 0 := (tailEmbed_quadratic (s + 1) q _).trans (negative_axis_norm s q)
  have huv : A.polarBilin u v = 0 := by
    rw [positive_axis_polar]
    exact tailEmbed_negativeHead (s + 1) q _
  have huw : A.polarBilin u w = 0 := by
    rw [positive_axis_polar]
    exact tailEmbed_negativeHead (s + 1) q _
  have hvw : A.polarBilin v w = 1 := by
    rw [tailEmbed_pairing (s + 1) q v (tailEmbed_negativeHead (s + 1) q _) _, tailEmbed_tail]
    exact axes_pairing s q
  have hnv (c : fixedField q) : v ≠ c • u := by
    intro he
    have hz : A.polarBilin v w = 0 := by rw [he, map_smul, LinearMap.smul_apply, huw, smul_zero]
    exact one_ne_zero (hvw.symm.trans hz)
  have hnw (c : fixedField q) : w ≠ c • u := by
    intro he
    have hvu : A.polarBilin v u = 0 :=
      (QuadraticMap.polar_comm (A : _ → fixedField q) v u).trans huv
    have hz : A.polarBilin v w = 0 := by rw [he, map_smul, hvu, smul_zero]
    exact one_ne_zero (hvw.symm.trans hz)
  let P : SingularPlanes s q := ⟨Submodule.span (fixedField q) {u, v},
    pairPlane_finrank u v hu hnv, singular_span_pair A u v huQ hvQ huv⟩
  let Q : SingularPlanes s q := ⟨Submodule.span (fixedField q) {u, w},
    pairPlane_finrank u w hu hnw, singular_span_pair A u w huQ hwQ huw⟩
  have huP : u ∈ P.val := Submodule.subset_span (Or.inl rfl)
  have huQ' : u ∈ Q.val := Submodule.subset_span (Or.inl rfl)
  exact ⟨P, Q, huP, huQ', intersecting_nonsingular_of_pairing A P.val Q.val
    P.property.1 Q.property.1 P.property.2 Q.property.2 u v w hu huP huQ'
      (Submodule.subset_span (Or.inr rfl)) (Submodule.subset_span (Or.inr rfl))
      (hvw.trans_ne one_ne_zero)⟩

theorem exists_axis_seed (s : ℕ) (q : CFSG.PrimePower)
    (u : fixedSpace (s + 2) q) (hu : u ≠ 0) (huQ : fixedQuadraticForm (s + 2) q u = 0) :
    ∃ P Q : SingularPlanes s q, u ∈ P.val ∧ u ∈ Q.val ∧ IntersectingNonadjacent s q P Q := by
  have hraw := congrArg (fun a : fixedField q => (a : q.Extension 2)) huQ
  dsimp only at hraw
  rw [fixedQuadraticForm_apply] at hraw
  obtain ⟨g, hg⟩ := CFSGTwistedDAllRankSingularOrbit.exists_normalize_all (s + 2) q
    u.val u.property hraw (fun he => hu (Subtype.ext he))
  have hgu : fixedLinearHom (s + 2) q g u = firstAxis (s + 2) q := by
    apply Subtype.ext
    rw [fixedLinearHom_apply]
    exact hg
  have hi : fixedLinearHom (s + 2) q g⁻¹ (firstAxis (s + 2) q) = u := by
    have he := congrArg (fixedLinearHom (s + 2) q g).symm hgu
    rw [LinearEquiv.symm_apply_apply] at he
    simpa only [map_inv] using he.symm
  obtain ⟨P, Q, huP, huQ', hPQ⟩ := standard_axis_seed s q
  let f := singularActionHom s q (MulAut.conj (projection s q g⁻¹))
  refine ⟨f P, f Q, ?_, ?_, (singularAction_preserves_R11 s q _ P Q).mpr hPQ⟩
  · rw [innerPlane_action_map]
    exact ⟨firstAxis (s + 2) q, huP, hi⟩
  · rw [innerPlane_action_map]
    exact ⟨firstAxis (s + 2) q, huQ', hi⟩

end SymmetricSubgroupAsymptotics.CFSGTwistedDStarSeed
