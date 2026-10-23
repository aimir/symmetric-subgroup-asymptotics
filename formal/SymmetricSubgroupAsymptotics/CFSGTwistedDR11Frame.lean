import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedPairRootRealization
import SymmetricSubgroupAsymptotics.CFSGTwistedDResidualNeighbourData
import SymmetricSubgroupAsymptotics.CFSGQuadraticNonorthogonalCompanions

/-! Actual relative words normalize every original fixed-field R11
pair to the e0,e1/w chart. The transverse coefficient is derived from
nonsingularity of the SAME original sum, rather than assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDR11Frame
open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDFixedQuadraticAction
open CFSGTwistedDRelativeElementaryGroup CFSGTwistedDHighestPairOperator
open CFSGTwistedDFixedPairRootRealization CFSGTwistedDSingularPlaneOrbit
open CFSGTwistedDPlaneRootLine CFSGTwistedDResidualNeighbourData CFSGTwistedA2FixedField
open CFSGOrthogonalDIndexQuadraticNeighborPlane

local instance (n : ℕ) (q : CFSG.PrimePower) :
    Module.Finite (fixedField q) (fixedSpace n q) := Module.Finite.of_finite

theorem exists_normalized_frame (s : ℕ) (q : CFSG.PrimePower)
    (P Q : Submodule (fixedField q) (fixedSpace (s + 2) q))
    (hP : Module.finrank (fixedField q) P = 2) (hQ : Module.finrank (fixedField q) Q = 2)
    (hPs : ∀ x ∈ P, fixedQuadraticForm (s + 2) q x = 0)
    (hQs : ∀ x ∈ Q, fixedQuadraticForm (s + 2) q x = 0)
    (hmeet : P ⊓ Q ≠ ⊥)
    (hnonsingular : ¬∀ x ∈ P ⊔ Q, fixedQuadraticForm (s + 2) q x = 0) :
    ∃ g : relativeRootGroup (s + 2) q, ∃ w : fixedSpace (s + 2) q,
      P.map (fixedLinearHom (s + 2) q g).toLinearMap = standardRootPlane s q ∧
      Q.map (fixedLinearHom (s + 2) q g).toLinearMap = rightPlane s q w ∧
      fixedQuadraticForm (s + 2) q w = 0 ∧
      (fixedQuadraticForm (s + 2) q).polarBilin w (firstVector s q) = 0 ∧
      (fixedQuadraticForm (s + 2) q).polarBilin w (secondVector s q) ≠ 0 := by
  obtain ⟨u, huP, huQ, hu, v, hvP, w, hwQ, hnv, _, hspanP, hspanQ, hvw⟩ :=
    CFSGQuadraticNonorthogonalCompanions.exists_companions
      (fixedQuadraticForm (s + 2) q) P Q hP hQ hPs hQs hmeet hnonsingular
  obtain ⟨g, hgu, hgv⟩ := exists_fixed_pair_frame s q u v hu
    (hPs u huP) (hPs v hvP)
    (polar_zero_of_singular _ P hPs u v huP hvP) hnv
  let w0 := fixedLinearHom (s + 2) q g w
  have hw0 : (fixedQuadraticForm (s + 2) q).polarBilin w0 (firstVector s q) = 0 := by
    rw [← hgu]
    exact (fixedLinearHom_preserves_polar (s + 2) q g w u).trans
      (polar_zero_of_singular _ Q hQs w u hwQ huQ)
  have hw1 : (fixedQuadraticForm (s + 2) q).polarBilin w0 (secondVector s q) ≠ 0 := by
    rw [← hgv]
    have he := fixedLinearHom_preserves_polar (s + 2) q g w v
    intro hz
    exact hvw ((QuadraticMap.polar_comm
      (fixedQuadraticForm (s + 2) q : _ → fixedField q) v w).trans (he.symm.trans hz))
  refine ⟨g, w0, ?_, ?_, ?_, hw0, hw1⟩
  · rw [← hspanP, Submodule.map_span, Set.image_pair]
    change Submodule.span (fixedField q)
      {fixedLinearHom (s + 2) q g u, fixedLinearHom (s + 2) q g v} = _
    rw [hgu, hgv]
    rfl
  · rw [← hspanQ, Submodule.map_span, Set.image_pair]
    change Submodule.span (fixedField q)
      {fixedLinearHom (s + 2) q g u, fixedLinearHom (s + 2) q g w} = _
    rw [hgu]
    rfl
  · exact (fixedLinearHom_preserves_Q (s + 2) q g w).trans (hQs w hwQ)

end SymmetricSubgroupAsymptotics.CFSGTwistedDR11Frame
