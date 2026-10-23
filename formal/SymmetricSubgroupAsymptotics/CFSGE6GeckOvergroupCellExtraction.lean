import SymmetricSubgroupAsymptotics.CFSGE6GeckOvergroupWeylExtraction
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckFixedRangeFactor

/-! Actual overgroups of the upper envelope inside the fixed-action
preimage contain a folded simple Weyl representative as soon as they
contain an element outside the envelope. This uses genuine fixed cell
coordinates; no torus recognition or source faithfulness is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckOvergroupCellExtraction
open CFSGE6GeckOvergroupWeylExtraction CFSGTwistedE6WeylChamber
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckSourceAction
open CFSGTwistedE6GeckMatrixTwist CFSGTwistedE6GeckPositiveTwist
open CFSGTwistedE6GeckRelativeRootGenerated CFSGTwistedE6GeckFixedRangePreimage
open CFSGTwistedE6GeckCentralTwistedBruhatCell CFSGTwistedE6GeckCentralTwistedCellFactors
open CFSGTwistedE6GeckNormalizerEnvelope CFSGTwistedE6GeckRelativeWordEnvelope
open CFSGTwistedE6GeckInversionParts CFSGTwistedE6GeckRelativeWordTwist
open CFSGTwistedE6FixedWordClassification CFSGTwistedE6RelativeWeylOrbits
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckIntegralWord
open CFSGSerreQuadraticWeylWord
local notation "A" => CartanMatrix.E₆
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite

def upperEnvelope (K : Type) [Field K] (sigma : K≃+*K) :
    Subgroup (Matrix GeckIndex GeckIndex K)ˣ :=
  normalizerEnvelope K ⊓ ambientFixedRangePreimage K sigma

theorem fixed_positive_le_upperEnvelope (K : Type) [Field K] (sigma : K≃+*K) :
    signedFixed K sigma false ≤ upperEnvelope K sigma := by
  intro u hu
  exact ⟨positive_le_envelope K hu.1,
    fixedRootGenerated_le_preimage K sigma (signedFixed_le_generated K sigma false hu)⟩

theorem preimage_relative_cell (K : Type) [Field K] [Finite K] (sigma : K≃+*K)
    (x : (Matrix GeckIndex GeckIndex K)ˣ) (hx : x∈ambientFixedRangePreimage K sigma) :
    ∃ (r : List (Fin 4)) (b v : (Matrix GeckIndex GeckIndex K)ˣ),
      b∈upperEnvelope K sigma ∧ v∈signedFixed K sigma false ∧
        x=b*wordUnit A hs hp E6Base E6Index K (expandRelative r)*v := by
  obtain ⟨g,hg,rfl⟩ := hx
  obtain ⟨z,hz,htwist⟩ := preimage_central_twist K sigma g hg
  obtain ⟨r,b,hb,v,he⟩ := exists_central_twisted_relative_cell K sigma
    g.val g.property z hz htwist
  let W := wordUnit A hs hp E6Base E6Index K (expandRelative r)
  let v0 := inversionEmbedding K (expandRelative r) v
  have hW : unitTwist K sigma W=W := by
    dsimp only [W]
    simpa only [word_eq_canonicalWord] using relative_word_fixed K sigma r
  have hcell : unitTwist K sigma (b*W*v0)=z.val*(b*W*v0) := by
    calc
      _=unitTwist K sigma g.val := congrArg (unitTwist K sigma) he.symm
      _=z.val*g.val := htwist
      _=_ := congrArg (fun y=>z.val*y) he
  have hc := central_twisted_cell_coordinates K sigma (expandRelative r) hW z hz ⟨b,hb⟩ v hcell
  have hv : v0∈signedFixed K sigma false := ⟨v.val.property,hc.2⟩
  have hWP : W∈ambientFixedRangePreimage K sigma :=
    fixedRootGenerated_le_preimage K sigma (relativeWord_mem_generated K sigma r)
  have hvP : v0∈ambientFixedRangePreimage K sigma :=
    fixedRootGenerated_le_preimage K sigma (signedFixed_le_generated K sigma false hv)
  have hbP : b∈ambientFixedRangePreimage K sigma := by
    have hh := (ambientFixedRangePreimage K sigma).mul_mem
      ((ambientFixedRangePreimage K sigma).mul_mem (show g.val∈ambientFixedRangePreimage K sigma from ⟨g,hg,rfl⟩)
        ((ambientFixedRangePreimage K sigma).inv_mem hvP))
      ((ambientFixedRangePreimage K sigma).inv_mem hWP)
    have hcancel : g.val*v0⁻¹*W⁻¹=b := by
      change g.val=b*W*v0 at he
      rw [he]
      group
    exact hcancel ▸ hh
  exact ⟨r,b,v0,⟨hb,hbP⟩,hv,he⟩

theorem exists_simple_weyl_mem_of_not_envelope (K : Type) [Field K] [Finite K]
    (sigma : K≃+*K) (H : Subgroup (Matrix GeckIndex GeckIndex K)ˣ)
    (hB : upperEnvelope K sigma≤H)
    (x : (Matrix GeckIndex GeckIndex K)ˣ) (hxH : x∈H)
    (hxP : x∈ambientFixedRangePreimage K sigma) (hxB : x∉normalizerEnvelope K) :
    ∃a : Fin 4,canonicalWord rawData K (orbitWord a)∈H := by
  obtain ⟨r,b,v,hb,hv,he⟩ := preimage_relative_cell K sigma x hxP
  have hvB := fixed_positive_le_upperEnvelope K sigma hv
  have hWH : wordUnit A hs hp E6Base E6Index K (expandRelative r)∈H := by
    have hh := H.mul_mem (H.mul_mem (H.inv_mem (hB hb)) hxH) (H.inv_mem (hB hvB))
    have hcancel : b⁻¹*x*v⁻¹=wordUnit A hs hp E6Base E6Index K (expandRelative r) := by
      rw [he]
      group
    exact hcancel ▸ hh
  have hne : linearAction (expandRelative r)≠1 := by
    intro hi
    apply hxB
    rw [he]
    exact (normalizerEnvelope K).mul_mem
      ((normalizerEnvelope K).mul_mem hb.1
        (diagonalNormalizer_le_envelope K (identity_word_mem_diagonalNormalizer K _ hi))) hvB.1
  exact exists_simple_weyl_mem K sigma H
    ((fixed_positive_le_upperEnvelope K sigma).trans hB) r hWH hne

end SymmetricSubgroupAsymptotics.CFSGE6GeckOvergroupCellExtraction
