import SymmetricSubgroupAsymptotics.CFSGE6GeckFixedUpperNormalizer

/-! The intrinsic upper-normalizer and Weyl-extraction statements restrict
to every actual intermediate group between the fixed-root-generated
subgroup and the fixed-action preimage. In particular they apply to J
itself, without adjoining the whole diagonal preimage. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckIntermediateOvergroup
open CFSGE6GeckOvergroupCellExtraction CFSGE6GeckFixedUpperNormalizer
open CFSGE6GeckOvergroupWeylExtraction CFSGTwistedE6WeylChamber
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckRelativeRootGenerated
open CFSGTwistedE6GeckFixedRangePreimage CFSGTwistedE6GeckNormalizerEnvelope
open CFSGTwistedE6GeckRelativeWordEnvelope CFSGTwistedE6RelativeWeylOrbits
open CFSGTwistedE6FixedWordClassification CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGNormTwoGeckWeylWordDegree
open CFSGSerreQuadraticWeylWord
local notation "A" => CartanMatrix.E₆
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite

def upperIn (K : Type) [Field K] (L : Subgroup (Matrix GeckIndex GeckIndex K)ˣ) :
    Subgroup (Matrix GeckIndex GeckIndex K)ˣ := normalizerEnvelope K ⊓ L

theorem upperIn_eq_normalizer_inter (K : Type) [Field K] [Finite K] (sigma : K≃+*K)
    (L : Subgroup (Matrix GeckIndex GeckIndex K)ˣ)
    (hLP : L≤ambientFixedRangePreimage K sigma) :
    upperIn K L=Subgroup.normalizer
      (signedFixed K sigma false : Set (Matrix GeckIndex GeckIndex K)ˣ) ⊓ L := by
  apply le_antisymm
  · intro x hx
    exact ⟨upperEnvelope_le_fixed_upper_normalizer K sigma ⟨hx.1,hLP hx.2⟩,hx.2⟩
  · intro x hx
    exact ⟨(fixed_upper_normalizer_inter_preimage_le K sigma ⟨hx.1,hLP hx.2⟩).1,hx.2⟩

theorem exists_simple_weyl_mem_of_upperIn_lt (K : Type) [Field K] [Finite K]
    (sigma : K≃+*K) (L H : Subgroup (Matrix GeckIndex GeckIndex K)ˣ)
    (hJL : fixedRootGenerated K sigma≤L) (hLP : L≤ambientFixedRangePreimage K sigma)
    (hBH : upperIn K L < H) (hHL : H≤L) :
    ∃a : Fin 4,canonicalWord rawData K (orbitWord a)∈H := by
  obtain ⟨x,hxH,hxB⟩ := SetLike.exists_of_lt hBH
  obtain ⟨r,b,v,hb,hv,he⟩ := preimage_relative_cell K sigma x (hLP (hHL hxH))
  have hU : signedFixed K sigma false≤upperIn K L :=
    le_inf (inf_le_left.trans (positive_le_envelope K))
      ((signedFixed_le_generated K sigma false).trans hJL)
  have hvH : v∈H := hBH.le (hU hv)
  have hWL : wordUnit A hs hp E6Base E6Index K (expandRelative r)∈L :=
    hJL (relativeWord_mem_generated K sigma r)
  have hbL : b∈L := by
    have hh := L.mul_mem (L.mul_mem (hHL hxH) (L.inv_mem (hJL
      (signedFixed_le_generated K sigma false hv)))) (L.inv_mem hWL)
    have hc : x*v⁻¹*(wordUnit A hs hp E6Base E6Index K (expandRelative r))⁻¹=b := by
      rw [he]
      group
    exact hc ▸ hh
  have hbH := hBH.le (show b∈upperIn K L from ⟨hb.1,hbL⟩)
  have hWH : wordUnit A hs hp E6Base E6Index K (expandRelative r)∈H := by
    have hh := H.mul_mem (H.mul_mem (H.inv_mem hbH) hxH) (H.inv_mem hvH)
    have hc : b⁻¹*x*v⁻¹=wordUnit A hs hp E6Base E6Index K (expandRelative r) := by
      rw [he]
      group
    exact hc ▸ hh
  have hne : linearAction (expandRelative r)≠1 := by
    intro hi
    apply hxB
    refine ⟨?_,hHL hxH⟩
    rw [he]
    exact (normalizerEnvelope K).mul_mem
      ((normalizerEnvelope K).mul_mem hb.1
        (diagonalNormalizer_le_envelope K (identity_word_mem_diagonalNormalizer K _ hi)))
      (positive_le_envelope K hv.1)
  exact exists_simple_weyl_mem K sigma H (hU.trans hBH.le) r hWH hne

end SymmetricSubgroupAsymptotics.CFSGE6GeckIntermediateOvergroup
