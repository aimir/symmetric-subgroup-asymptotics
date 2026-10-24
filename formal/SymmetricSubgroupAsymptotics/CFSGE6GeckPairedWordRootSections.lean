import SymmetricSubgroupAsymptotics.CFSGE6GeckPositiveWordRootSections
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckMatrixTwist
import Mathlib.Tactic.Group

/-! A fixed literal Weyl word transports paired root sections with the
same parameter on the two simple axes. This is an actual matrix identity,
using arbitrary root-line elements rather than chosen sign conventions. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckPairedWordRootSections
open CFSGE6GeckPositiveWordRootSections CFSGTwistedE6GeckSectionRootParameters
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckMatrixTwist
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoGeckWeylWordDegree CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord
open CFSGSerreDiagram CFSGNormTwoRootPairing
local notation "A" => CartanMatrix.E₆
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local instance : DecidableEq (Roots A) := Classical.decEq _

def rawSectionValue (K : Type) [Field K] (k : Roots A) (x : RootLine K k) :
    (Matrix GeckIndex GeckIndex K)ˣ := x.val

theorem exists_paired_word_parameter (K : Type) [Field K] (w : List (Fin 6)) (i : Fin 6)
    (hw : unitTwist K (RingEquiv.refl K) (canonicalWord rawData K w) =
      canonicalWord rawData K w)
    (x : RootLine K (wordRoot A hs hp E6Base E6Index w (E6Index i))) :
    ∃ a : K, rawSectionValue K _ x * unitTwist K (RingEquiv.refl K) (rawSectionValue K _ x) =
      canonicalWord rawData K w *
        (canonicalRoot rawData K false i a * canonicalRoot rawData K false (e6Permutation i) a) *
      (canonicalWord rawData K w)⁻¹ := by
  obtain ⟨a,ha⟩ := exists_word_parameter K w i x
  have hav : canonicalWord rawData K w * canonicalRoot rawData K false i a *
      (canonicalWord rawData K w)⁻¹ = rawSectionValue K _ x := ha
  refine ⟨a,?_⟩
  rw [←hav,map_mul,map_mul,map_inv,hw,unitTwist_root,RingEquiv.refl_apply]
  group

end SymmetricSubgroupAsymptotics.CFSGE6GeckPairedWordRootSections
