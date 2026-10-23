import SymmetricSubgroupAsymptotics.CFSGInvolutionFixedNormQuotientCoordinates
import SymmetricSubgroupAsymptotics.CFSGFFourE6FixedIndexRepresentatives

/-! The genuine fixed-space quotient by the norm image in the original
78-coordinate E6 module has dimension 26 in characteristic two. The
quotient coordinates are its two fixed Cartan and 24 fixed root indices.
No exceptional covariance, faithfulness, or original F4 correspondence
is asserted by this module. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6CharacteristicTwoFixedQuotient
open CFSGInvolutionFixedNormQuotientCoordinates CFSGInvolutionNormPairCoordinates
open CFSGFFourE6CharacteristicTwoNormImage CFSGFFourE6NormPairRepresentatives
open CFSGFFourE6CharacteristicTwoNormBasis CFSGFFourE6FixedIndexRepresentatives
open CFSGTwistedE6GeckDiagramCovariance
open CFSGNormTwoRootPairing
local instance : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _
private instance : Fintype PairIndex := by unfold PairIndex;infer_instance
private instance : Fintype FixedLabel := by unfold FixedLabel;infer_instance

def characteristicFixedSpace (K:Type) [Field K] : Submodule K (Ambient K) :=
  fixedSpace (R:=K) diagramIndex

def characteristicNormInFixed (K:Type) [Field K] :
    Submodule K (characteristicFixedSpace K) := normInFixed (R:=K) diagramIndex

theorem mem_characteristicNormInFixed (K:Type) [Field K]
    (x:characteristicFixedSpace K) :
    x∈characteristicNormInFixed K ↔ x.val∈characteristicNormImage K := Iff.rfl

abbrev characteristicFixedQuotient (K:Type) [Field K] :=
  characteristicFixedSpace K ⧸ characteristicNormInFixed K

def quotientCoordinateEquiv (K:Type) [Field K] [CharP K 2] :
    characteristicFixedQuotient K≃ₗ[K](FixedLabel→K) :=
  (fixedNormQuotientEquiv (R:=K) diagramIndex diagramIndex_involutive selectedRepresentative
    selectedRepresentative_injective selectedRepresentative_disjoint selectedRepresentative_cover).trans
      (LinearEquiv.funCongrLeft K K fixedIndexEquiv)

theorem quotientCoordinateEquiv_mk (K:Type) [Field K] [CharP K 2]
    (x:characteristicFixedSpace K) (j:FixedLabel) :
    quotientCoordinateEquiv K (Submodule.Quotient.mk x) j=x.val (fixedRepresentative j) := by
  change (fixedNormQuotientEquiv (R:=K) diagramIndex diagramIndex_involutive selectedRepresentative
    selectedRepresentative_injective selectedRepresentative_disjoint selectedRepresentative_cover
      (Submodule.Quotient.mk x)) (fixedIndexEquiv j)=x.val (fixedRepresentative j)
  rw [fixedNormQuotientEquiv_mk]
  rfl

def quotientBasis (K:Type) [Field K] [CharP K 2] :
    Module.Basis FixedLabel K (characteristicFixedQuotient K) :=
  (Pi.basisFun K FixedLabel).map (quotientCoordinateEquiv K).symm

theorem characteristicFixedQuotient_finrank (K:Type) [Field K] [CharP K 2] :
    Module.finrank K (characteristicFixedQuotient K)=26 := by
  rw [Module.finrank_eq_card_basis (quotientBasis K),←Nat.card_eq_fintype_card,fixedLabel_card]

end SymmetricSubgroupAsymptotics.CFSGFFourE6CharacteristicTwoFixedQuotient
