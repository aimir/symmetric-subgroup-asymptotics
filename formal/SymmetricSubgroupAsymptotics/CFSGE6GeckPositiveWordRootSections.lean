import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckSectionRootParameters
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootWeylAction
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateCanonicalSimpleRootLine

/-! Arbitrary elements of a literal positive-simple Weyl-word root line
have parameters in that SAME word chart. Root-line equality absorbs the
integral selected-root sign, so no sign-one convention is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckPositiveWordRootSections
open CFSGTwistedE6GeckSectionRootParameters CFSGTwistedE6GeckDiagramCovariance
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoRootPairing CFSGNormTwoCoordinateRootSubgroup
open CFSGNormTwoCoordinateRootWeylAction CFSGNormTwoCoordinateCanonicalSimpleRootLine
open CFSGNormTwoGeckWeylWordDegree CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos
local instance : DecidableEq (Roots A) := Classical.decEq _

theorem exists_word_parameter (K : Type) [Field K] (w : List (Fin 6)) (i : Fin 6)
    (x : RootLine K (wordRoot A hs hp E6Base E6Index w (E6Index i))) :
    ∃ a : K, canonicalWord rawData K w * canonicalRoot rawData K false i a *
      (canonicalWord rawData K w)⁻¹ = x.val := by
  have hline : (canonicalRootSubgroup rawData K false i).map
      (MulAut.conj (canonicalWord rawData K w)).toMonoidHom =
      RootLine K (wordRoot A hs hp E6Base E6Index w (E6Index i)) := by
    have hsimp : RootLine K (E6Index i) = canonicalRootSubgroup rawData K false i :=
      rootSubgroup_simple_eq_canonical A hd hs hp ho K i
    calc
      _ = (RootLine K (E6Index i)).map
          (MulAut.conj (canonicalWord rawData K w)).toMonoidHom :=
        congrArg (fun S : Subgroup ((Matrix GeckIndex GeckIndex K)ˣ) =>
          S.map (MulAut.conj (canonicalWord rawData K w)).toMonoidHom) hsimp.symm
      _ = _ := rootSubgroup_map_word A hd hs hp ho K w (E6Index i)
  have hx : x.val ∈ (canonicalRootSubgroup rawData K false i).map
      (MulAut.conj (canonicalWord rawData K w)).toMonoidHom := hline.symm ▸ x.property
  obtain ⟨y,hy,he⟩ := hx
  obtain ⟨a,rfl⟩ := hy
  exact ⟨a,he⟩

end SymmetricSubgroupAsymptotics.CFSGE6GeckPositiveWordRootSections
