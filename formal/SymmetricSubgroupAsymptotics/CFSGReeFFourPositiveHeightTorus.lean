import SymmetricSubgroupAsymptotics.CFSGReeFFourPositiveHeightCoordinates
import SymmetricSubgroupAsymptotics.CFSGReeFFourRawRootCharacter
import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedTorusGroup
import Mathlib.GroupTheory.Commutator.Basic

/-! Literal fixed-torus conjugates stay in each full ReeF4 positive
height tail. Their actual coordinates transform by the proved two-unit
root characters; their differences from the input are genuine original
commutators, including at bad characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourPositiveHeightTorus
open CFSGReeFFourFieldParameters CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourPositiveHeightCoordinates CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourFixedTorus CFSGReeFFourFixedTorusGroup
open CFSGReeFFourRawRootCharacter CFSGFFourOriginalProductTorus
open CFSGFFourOriginalMiddleWords CFSGTwistedE6GeckPositiveTwist
open CFSGTwistedE6GeckHeightQuotientTwist CFSGE6GeckHeightTorusAutomorphism
open CFSGE6GeckProductTorus CFSGNormTwoCoordinateExactHeightLayer
local notation "A" => CartanMatrix.E₆
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots A) := Classical.decEq _

def rawTuple (m : ℕ) (t : (Field m)ˣ×(Field m)ˣ) : Fin 6→(Field m)ˣ :=
  CFSGFFourE6ProductTorus.torusTuple (Field m) (fixedTorusTuple m t.1 t.2)

theorem fixedRawHom_fixedTorusHom (m : ℕ) (t : (Field m)ˣ×(Field m)ˣ) :
    fixedRawHom m (fixedTorusHom m t)=rawProductTorus (Field m) (rawTuple m t) := by
  change rawHom (Field m) (modelProductTorusHom (Field m) (fixedTorusTuple m t.1 t.2))=_
  exact rawHom_modelProductTorus (Field m) (fixedTorusTuple m t.1 t.2)

def torusConjugate (m : ℕ) (h : ℤ) (t : (Field m)ˣ×(Field m)ˣ)
    (u : tail m h) : tail m h := by
  let g := fixedTorusHom m t*u.val.val*(fixedTorusHom m t)⁻¹
  have hraw : fixedRawHom m g=rawProductTorus (Field m) (rawTuple m t)*
      (positiveRawHom m u.val).val*(rawProductTorus (Field m) (rawTuple m t))⁻¹ := by
    simp only [g,map_mul (fixedRawHom m),map_inv (fixedRawHom m),fixedRawHom_fixedTorusHom]
    rfl
  have hg : g∈fixedPositive m := by
    change fixedRawHom m g∈Positive (Field m)
    rw [hraw]
    exact (positiveTorus (Field m) (rawTuple m t) (positiveRawHom m u.val)).property
  refine ⟨⟨g,hg⟩,?_⟩
  change positiveRawHom m ⟨g,hg⟩∈TailInPositive (Field m) h
  have he : positiveRawHom m ⟨g,hg⟩=
      positiveTorus (Field m) (rawTuple m t) (positiveRawHom m u.val) := by
    apply Subtype.ext
    exact hraw
  rw [he]
  have hm : positiveTorus (Field m) (rawTuple m t) (positiveRawHom m u.val)∈
      (TailInPositive (Field m) h).map (positiveTorus (Field m) (rawTuple m t)).toMonoidHom :=
    ⟨positiveRawHom m u.val,u.property,rfl⟩
  rw [tailInPositive_torus_image_eq] at hm
  exact hm

theorem torusConjugate_coordinate (m : ℕ) (h : ℤ) (hh : 0<h)
    (t : (Field m)ˣ×(Field m)ˣ) (u : tail m h) (k : ExactHeightRoot A h) :
    (coordinateHom m h hh (torusConjugate m h t u)).toAdd k=
      (CFSGReeFFourRootTorusCharacters.rootCharacter m k.val.val t : Field m)*
        (coordinateHom m h hh u).toAdd k := by
  have hv : (toAmbientTail m h (torusConjugate m h t u)).val=
      positiveTorus (Field m) (rawTuple m t) (toAmbientTail m h u).val := by
    apply Subtype.ext
    change fixedRawHom m (fixedTorusHom m t*u.val.val*(fixedTorusHom m t)⁻¹)=_
    simp only [map_mul (fixedRawHom m),map_inv (fixedRawHom m),fixedRawHom_fixedTorusHom]
    rfl
  have hc := CFSGE6GeckHeightCoordinateHom.coordinateHom_torus (Field m) (rawTuple m t)
    h hh (toAmbientTail m h u) (toAmbientTail m h (torusConjugate m h t u)) hv k
  dsimp only [rawTuple] at hc
  rw [raw_root_character_eq] at hc
  exact hc

theorem torus_commutator_mem (m : ℕ) (h : ℤ) (t : (Field m)ˣ×(Field m)ˣ)
    (u : tail m h) :
    ((torusConjugate m h t u*u⁻¹).val : originalModelFixed m)∈commutator (originalModelFixed m) := by
  change ⁅fixedTorusHom m t,u.val.val⁆∈commutator (originalModelFixed m)
  exact Subgroup.commutator_mem_commutator (by trivial) (by trivial)

end SymmetricSubgroupAsymptotics.CFSGReeFFourPositiveHeightTorus
