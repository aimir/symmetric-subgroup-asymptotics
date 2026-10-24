import SymmetricSubgroupAsymptotics.CFSGReeFFourDerivedRegularPositive
import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedAmbientHom

/-! Literal ambient inclusion of the original fixed group's derived
subgroup. The regular witness is chosen inside that derived subgroup,
only for m>0. No equality with the full fixed group is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourDerivedAmbientHom
open CFSGReeFFourFieldParameters CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourFixedPositiveFamilies CFSGReeFFourDerivedRegularPositive
open CFSGReeFFourFixedAmbientHom CFSGFFourE6AmbientPositiveSylow
open CFSGFFourOriginalMiddleWords CFSGTwistedE6GeckPositiveTwist
open CFSGNormTwoCoordinateLeadingFactor CFSGNormTwoCoordinateRegularPositiveUniqueness
open CFSGExceptionalCartanPositiveDefinite
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos

def derivedAmbientHom (m : ℕ) : commutator (originalModelFixed m)→*AmbientGroup (Field m) :=
  (fixedAmbientHom m).comp (commutator (originalModelFixed m)).subtype

theorem derivedAmbientHom_val (m : ℕ) (g : commutator (originalModelFixed m)) :
    (derivedAmbientHom m g).val=rawHom (Field m) g.val.val := rfl

theorem derivedAmbientHom_injective (m : ℕ) : Function.Injective (derivedAmbientHom m) :=
  (fixedAmbientHom_injective m).comp (commutator (originalModelFixed m)).subtype_injective

def derivedPositive (m : ℕ) : Subgroup (commutator (originalModelFixed m)) :=
  (fixedPositive m).comap (commutator (originalModelFixed m)).subtype

theorem derivedPositive_eq_preimage (m : ℕ) :
    derivedPositive m=(AmbientPositive (Field m)).comap (derivedAmbientHom m) := by
  ext g
  rfl

def derivedRegularWitness (m : ℕ) (hm : 0<m) : commutator (originalModelFixed m) :=
  Classical.choose (exists_derived_regular_positive m hm)

theorem derivedRegularWitness_positive (m : ℕ) (hm : 0<m) :
    derivedAmbientHom m (derivedRegularWitness m hm)∈AmbientPositive (Field m) :=
  (Classical.choose_spec (exists_derived_regular_positive m hm)).1

theorem derivedRegularWitness_leading (m : ℕ) (hm : 0<m) (i : Fin 6) :
    leadingCoordinates A hd hs hp ho (Field m)
      (derivedAmbientHom m (derivedRegularWitness m hm)).val i≠0 :=
  (Classical.choose_spec (exists_derived_regular_positive m hm)).2 i

theorem derivedAmbientHom_regular_unique (m : ℕ) (hm : 0<m) (g : AmbientGroup (Field m))
    (hg : g⁻¹*derivedAmbientHom m (derivedRegularWitness m hm)*g∈AmbientPositive (Field m)) :
    g∈Subgroup.normalizer (AmbientPositive (Field m) : Set (AmbientGroup (Field m))) := by
  have hpos : (derivedAmbientHom m (derivedRegularWitness m hm)).val∈Positive (Field m) :=
    derivedRegularWitness_positive m hm
  have hgraw : g.val⁻¹*(derivedAmbientHom m (derivedRegularWitness m hm)).val*g.val∈
      Positive (Field m) := hg
  have hn := mem_normalizer_of_regular_conjugate A hd hs hp ho (Field m)
    g.val (derivedAmbientHom m (derivedRegularWitness m hm)).val g.property hpos
    (derivedRegularWitness_leading m hm) hgraw
  apply Subgroup.mem_normalizer_iff.mpr
  intro x
  exact Subgroup.mem_normalizer_iff.mp hn x.val

end SymmetricSubgroupAsymptotics.CFSGReeFFourDerivedAmbientHom
