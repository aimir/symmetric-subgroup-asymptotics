import SymmetricSubgroupAsymptotics.CFSGReeFFourRegularFixedPositive
import SymmetricSubgroupAsymptotics.CFSGFFourE6AmbientPositiveSylow

/-! The actual original ReeF4 fixed group embeds in the literal E6
elementary group. Its positive preimage contains the constructed regular
fixed element. Ambient uniqueness is established by its six nonzero
leading coordinates, not by recognition of the entire positive group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourFixedAmbientHom
open CFSGReeFFourFieldParameters CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourFixedPositiveFamilies CFSGReeFFourRegularFixedPositive
open CFSGFFourE6AmbientPositiveSylow CFSGFFourE6RootSubgroups
open CFSGFFourOriginalMiddleWords CFSGFFourOriginalFoldedEquivalence
open CFSGTwistedE6GeckPositiveTwist CFSGNormTwoCoordinateLeadingFactor
open CFSGNormTwoCoordinateRegularPositiveUniqueness CFSGExceptionalCartanPositiveDefinite
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos

def fixedAmbientHom (m : ℕ) : originalModelFixed m→*AmbientGroup (Field m) :=
  (fixedRawHom m).codRestrict (AmbientGroup (Field m)) (fun g=>by
    apply foldedModel_le_ambient (Field m)
    change rawHom (Field m) g.val∈
      CFSGSerreQuadraticMatrix.canonicalElementaryGroup CFSGFFourSerreMatrices.realizationData (Field m)
    exact (modelEquivFolded (Field m) g.val).property)

theorem fixedAmbientHom_val (m : ℕ) (g : originalModelFixed m) :
    (fixedAmbientHom m g).val=fixedRawHom m g := rfl

theorem fixedAmbientHom_injective (m : ℕ) : Function.Injective (fixedAmbientHom m) := by
  intro x y he
  have hv := congrArg (fun z : AmbientGroup (Field m)=>z.val) he
  change rawHom (Field m) x.val=rawHom (Field m) y.val at hv
  exact Subtype.ext (rawHom_injective (Field m) hv)

theorem fixedPositive_eq_preimage (m : ℕ) :
    fixedPositive m=(AmbientPositive (Field m)).comap (fixedAmbientHom m) := by
  ext g
  rfl

theorem fixedAmbientHom_regular_positive (m : ℕ) :
    fixedAmbientHom m (regularFixed m)∈AmbientPositive (Field m) := by
  change rawHom (Field m) (regularFixed m).val∈Positive (Field m)
  exact regularFixed_mem_fixedPositive m

theorem fixedAmbientHom_regular_unique (m : ℕ) (g : AmbientGroup (Field m))
    (hg : g⁻¹*fixedAmbientHom m (regularFixed m)*g∈AmbientPositive (Field m)) :
    g∈Subgroup.normalizer (AmbientPositive (Field m) : Set (AmbientGroup (Field m))) := by
  have hpos : (fixedAmbientHom m (regularFixed m)).val∈Positive (Field m) :=
    fixedAmbientHom_regular_positive m
  have hlead (i : Fin 6) : leadingCoordinates A hd hs hp ho (Field m)
      (fixedAmbientHom m (regularFixed m)).val i≠0 := by
    change leadingCoordinates A hd hs hp ho (Field m)
      (rawHom (Field m) (regularFixed m).val) i≠0
    rw [regularFixed_leading]
    exact one_ne_zero
  have hgraw : g.val⁻¹*(fixedAmbientHom m (regularFixed m)).val*g.val∈Positive (Field m) := hg
  have hn := mem_normalizer_of_regular_conjugate A hd hs hp ho (Field m)
    g.val (fixedAmbientHom m (regularFixed m)).val g.property hpos hlead hgraw
  apply Subgroup.mem_normalizer_iff.mpr
  intro x
  exact Subgroup.mem_normalizer_iff.mp hn x.val

end SymmetricSubgroupAsymptotics.CFSGReeFFourFixedAmbientHom
