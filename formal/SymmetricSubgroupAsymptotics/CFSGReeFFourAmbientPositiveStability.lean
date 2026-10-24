import SymmetricSubgroupAsymptotics.CFSGFFourOriginalAmbientHom
import SymmetricSubgroupAsymptotics.CFSGRegularSylowPreimageUniqueness
import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedAmbientHom

/-! The exceptional automorphism preserves the WHOLE original F4
positive preimage. It fixes the genuine regular witness, and that
witness lies in a unique Sylow preimage. This works also for m=0 and
uses neither ordinary F4 simplicity nor four-simple-root generation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourAmbientPositiveStability
open CFSG.Models.Chevalley CFSGReeFFourFieldParameters
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourOriginalAutomorphism
open CFSGReeFFourRegularFixedPositive CFSGReeFFourFixedAmbientHom
open CFSGFFourOriginalAmbientHom CFSGFFourE6AmbientPositiveSylow
open CFSGRegularElementSylowPreimage CFSGRegularSylowPreimageUniqueness
open CFSGReeFFourFixedPositiveFamilies
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private theorem regular_positive (m : ℕ) :
    modelAmbientHom (Field m) (regularFixed m).val∈AmbientPositive (Field m) :=
  fixedAmbientHom_regular_positive m

private theorem regular_unique (m : ℕ) (g : AmbientGroup (Field m))
    (hg : g⁻¹*modelAmbientHom (Field m) (regularFixed m).val*g∈AmbientPositive (Field m)) :
    g∈Subgroup.normalizer (AmbientPositive (Field m) : Set (AmbientGroup (Field m))) :=
  fixedAmbientHom_regular_unique m g hg

def modelPositiveSylow (m : ℕ) : Sylow 2 (Model CartanMatrix.F₄ (Field m)) :=
  preimageSylow (ambientSylow (Field m) 2) (modelAmbientHom (Field m))
    (modelAmbientHom_injective (Field m)) (regularFixed m).val
    (regular_positive m) (regular_unique m)

theorem modelPositiveSylow_coe (m : ℕ) :
    (modelPositiveSylow m : Subgroup (Model CartanMatrix.F₄ (Field m)))=modelPositive (Field m) := rfl

theorem fixedPositive_eq_model_comap (m : ℕ) :
    fixedPositive m=(modelPositive (Field m)).comap (originalModelFixed m).subtype := by
  ext g
  rfl

theorem ree_preserves_modelPositive (m : ℕ) :
    (modelPositive (Field m)).map (reeAutomorphism m).toMonoidHom=modelPositive (Field m) :=
  automorphism_preserves_regular_preimage (ambientSylow (Field m) 2)
    (modelAmbientHom (Field m)) (modelAmbientHom_injective (Field m)) (regularFixed m).val
    (regular_positive m) (regular_unique m) (reeAutomorphism m) (regularFixed m).property

end SymmetricSubgroupAsymptotics.CFSGReeFFourAmbientPositiveStability
