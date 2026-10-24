import SymmetricSubgroupAsymptotics.CFSGReeFFourDerivedAmbientHom
import SymmetricSubgroupAsymptotics.CFSGRegularElementSylowPreimage

/-! The actual intersection of U with the original fixed group's derived
subgroup is Sylow, with soluble normalizer, for m>0. This does not identify
that intersection with all of fixed U or handle the Tits parameter. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourDerivedPositiveSylow
open CFSGReeFFourFieldParameters CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourDerivedAmbientHom CFSGFFourE6AmbientPositiveSylow
open CFSGRegularElementSylowPreimage
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

def derivedPositiveSylow (m : ℕ) (hm : 0<m) : Sylow 2 (commutator (originalModelFixed m)) :=
  preimageSylow (ambientSylow (Field m) 2) (derivedAmbientHom m)
    (derivedAmbientHom_injective m) (derivedRegularWitness m hm)
    (derivedRegularWitness_positive m hm) (derivedAmbientHom_regular_unique m hm)

theorem derivedPositiveSylow_coe (m : ℕ) (hm : 0<m) :
    (derivedPositiveSylow m hm : Subgroup (commutator (originalModelFixed m)))=derivedPositive m := by
  change (AmbientPositive (Field m)).comap (derivedAmbientHom m)=derivedPositive m
  exact (derivedPositive_eq_preimage m).symm

theorem derived_positive_normalizer_soluble (m : ℕ) (hm : 0<m) :
    IsSolvable (Subgroup.normalizer
      (derivedPositive m : Set (commutator (originalModelFixed m)))) := by
  letI : IsSolvable (Subgroup.normalizer
      ((ambientSylow (Field m) 2 : Subgroup (AmbientGroup (Field m))) :
        Set (AmbientGroup (Field m)))) := by
    rw [ambientSylow_coe]
    exact ambient_normalizer_soluble (Field m)
  rw [derivedPositive_eq_preimage]
  exact preimage_normalizer_soluble (ambientSylow (Field m) 2) (derivedAmbientHom m)
    (derivedAmbientHom_injective m) (derivedRegularWitness m hm)
    (derivedRegularWitness_positive m hm) (derivedAmbientHom_regular_unique m hm)

end SymmetricSubgroupAsymptotics.CFSGReeFFourDerivedPositiveSylow
