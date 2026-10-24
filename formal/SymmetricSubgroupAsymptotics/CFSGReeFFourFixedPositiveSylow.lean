import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedAmbientHom
import SymmetricSubgroupAsymptotics.CFSGRegularElementSylowPreimage

/-! The literal fixed-positive preimage is a Sylow 2 subgroup of the
original exceptional-fixed group, with soluble normalizer. The exact
pinned fixedSubgroup receives the same conclusions by its established
equivalence. These are fixed-group assertions, before the derived/full
centre quotient defining ReeF4 or Tits. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourFixedPositiveSylow
open CFSG.Models.Chevalley CFSGReeFFourFieldParameters
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourRegularFixedPositive CFSGReeFFourFixedAmbientHom
open CFSGFFourE6AmbientPositiveSylow CFSGRegularElementSylowPreimage
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

def fixedPositiveSylow (m : ℕ) : Sylow 2 (originalModelFixed m) :=
  preimageSylow (ambientSylow (Field m) 2) (fixedAmbientHom m)
    (fixedAmbientHom_injective m) (regularFixed m)
    (fixedAmbientHom_regular_positive m) (fixedAmbientHom_regular_unique m)

theorem fixedPositiveSylow_coe (m : ℕ) :
    (fixedPositiveSylow m : Subgroup (originalModelFixed m))=fixedPositive m := by
  change (AmbientPositive (Field m)).comap (fixedAmbientHom m)=fixedPositive m
  exact (fixedPositive_eq_preimage m).symm

theorem fixed_positive_normalizer_soluble (m : ℕ) :
    IsSolvable (Subgroup.normalizer (fixedPositive m : Set (originalModelFixed m))) := by
  letI : IsSolvable (Subgroup.normalizer
      ((ambientSylow (Field m) 2 : Subgroup (AmbientGroup (Field m))) :
        Set (AmbientGroup (Field m)))) := by
    rw [ambientSylow_coe]
    exact ambient_normalizer_soluble (Field m)
  rw [fixedPositive_eq_preimage]
  exact preimage_normalizer_soluble (ambientSylow (Field m) 2) (fixedAmbientHom m)
    (fixedAmbientHom_injective m) (regularFixed m)
    (fixedAmbientHom_regular_positive m) (fixedAmbientHom_regular_unique m)

def originalFixedPositiveSylow (m : ℕ) :
    Sylow 2 (fixedSubgroup CartanMatrix.F₄ (Field m) CFSG.Models.reverseNode (originalExponent m)) :=
  (fixedPositiveSylow m).comapOfInjective (originalFixedEquiv m).toMonoidHom
    (originalFixedEquiv m).injective
    (by rw [MonoidHom.range_eq_top.mpr (originalFixedEquiv m).surjective];exact le_top)

theorem originalFixedPositiveSylow_coe (m : ℕ) :
    (originalFixedPositiveSylow m : Subgroup (fixedSubgroup CartanMatrix.F₄ (Field m)
      CFSG.Models.reverseNode (originalExponent m)))=originalFixedPositive m := by
  change (fixedPositiveSylow m : Subgroup (originalModelFixed m)).comap
    (originalFixedEquiv m).toMonoidHom=originalFixedPositive m
  rw [fixedPositiveSylow_coe]
  rfl

theorem original_fixed_positive_normalizer_soluble (m : ℕ) :
    IsSolvable (Subgroup.normalizer (originalFixedPositive m : Set
      (fixedSubgroup CartanMatrix.F₄ (Field m) CFSG.Models.reverseNode (originalExponent m)))) := by
  let M := Subgroup.normalizer (fixedPositive m : Set (originalModelFixed m))
  letI : IsSolvable M := fixed_positive_normalizer_soluble m
  let phi := (originalFixedEquiv m).toMonoidHom.subgroupComap M
  have hphi : Function.Injective phi := by
    intro x y he
    apply Subtype.ext
    apply (originalFixedEquiv m).injective
    exact congrArg (fun z : M=>z.val) he
  have hsol : IsSolvable (M.comap (originalFixedEquiv m).toMonoidHom) :=
    solvable_of_solvable_injective (f:=phi) hphi
  have he := Subgroup.comap_normalizer_eq_of_surjective (fixedPositive m)
    (f:=(originalFixedEquiv m).toMonoidHom) (originalFixedEquiv m).surjective
  exact he ▸ hsol

end SymmetricSubgroupAsymptotics.CFSGReeFFourFixedPositiveSylow
