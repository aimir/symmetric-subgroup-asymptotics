import SymmetricSubgroupAsymptotics.CFSGReeFFourDerivedPositiveSylow
import SymmetricSubgroupAsymptotics.CFSGSolubleSylowNormalizerSurjective

/-! The derived-group Sylow and its soluble normalizer descend to the
literal original ReeF4 model through its FULL central quotient.
This assertion is for m>0 and does not assert two-Sylow generation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalPositiveSylow
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourDerivedAmbientHom
open CFSGReeFFourDerivedPositiveSylow CFSGSolubleSylowNormalizerSurjective
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private instance derived_finite (m : ℕ) : Finite (commutator (originalModelFixed m)) :=
  Finite.of_injective (derivedAmbientHom m) (derivedAmbientHom_injective m)

def derivedReeHom (m : ℕ) : commutator (originalModelFixed m)→*CFSG.Models.ReeF4 m :=
  (originalReeEquiv m).symm.toMonoidHom.comp
    (QuotientGroup.mk' (Subgroup.center (commutator (originalModelFixed m))))

theorem derivedReeHom_surjective (m : ℕ) : Function.Surjective (derivedReeHom m) :=
  (originalReeEquiv m).symm.surjective.comp (QuotientGroup.mk'_surjective _)

def reePositiveSylow (m : ℕ) (hm : 0<m) : Sylow 2 (CFSG.Models.ReeF4 m) :=
  (derivedPositiveSylow m hm).mapSurjective (f:=derivedReeHom m) (derivedReeHom_surjective m)

theorem reePositiveSylow_coe (m : ℕ) (hm : 0<m) :
    (reePositiveSylow m hm : Subgroup (CFSG.Models.ReeF4 m))=
      (derivedPositive m).map (derivedReeHom m) := by
  change ((derivedPositiveSylow m hm : Subgroup (commutator (originalModelFixed m))).map
    (derivedReeHom m))=_
  rw [derivedPositiveSylow_coe]

theorem ree_positive_normalizer_soluble (m : ℕ) (hm : 0<m) :
    IsSolvable (Subgroup.normalizer
      (reePositiveSylow m hm : Set (CFSG.Models.ReeF4 m))) := by
  have hsol : IsSolvable (Subgroup.normalizer
      (derivedPositiveSylow m hm : Set (commutator (originalModelFixed m)))) := by
    have hn := congrArg
      (fun S : Subgroup (commutator (originalModelFixed m))=>
        Subgroup.normalizer (S : Set (commutator (originalModelFixed m))))
      (derivedPositiveSylow_coe m hm)
    letI : IsSolvable (Subgroup.normalizer
        (derivedPositive m : Set (commutator (originalModelFixed m)))) :=
      derived_positive_normalizer_soluble m hm
    have hN : Subgroup.normalizer
        (derivedPositiveSylow m hm : Set (commutator (originalModelFixed m)))≤
      Subgroup.normalizer (derivedPositive m : Set (commutator (originalModelFixed m))) :=
      le_of_eq hn
    exact solvable_of_solvable_injective (f:=Subgroup.inclusion hN)
      (Subgroup.inclusion_injective hN)
  exact normalizer_soluble_map (derivedReeHom m) (derivedReeHom_surjective m)
    (derivedPositiveSylow m hm) hsol

end SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalPositiveSylow
