import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryOuterParabolicSolvable
import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryMiddleParabolicSolvable
import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryDerivedNormalizerParabolic
import SymmetricSubgroupAsymptotics.CFSGReeFFourAllParameterDerivedPositive
import SymmetricSubgroupAsymptotics.CFSGSolubleSylowNormalizerSurjective

/-! The actual binary derived positive Sylow has a soluble normalizer,
and this descends through the FULL derived-centre quotient defining Tits.
The same literal U intersection D and actual quotient homomorphism are
retained. Two-Sylow generation and global class capacity are not asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourBinarySylowNormalizerSolvable
open CFSGReeFFourBinaryDerivedNormalizerParabolic
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourDerivedAmbientHom
open CFSGReeFFourOriginalPositiveSylow CFSGReeFFourAllParameterDerivedPositive
open CFSGSolubleSylowNormalizerSurjective
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private abbrev D := commutator (originalModelFixed 0)
private instance derivedFinite : Finite D :=
  Finite.of_injective (derivedAmbientHom 0) (derivedAmbientHom_injective 0)

private theorem normalizer_solvable_of_injective {G H : Type*} [Group G] [Group H]
    (rho : G →* H) (hrho : Function.Injective rho) (P : Subgroup G)
    (hsol : IsSolvable (Subgroup.normalizer (P.map rho : Set H))) :
    IsSolvable (Subgroup.normalizer (P : Set G)) := by
  let N := Subgroup.normalizer (P : Set G)
  let M := Subgroup.normalizer (P.map rho : Set H)
  letI : IsSolvable M := hsol
  let F : N →* M :=
    { toFun := fun x => ⟨rho x.val, P.le_normalizer_map rho ⟨x.val, x.property, rfl⟩⟩
      map_one' := Subtype.ext rho.map_one
      map_mul' x y := Subtype.ext (rho.map_mul x.val y.val) }
  have hF : Function.Injective F := by
    intro x y h
    apply Subtype.ext
    apply hrho
    exact congrArg (fun z : M => z.val) h
  exact solvable_of_solvable_injective (f := F) hF

theorem ambientDerivedPositive_normalizer_solvable :
    IsSolvable (Subgroup.normalizer (ambientDerivedPositive 0 : Set (originalModelFixed 0))) := by
  rcases ambientDerivedPositive_zero_normalizer_le_outer_or_middle with h | h
  · letI := CFSGReeFFourBinaryOuterParabolicSolvable.outerParabolic_zero_solvable
    exact solvable_of_solvable_injective (f := Subgroup.inclusion h)
      (Subgroup.inclusion_injective h)
  · letI := CFSGReeFFourBinaryMiddleParabolicSolvable.middleParabolic_zero_solvable
    exact solvable_of_solvable_injective (f := Subgroup.inclusion h)
      (Subgroup.inclusion_injective h)

private theorem derivedPositive_map : (derivedPositive 0).map D.subtype = ambientDerivedPositive 0 := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, y.property⟩
  · intro hx
    exact ⟨⟨x, hx.2⟩, hx.1, rfl⟩

theorem derivedPositive_normalizer_solvable :
    IsSolvable (Subgroup.normalizer (derivedPositive 0 : Set D)) := by
  have hsol : IsSolvable (Subgroup.normalizer ((derivedPositive 0).map D.subtype : Set (originalModelFixed 0))) := by
    rw [derivedPositive_map]
    exact ambientDerivedPositive_normalizer_solvable
  exact normalizer_solvable_of_injective D.subtype Subtype.val_injective (derivedPositive 0) hsol

def titsPositiveSylow : Sylow 2 CFSG.Models.Tits :=
  (positiveSylow 0).mapSurjective (f := derivedReeHom 0) (derivedReeHom_surjective 0)

theorem titsPositiveSylow_coe : (titsPositiveSylow : Subgroup CFSG.Models.Tits) =
    (derivedPositive 0).map (derivedReeHom 0) := by
  change (positiveSylow 0 : Subgroup D).map (derivedReeHom 0) = _
  rw [positiveSylow_coe]

theorem titsPositiveSylow_normalizer_solvable :
    IsSolvable (Subgroup.normalizer (titsPositiveSylow : Set CFSG.Models.Tits)) := by
  have hn := congrArg (fun S : Subgroup D => Subgroup.normalizer (S : Set D)) (positiveSylow_coe 0)
  letI := derivedPositive_normalizer_solvable
  have hN : Subgroup.normalizer (positiveSylow 0 : Set D) ≤
      Subgroup.normalizer (derivedPositive 0 : Set D) := le_of_eq hn
  have hsol : IsSolvable (Subgroup.normalizer (positiveSylow 0 : Set D)) :=
    solvable_of_solvable_injective (f := Subgroup.inclusion hN) (Subgroup.inclusion_injective hN)
  exact normalizer_soluble_map (derivedReeHom 0) (derivedReeHom_surjective 0) (positiveSylow 0) hsol

theorem exists_tits_sylow_soluble_normalizer :
    ∃ P : Sylow 2 CFSG.Models.Tits, IsSolvable (Subgroup.normalizer (P : Set CFSG.Models.Tits)) :=
  ⟨titsPositiveSylow, titsPositiveSylow_normalizer_solvable⟩

end SymmetricSubgroupAsymptotics.CFSGReeFFourBinarySylowNormalizerSolvable
