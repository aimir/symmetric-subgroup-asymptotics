import SymmetricSubgroupAsymptotics.FiniteSylowNormalIntersection
import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedPositiveSylow
import SymmetricSubgroupAsymptotics.CFSGReeFFourDerivedOppositeSylow
import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalPositiveSylow
import SymmetricSubgroupAsymptotics.CFSGDisjointSylowProjectiveCardinality

/-! The literal positive intersection with the derived fixed group is Sylow
for every parameter, including zero. Opposition separates two such Sylows,
so this intersection survives the full central quotient defining the original
model. No whole-positive containment or cardinality assertion is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourAllParameterDerivedPositive
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourFixedPositiveSylow CFSGReeFFourFixedAmbientHom
open CFSGReeFFourDerivedAmbientHom CFSGReeFFourDerivedOppositeSylow
open CFSGReeFFourOppositionFixedPositiveNegative CFSGReeFFourOriginalPositiveSylow
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private instance fixed_finite (m : ℕ) : Finite (originalModelFixed m) :=
  Finite.of_injective (fixedAmbientHom m) (fixedAmbientHom_injective m)

def positiveSylow (m : ℕ) : Sylow 2 (commutator (originalModelFixed m)) :=
  FiniteSylowNormalIntersection.normalIntersection (fixedPositiveSylow m)
    (commutator (originalModelFixed m))

theorem positiveSylow_coe (m : ℕ) :
    (positiveSylow m : Subgroup (commutator (originalModelFixed m))) = derivedPositive m := by
  rw [positiveSylow, FiniteSylowNormalIntersection.normalIntersection_coe,
    fixedPositiveSylow_coe]
  rfl

def negativeSylow (m : ℕ) : Sylow 2 (commutator (originalModelFixed m)) :=
  (positiveSylow m).mapSurjective (f := (derivedOppositionAut m).toMonoidHom)
    (derivedOppositionAut m).surjective

theorem negativeSylow_coe (m : ℕ) :
    (negativeSylow m : Subgroup (commutator (originalModelFixed m))) =
      (derivedPositive m).map (derivedOppositionAut m).toMonoidHom := by
  change (positiveSylow m : Subgroup (commutator (originalModelFixed m))).map
    (derivedOppositionAut m).toMonoidHom = _
  rw [positiveSylow_coe]

theorem negativeSylow_le_negative (m : ℕ) :
    (negativeSylow m : Subgroup (commutator (originalModelFixed m))) ≤
      (fixedNegative m).comap (commutator (originalModelFixed m)).subtype := by
  rw [negativeSylow_coe]
  rintro _ ⟨u, hu, rfl⟩
  have hup : u.val ∈ fixedPositive m := hu
  have hn : oppositionFixed m * u.val * (oppositionFixed m)⁻¹ ∈ fixedNegative m := by
    rw [← fixed_positive_image_eq_fixed_negative]
    exact ⟨u.val, hup, rfl⟩
  change (derivedOppositionAut m u).val ∈ fixedNegative m
  simpa only [derivedOppositionAut, MulAut.conjNormal_apply] using hn

theorem opposite_inf (m : ℕ) :
    (positiveSylow m : Subgroup (commutator (originalModelFixed m))) ⊓
      (negativeSylow m : Subgroup (commutator (originalModelFixed m))) = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  have hp : x ∈ derivedPositive m := positiveSylow_coe m ▸ hx.1
  have hn := negativeSylow_le_negative m hx.2
  have hb : x.val ∈ fixedPositive m ⊓ fixedNegative m := ⟨hp, hn⟩
  rw [fixed_positive_inf_negative, Subgroup.mem_bot] at hb
  exact Subgroup.mem_bot.mpr (Subtype.ext hb)

def positiveHom (m : ℕ) : derivedPositive m →* CFSG.Models.ReeF4 m :=
  (derivedReeHom m).comp (derivedPositive m).subtype

theorem positiveHom_injective (m : ℕ) : Function.Injective (positiveHom m) := by
  have hi := CFSGDisjointSylowProjectiveCardinality.central_quotient_injective
    (positiveSylow m) (negativeSylow m) (opposite_inf m)
  have hi' : Function.Injective
      ((QuotientGroup.mk' (Subgroup.center (commutator (originalModelFixed m)))).comp
        (derivedPositive m).subtype) := by
    intro x y hxy
    have hx : x.val ∈ (positiveSylow m : Subgroup (commutator (originalModelFixed m))) := by
      rw [positiveSylow_coe]
      exact x.property
    have hy : y.val ∈ (positiveSylow m : Subgroup (commutator (originalModelFixed m))) := by
      rw [positiveSylow_coe]
      exact y.property
    have he : (⟨x.val, hx⟩ : positiveSylow m) = (⟨y.val, hy⟩ : positiveSylow m) := hi hxy
    exact Subtype.ext (congrArg (fun z : positiveSylow m =>
      (z : commutator (originalModelFixed m))) he)
  exact (originalReeEquiv m).symm.injective.comp hi'

def titsPositiveHom : derivedPositive 0 →* CFSG.Models.Tits := positiveHom 0

theorem titsPositiveHom_injective : Function.Injective titsPositiveHom :=
  positiveHom_injective 0

end SymmetricSubgroupAsymptotics.CFSGReeFFourAllParameterDerivedPositive
