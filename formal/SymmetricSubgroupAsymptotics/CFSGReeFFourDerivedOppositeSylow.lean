import SymmetricSubgroupAsymptotics.CFSGReeFFourDerivedPositiveSylow
import SymmetricSubgroupAsymptotics.CFSGReeFFourOppositionFixedPositiveNegative
import Mathlib.GroupTheory.GroupAction.ConjAct

/-! Opposition restricts to the actual derived subgroup by normality.
Its image of the derived positive Sylow is disjoint from that Sylow.
The explicit opposition is not asserted to belong to the derived group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourDerivedOppositeSylow
open CFSGReeFFourFieldParameters CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourFixedPositiveFamilies CFSGReeFFourDerivedAmbientHom
open CFSGReeFFourDerivedPositiveSylow CFSGReeFFourOppositionFixedPositiveNegative
open CFSGFFourOriginalMiddleWords CFSGTwistedE6GeckPositiveTwist
open CFSGNormTwoGeckOppositeIntersection CFSGNormTwoCoordinateHeight
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private instance derived_finite (m : ℕ) : Finite (commutator (originalModelFixed m)) :=
  Finite.of_injective (derivedAmbientHom m) (derivedAmbientHom_injective m)

theorem fixed_positive_inf_negative (m : ℕ) : fixedPositive m⊓fixedNegative m=⊥ := by
  apply eq_bot_iff.mpr
  intro g hg
  have hraw : rawHom (Field m) g.val∈Positive (Field m)⊓
      CFSGNormTwoGeckPositivePGroup.rootGroup A hs hp E6Base E6Index (Field m) true := hg
  rw [positive_inf_negative A hs hp E6Base E6Index coordinateHeight
    (simple_height A hd hs hp ho) (Field m),Subgroup.mem_bot] at hraw
  apply Subgroup.mem_bot.mpr
  apply Subtype.ext
  apply rawHom_injective (Field m)
  change rawHom (Field m) g.val=rawHom (Field m)
    (1 : CFSG.Models.Chevalley.Model CartanMatrix.F₄ (Field m))
  rw [map_one]
  exact hraw

def derivedOppositionAut (m : ℕ) : MulAut (commutator (originalModelFixed m)) :=
  MulAut.conjNormal (oppositionFixed m)

def derivedNegativeSylow (m : ℕ) (hm : 0<m) : Sylow 2 (commutator (originalModelFixed m)) :=
  (derivedPositiveSylow m hm).mapSurjective
    (f:=(derivedOppositionAut m).toMonoidHom) (derivedOppositionAut m).surjective

theorem derivedNegativeSylow_coe (m : ℕ) (hm : 0<m) :
    (derivedNegativeSylow m hm : Subgroup (commutator (originalModelFixed m)))=
      (derivedPositive m).map (derivedOppositionAut m).toMonoidHom := by
  change ((derivedPositiveSylow m hm : Subgroup (commutator (originalModelFixed m))).map
    (derivedOppositionAut m).toMonoidHom)=_
  rw [derivedPositiveSylow_coe]

theorem derivedNegativeSylow_le_negative (m : ℕ) (hm : 0<m) :
    (derivedNegativeSylow m hm : Subgroup (commutator (originalModelFixed m)))≤
      (fixedNegative m).comap (commutator (originalModelFixed m)).subtype := by
  rw [derivedNegativeSylow_coe]
  rintro _ ⟨u,hu,rfl⟩
  have hup : u.val∈fixedPositive m := hu
  have hn : oppositionFixed m*u.val*(oppositionFixed m)⁻¹∈fixedNegative m := by
    rw [←fixed_positive_image_eq_fixed_negative]
    exact ⟨u.val,hup,rfl⟩
  change (derivedOppositionAut m u).val∈fixedNegative m
  simpa only [derivedOppositionAut,MulAut.conjNormal_apply] using hn

theorem derived_opposite_sylows_inf (m : ℕ) (hm : 0<m) :
    (derivedPositiveSylow m hm : Subgroup (commutator (originalModelFixed m)))⊓
      (derivedNegativeSylow m hm : Subgroup (commutator (originalModelFixed m)))=⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  have hp' : x∈derivedPositive m := derivedPositiveSylow_coe m hm ▸ hx.1
  have hn' : x∈(fixedNegative m).comap (commutator (originalModelFixed m)).subtype :=
    derivedNegativeSylow_le_negative m hm hx.2
  have hboth : x.val∈fixedPositive m⊓fixedNegative m := ⟨hp',hn'⟩
  rw [fixed_positive_inf_negative,Subgroup.mem_bot] at hboth
  exact Subgroup.mem_bot.mpr (Subtype.ext hboth)

end SymmetricSubgroupAsymptotics.CFSGReeFFourDerivedOppositeSylow
