import SymmetricSubgroupAsymptotics.AffineIrreducibleNormalGenerators
import SymmetricSubgroupAsymptotics.BinaryBitmaskCoordinates
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenInterfaces
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The literal primitive-sixteen row one as an irreducible affine group

The original labels are four-bit masks. The first retained permutation is
the linear map with characteristic polynomial `X^4 + X^3 + X^2 + X + 1`,
and the second is translation by the low bit. Four explicit conjugates
give the coordinate translations. The orbit of every nonzero vector
spans the four-dimensional translation space, checked only on vectors.

The actual generated linear complement has prime order five. The generic
affine normal-chain theorem therefore proves the quotient-socle bound on
every normal quotient of the original sixteen-point permutation group.
There is no group or normal-subgroup census premise.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

abbrev Vector := AffineModel.V 2 4
abbrev LinearGroup := AffineModel.GLV 2 4
abbrev Top := DegreeTwoPrimitiveSixteenInterfaces.row1.top

/-- The chart retains every original point label. -/
def pointEquiv : Vector ≃ Fin 16 where
  toFun v := ⟨binaryVectorMask v, by decide +kernel +revert⟩
  invFun i := binaryVectorOfMask 4 i.val
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- The literal first generator in the four-bit chart. -/
def cycle : LinearGroup where
  toFun v := ![v 0 + v 1, v 0 + v 2, v 0 + v 3, v 0]
  invFun v := ![v 3, v 0 + v 3, v 1 + v 3, v 2 + v 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_add' := by decide +kernel
  map_smul' := by decide +kernel

def firstVector : Vector := binaryVectorOfMask 4 1

def linearAction : LinearGroup →* Equiv.Perm Vector where
  toFun g := g.toEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

def linearPerm : LinearGroup →* Equiv.Perm (Fin 16) :=
  pointEquiv.permCongrHom.toMonoidHom.comp linearAction

def translationPerm : Multiplicative Vector →* Equiv.Perm (Fin 16) :=
  pointEquiv.permCongrHom.toMonoidHom.comp AffineModel.transl

theorem linearPerm_cycle :
    linearPerm cycle = DegreeTwoPrimitiveSixteenInterfaces.row1Generators 0 := by
  ext x
  revert x
  decide +kernel

theorem translationPerm_firstVector :
    translationPerm (Multiplicative.ofAdd firstVector) =
      DegreeTwoPrimitiveSixteenInterfaces.row1Generators 1 := by
  ext x
  revert x
  decide +kernel

def linearGenerators : Fin 1 → LinearGroup := fun _ ↦ cycle
abbrev linearGroup : Subgroup LinearGroup :=
  Subgroup.closure (Set.range linearGenerators)

theorem cycle_mem : cycle ∈ linearGroup :=
  Subgroup.subset_closure ⟨0, rfl⟩

/-- A four-term sum from the orbit of a given vector. -/
def orbitCombination (x : Vector) (c : Fin 16) : Vector :=
  ∑ i : Fin 4, if c.val.testBit i.val then (cycle ^ i.val) x else 0

/-- The first four orbit vectors span for each of the fifteen nonzero inputs.
Only four-bit vectors and sixteen coefficient masks are reduced. -/
theorem orbit_spans : ∀ x : Vector, x ≠ 0 → ∀ y : Vector,
    ∃ c : Fin 16, orbitCombination x c = y := by
  decide +kernel

theorem irreducible : AffineModel.Irreducible linearGroup := by
  intro S hS
  by_cases hbot : S = ⊥
  · exact Or.inl hbot
  right
  have hx : ∃ x ∈ S, x ≠ 0 := by
    by_contra h
    push Not at h
    apply hbot
    apply le_antisymm _ bot_le
    intro x hx
    exact AddSubgroup.mem_bot.mpr (h x hx)
  obtain ⟨x, hx, hx0⟩ := hx
  apply top_unique
  intro y _hy
  obtain ⟨c, hc⟩ := orbit_spans x hx0 y
  rw [← hc]
  unfold orbitCombination
  apply S.sum_mem
  intro i _hi
  split
  · exact hS (cycle ^ i.val) (linearGroup.pow_mem cycle_mem i.val) x hx
  · exact S.zero_mem

private def translationExponent : Fin 4 → ℕ := ![0, 4, 3, 2]

/-- Each coordinate translation is a displayed conjugate of generator one. -/
def translationFactor (v : Vector) (i : Fin 4) : Equiv.Perm (Fin 16) :=
  if v i = 0 then 1 else
    DegreeTwoPrimitiveSixteenInterfaces.row1Generators 0 ^ translationExponent i *
      DegreeTwoPrimitiveSixteenInterfaces.row1Generators 1 *
      (DegreeTwoPrimitiveSixteenInterfaces.row1Generators 0 ^ translationExponent i)⁻¹

def translationWord (v : Vector) : Equiv.Perm (Fin 16) :=
  translationFactor v 0 * translationFactor v 1 *
    translationFactor v 2 * translationFactor v 3

theorem translationWord_eq (v : Vector) :
    translationWord v = translationPerm (Multiplicative.ofAdd v) := by
  ext x
  revert v x
  decide +kernel

theorem translationFactor_mem (v : Vector) (i : Fin 4) :
    translationFactor v i ∈ Top := by
  have ha : DegreeTwoPrimitiveSixteenInterfaces.row1Generators 0 ∈ Top :=
    Subgroup.subset_closure (Set.mem_range_self 0)
  have ht : DegreeTwoPrimitiveSixteenInterfaces.row1Generators 1 ∈ Top :=
    Subgroup.subset_closure (Set.mem_range_self 1)
  unfold translationFactor
  split
  · exact Top.one_mem
  · exact Top.mul_mem (Top.mul_mem (Top.pow_mem ha _) ht)
      (Top.inv_mem (Top.pow_mem ha _))

theorem translation_mem (v : Multiplicative Vector) : translationPerm v ∈ Top := by
  change translationPerm (Multiplicative.ofAdd (Multiplicative.toAdd v)) ∈ Top
  rw [← translationWord_eq]
  exact Top.mul_mem
    (Top.mul_mem
      (Top.mul_mem (translationFactor_mem _ 0) (translationFactor_mem _ 1))
      (translationFactor_mem _ 2))
    (translationFactor_mem _ 3)

theorem linearPerm_mem {r : LinearGroup} (hr : r ∈ linearGroup) :
    linearPerm r ∈ Top := by
  induction hr using Subgroup.closure_induction with
  | mem r hr =>
    obtain ⟨i, rfl⟩ := hr
    rw [show linearGenerators i = cycle from rfl, linearPerm_cycle]
    exact Subgroup.subset_closure (Set.mem_range_self 0)
  | one => simpa only [map_one] using Top.one_mem
  | mul r s _ _ hr hs => simpa only [map_mul] using Top.mul_mem hr hs
  | inv r _ hr => simpa only [map_inv] using Top.inv_mem hr

/-- The faithful affine action still uses the original sixteen labels. -/
def affineAction : AffineModel.Aff linearGroup →* Equiv.Perm (Fin 16) :=
  pointEquiv.permCongrHom.toMonoidHom.comp (AffineModel.action linearGroup)

theorem affineAction_injective : Function.Injective affineAction :=
  pointEquiv.permCongrHom.injective.comp (AffineModel.action_injective linearGroup)

theorem affineAction_inl (v : Multiplicative Vector) :
    affineAction (SemidirectProduct.inl v) = translationPerm v := by
  ext x
  rfl

theorem affineAction_inr (r : linearGroup) :
    affineAction (SemidirectProduct.inr r) = linearPerm r.1 := by
  apply Equiv.ext
  intro x
  change pointEquiv (0 + r.1 (pointEquiv.symm x)) =
    pointEquiv (r.1 (pointEquiv.symm x))
  rw [zero_add]

theorem affineAction_range : affineAction.range = Top := by
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    rw [← SemidirectProduct.inl_left_mul_inr_right g, map_mul,
      affineAction_inl, affineAction_inr]
    exact Top.mul_mem (translation_mem g.left) (linearPerm_mem g.right.2)
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact ⟨SemidirectProduct.inr (⟨cycle, cycle_mem⟩ : linearGroup),
        (affineAction_inr _).trans linearPerm_cycle⟩
    · exact ⟨SemidirectProduct.inl (Multiplicative.ofAdd firstVector),
        (affineAction_inl _).trans translationPerm_firstVector⟩

/-- An equivalence of the literal original top with its explicit affine model. -/
def modelEquiv : Top ≃* AffineModel.Aff linearGroup :=
  (MulEquiv.subgroupCongr affineAction_range.symm).trans
    (MonoidHom.ofInjective affineAction_injective).symm

theorem cycle_pow_five : cycle ^ 5 = 1 := by
  apply LinearEquiv.ext
  intro v
  revert v
  decide +kernel

theorem cycle_ne_one : cycle ≠ 1 := by
  intro h
  have hmoved : cycle firstVector ≠ firstVector := by decide +kernel
  apply hmoved
  rw [h]
  rfl

theorem cycle_orderOf : orderOf cycle = 5 := by
  letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact orderOf_eq_prime cycle_pow_five cycle_ne_one

theorem linearGroup_eq_zpowers : linearGroup = Subgroup.zpowers cycle := by
  have hgen : Set.range linearGenerators = {cycle} := by
    ext g
    simp [linearGenerators, eq_comm]
  change Subgroup.closure (Set.range linearGenerators) = _
  rw [hgen, ← Subgroup.zpowers_eq_closure]

theorem linearGroup_card : Nat.card linearGroup = 5 := by
  rw [linearGroup_eq_zpowers, Nat.card_zpowers, cycle_orderOf]

theorem linearGroup_isSimpleGroup : IsSimpleGroup linearGroup := by
  letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact isSimpleGroup_of_prime_card linearGroup_card

theorem linear_normal_total (A B : Subgroup linearGroup)
    (hA : A.Normal) (_hB : B.Normal) : A ≤ B ∨ B ≤ A := by
  letI : IsSimpleGroup linearGroup := linearGroup_isSimpleGroup
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal A hA with h | h
  · left
    rw [h]
    exact bot_le
  · right
    rw [h]
    exact le_top

/-- Transport the affine normal-chain theorem along the actual action map. -/
theorem top_normal_total (A B : Subgroup Top)
    (hA : A.Normal) (hB : B.Normal) : A ≤ B ∨ B ≤ A :=
  normalSubgroups_total_of_surjective modelEquiv.symm.toMonoidHom
    modelEquiv.symm.surjective
    (AffineModel.normal_total_of_irreducible_complement
      linearGroup irreducible linear_normal_total) A B hA hB

/-- Every actual normal quotient has a normally cyclic socle. -/
theorem topSocle_one (N : {N : Subgroup Top // N.Normal}) :
    SocleNormalGeneratorBound (Top ⧸ N.1) 1 := by
  letI := N.2
  exact quotientSocleNormalGeneratorBound_one_of_normal_total top_normal_total N.1

/-- The two-position interface for the unchanged row-one top. -/
theorem topSocle (N : {N : Subgroup Top // N.Normal}) :
    SocleNormalGeneratorBound (Top ⧸ N.1) 2 :=
  (topSocle_one N).mono (by decide)

noncomputable def family :
    DegreeTwoPrimitiveSixteenInterfaces.row1.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  Non2UnipotentPrefixFiniteMenu.FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    DegreeTwoPrimitiveSixteenInterfaces.row1.normalRegistry topSocle

end PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles
end SymmetricSubgroupAsymptotics

end
