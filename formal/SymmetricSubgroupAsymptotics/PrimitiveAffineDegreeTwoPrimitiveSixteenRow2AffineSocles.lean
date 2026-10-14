import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles
import SymmetricSubgroupAsymptotics.DihedralFiveNormalChain

/-!
# The literal primitive-sixteen row two as an irreducible affine group

A cyclic rotation of the four binary coordinates identifies the retained
order-five generator with the cycle used for row one. The extra retained
linear generator is an involution inverting that cycle. Its generated
linear group is the image of the dihedral group of order ten, whose normal
chain was proved algebraically. Irreducibility follows from inclusion of
the actual row-one cyclic linear group in these coordinates.

All permutation comparisons retain the three original row-two generators.
The resulting socle bounds quantify over the original top's actual normal
subgroups and their literal quotients.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoPrimitiveSixteenRow2AffineSocles

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

abbrev Vector := AffineModel.V 2 4
abbrev LinearGroup := AffineModel.GLV 2 4
abbrev Top := DegreeTwoPrimitiveSixteenInterfaces.row2.top
abbrev cycle : LinearGroup := PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.cycle

/-- The bit rotation maps the row-one linear chart to the row-two chart. -/
def chartRotation : LinearGroup where
  toFun v := ![v 3, v 0, v 1, v 2]
  invFun v := ![v 1, v 2, v 3, v 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_add' := by decide +kernel
  map_smul' := by decide +kernel

def pointEquiv : Vector ≃ Fin 16 :=
  chartRotation.toEquiv.trans PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.pointEquiv

/-- The actual second linear generator, after the displayed bit rotation. -/
def flip : LinearGroup where
  toFun v := ![v 0, v 0 + v 3, v 0 + v 2, v 0 + v 1]
  invFun v := ![v 0, v 0 + v 3, v 0 + v 2, v 0 + v 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_add' := by decide +kernel
  map_smul' := by decide +kernel

def firstVector : Vector := binaryVectorOfMask 4 8

def linearPerm : LinearGroup →* Equiv.Perm (Fin 16) :=
  pointEquiv.permCongrHom.toMonoidHom.comp
    PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.linearAction

def translationPerm : Multiplicative Vector →* Equiv.Perm (Fin 16) :=
  pointEquiv.permCongrHom.toMonoidHom.comp AffineModel.transl

theorem linearPerm_cycle :
    linearPerm cycle = DegreeTwoPrimitiveSixteenInterfaces.row2Generators 0 := by
  ext x
  revert x
  decide +kernel

theorem linearPerm_flip :
    linearPerm flip = DegreeTwoPrimitiveSixteenInterfaces.row2Generators 1 := by
  ext x
  revert x
  decide +kernel

theorem translationPerm_firstVector :
    translationPerm (Multiplicative.ofAdd firstVector) =
      DegreeTwoPrimitiveSixteenInterfaces.row2Generators 2 := by
  ext x
  revert x
  decide +kernel

def linearGenerators : Fin 2 → LinearGroup := ![cycle, flip]
abbrev linearGroup : Subgroup LinearGroup := Subgroup.closure (Set.range linearGenerators)

theorem cycle_mem : cycle ∈ linearGroup := Subgroup.subset_closure ⟨0, rfl⟩
theorem flip_mem : flip ∈ linearGroup := Subgroup.subset_closure ⟨1, rfl⟩

/-- The checked cyclic row-one representation is literally a subgroup. -/
theorem cyclic_le :
    PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.linearGroup ≤ linearGroup := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  exact cycle_mem

theorem irreducible : AffineModel.Irreducible linearGroup := by
  intro S hS
  exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.irreducible S
    (fun r hr x hx ↦ hS r (cyclic_le hr) x hx)

private def translationExponent : Fin 4 → ℕ := ![3, 2, 1, 0]

def translationFactor (v : Vector) (i : Fin 4) : Equiv.Perm (Fin 16) :=
  if v i = 0 then 1 else
    DegreeTwoPrimitiveSixteenInterfaces.row2Generators 0 ^ translationExponent i *
      DegreeTwoPrimitiveSixteenInterfaces.row2Generators 2 *
      (DegreeTwoPrimitiveSixteenInterfaces.row2Generators 0 ^ translationExponent i)⁻¹

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
  have ha : DegreeTwoPrimitiveSixteenInterfaces.row2Generators 0 ∈ Top :=
    Subgroup.subset_closure (Set.mem_range_self 0)
  have ht : DegreeTwoPrimitiveSixteenInterfaces.row2Generators 2 ∈ Top :=
    Subgroup.subset_closure (Set.mem_range_self 2)
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
    fin_cases i
    · change linearPerm cycle ∈ Top
      rw [linearPerm_cycle]
      exact Subgroup.subset_closure (Set.mem_range_self 0)
    · change linearPerm flip ∈ Top
      rw [linearPerm_flip]
      exact Subgroup.subset_closure (Set.mem_range_self 1)
  | one => simpa only [map_one] using Top.one_mem
  | mul r s _ _ hr hs => simpa only [map_mul] using Top.mul_mem hr hs
  | inv r _ hr => simpa only [map_inv] using Top.inv_mem hr

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
    · exact ⟨SemidirectProduct.inr (⟨flip, flip_mem⟩ : linearGroup),
        (affineAction_inr _).trans linearPerm_flip⟩
    · exact ⟨SemidirectProduct.inl (Multiplicative.ofAdd firstVector),
        (affineAction_inl _).trans translationPerm_firstVector⟩

def modelEquiv : Top ≃* AffineModel.Aff linearGroup :=
  (MulEquiv.subgroupCongr affineAction_range.symm).trans
    (MonoidHom.ofInjective affineAction_injective).symm

/-- The standard dihedral presentation acts through the two actual linear
generators. Its four multiplication formulas reduce on two five-valued
exponents and the four-bit vectors, not on a subgroup registry. -/
def dihedralAction : DihedralGroup 5 →* LinearGroup where
  toFun
    | .r i => cycle ^ i.val
    | .sr i => flip * cycle ^ i.val
  map_one' := rfl
  map_mul' := by
    rintro (i | i) (j | j) <;> apply LinearEquiv.ext <;> intro v
    all_goals
      revert i j v
      decide +kernel

theorem dihedralAction_rotation : dihedralAction (.r 1) = cycle := by
  change cycle ^ (1 : ZMod 5).val = cycle
  letI : Fact (1 < (5 : ℕ)) := ⟨by decide⟩
  rw [ZMod.val_one, pow_one]

theorem dihedralAction_reflection : dihedralAction (.sr 0) = flip := by
  change flip * cycle ^ (0 : ZMod 5).val = flip
  norm_num

theorem dihedralAction_range : dihedralAction.range = linearGroup := by
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    cases g with
    | r i => exact linearGroup.pow_mem cycle_mem i.val
    | sr i => exact linearGroup.mul_mem flip_mem (linearGroup.pow_mem cycle_mem i.val)
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact ⟨.r 1, dihedralAction_rotation⟩
    · exact ⟨.sr 0, dihedralAction_reflection⟩

def complementMap : DihedralGroup 5 →* linearGroup :=
  (MulEquiv.subgroupCongr dihedralAction_range).toMonoidHom.comp
    dihedralAction.rangeRestrict

theorem complementMap_surjective : Function.Surjective complementMap :=
  (MulEquiv.subgroupCongr dihedralAction_range).surjective.comp
    dihedralAction.rangeRestrict_surjective

theorem linear_normal_total (A B : Subgroup linearGroup)
    (hA : A.Normal) (hB : B.Normal) : A ≤ B ∨ B ≤ A :=
  normalSubgroups_total_of_surjective complementMap complementMap_surjective
    DihedralFiveNormalChain.normal_total A B hA hB

theorem top_normal_total (A B : Subgroup Top)
    (hA : A.Normal) (hB : B.Normal) : A ≤ B ∨ B ≤ A :=
  normalSubgroups_total_of_surjective modelEquiv.symm.toMonoidHom
    modelEquiv.symm.surjective
    (AffineModel.normal_total_of_irreducible_complement
      linearGroup irreducible linear_normal_total) A B hA hB

theorem topSocle_one (N : {N : Subgroup Top // N.Normal}) :
    SocleNormalGeneratorBound (Top ⧸ N.1) 1 := by
  letI := N.2
  exact quotientSocleNormalGeneratorBound_one_of_normal_total top_normal_total N.1

theorem topSocle (N : {N : Subgroup Top // N.Normal}) :
    SocleNormalGeneratorBound (Top ⧸ N.1) 2 :=
  (topSocle_one N).mono (by decide)

noncomputable def family :
    DegreeTwoPrimitiveSixteenInterfaces.row2.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  Non2UnipotentPrefixFiniteMenu.FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    DegreeTwoPrimitiveSixteenInterfaces.row2.normalRegistry topSocle

end PrimitiveAffineDegreeTwoPrimitiveSixteenRow2AffineSocles
end SymmetricSubgroupAsymptotics

end
