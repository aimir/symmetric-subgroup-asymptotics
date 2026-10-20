import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles
import SymmetricSubgroupAsymptotics.F20NormalChain

/-!
# The literal primitive-sixteen row five and its F20 complement

The first and third retained permutations are exactly the row-one cycle
and translation. The additional linear map conjugates that cycle to its
square. An explicit homomorphism from the scalar-coordinate F20 model has
range equal to this actual generated linear group. Its algebraic normal
chain descends through that map. The irreducibility and all translations
are inherited through the literal inclusion of row one's generators.

The resulting bounds quantify over the unchanged row-five top's actual
normal subgroups and literal quotients. No census hypothesis is used.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoPrimitiveSixteenRow5AffineSocles

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

abbrev Vector := AffineModel.V 2 4
abbrev LinearGroup := AffineModel.GLV 2 4
abbrev Top := DegreeTwoPrimitiveSixteenInterfaces.row5.top
abbrev cycle : LinearGroup := PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.cycle
abbrev pointEquiv := PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.pointEquiv
abbrev linearPerm := PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.linearPerm
abbrev translationPerm := PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.translationPerm
abbrev firstVector := PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.firstVector

/-- The extra original linear generator in the unchanged bit-mask chart. -/
def quartic : LinearGroup where
  toFun v := ![v 1, v 1 + v 2, v 0 + v 1, v 1 + v 3]
  invFun v := ![v 0 + v 2, v 0, v 0 + v 1, v 0 + v 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_add' := by decide +kernel
  map_smul' := by decide +kernel

theorem linearPerm_cycle :
    linearPerm cycle = DegreeTwoPrimitiveSixteenInterfaces.row5Generators 0 :=
  PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.linearPerm_cycle

theorem linearPerm_quartic :
    linearPerm quartic = DegreeTwoPrimitiveSixteenInterfaces.row5Generators 1 := by
  ext x
  revert x
  decide +kernel

theorem translationPerm_firstVector :
    translationPerm (Multiplicative.ofAdd firstVector) =
      DegreeTwoPrimitiveSixteenInterfaces.row5Generators 2 :=
  PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.translationPerm_firstVector

def linearGenerators : Fin 2 → LinearGroup := ![cycle, quartic]
abbrev linearGroup : Subgroup LinearGroup := Subgroup.closure (Set.range linearGenerators)

theorem cycle_mem : cycle ∈ linearGroup := Subgroup.subset_closure ⟨0, rfl⟩
theorem quartic_mem : quartic ∈ linearGroup := Subgroup.subset_closure ⟨1, rfl⟩

theorem cyclic_le :
    PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.linearGroup ≤ linearGroup := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  exact cycle_mem

theorem irreducible : AffineModel.Irreducible linearGroup := by
  intro S hS
  exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.irreducible S
    (fun r hr x hx ↦ hS r (cyclic_le hr) x hx)

/-- Inclusion uses the exact retained first and third permutations. -/
theorem row1_le_top : PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.Top ≤ Top := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact Subgroup.subset_closure ⟨0, rfl⟩
  · exact Subgroup.subset_closure ⟨2, rfl⟩

theorem translation_mem (v : Multiplicative Vector) : translationPerm v ∈ Top :=
  row1_le_top (PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.translation_mem v)

theorem linearPerm_mem {r : LinearGroup} (hr : r ∈ linearGroup) :
    linearPerm r ∈ Top := by
  induction hr using Subgroup.closure_induction with
  | mem r hr =>
    obtain ⟨i, rfl⟩ := hr
    fin_cases i
    · change linearPerm cycle ∈ Top
      rw [linearPerm_cycle]
      exact Subgroup.subset_closure (Set.mem_range_self 0)
    · change linearPerm quartic ∈ Top
      rw [linearPerm_quartic]
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
    · exact ⟨SemidirectProduct.inr (⟨quartic, quartic_mem⟩ : linearGroup),
        (affineAction_inr _).trans linearPerm_quartic⟩
    · exact ⟨SemidirectProduct.inl (Multiplicative.ofAdd firstVector),
        (affineAction_inl _).trans translationPerm_firstVector⟩

def modelEquiv : Top ≃* AffineModel.Aff linearGroup :=
  (MulEquiv.subgroupCongr affineAction_range.symm).trans
    (MonoidHom.ofInjective affineAction_injective).symm

/-- Translation exponent in the prime-order cyclic subgroup. -/
def rotationMap : Multiplicative (AffineModel.V 5 1) →* LinearGroup where
  toFun v := cycle ^ (v.toAdd 0).val
  map_one' := rfl
  map_mul' := by
    intro v w
    apply LinearEquiv.ext
    intro x
    revert v w x
    decide +kernel

/-- The four scalar units are powers 0,1,3,2 of the scalar two. -/
def scalarExponent (u : (ZMod 5)ˣ) : ℕ :=
  (#[0, 0, 1, 3, 2] : Array ℕ)[(u : ZMod 5).val]!

def scalarMap : (ZMod 5)ˣ →* LinearGroup where
  toFun u := quartic ^ scalarExponent u
  map_one' := rfl
  map_mul' := by
    intro u v
    apply LinearEquiv.ext
    intro x
    revert u v x
    decide +kernel

/-- The compatibility check is precisely the original scalar action on the
five-element translation group; no normal-state information enters it. -/
def frobeniusAction : F20.ScalarModel →* LinearGroup :=
  SemidirectProduct.lift rotationMap scalarMap (by
    intro u
    apply MonoidHom.ext
    intro v
    apply LinearEquiv.ext
    intro x
    revert u v x
    decide +kernel)

def twoUnit : (ZMod 5)ˣ := Units.mk0 (2 : ZMod 5) (by decide +kernel)

theorem rotationMap_e0 : rotationMap (Multiplicative.ofAdd F20.e0) = cycle := by
  apply LinearEquiv.ext
  intro x
  revert x
  decide +kernel

theorem scalarMap_twoUnit : scalarMap twoUnit = quartic := by
  apply LinearEquiv.ext
  intro x
  revert x
  decide +kernel

theorem frobeniusAction_range : frobeniusAction.range = linearGroup := by
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    change rotationMap g.left * scalarMap g.right ∈ linearGroup
    exact linearGroup.mul_mem
      (linearGroup.pow_mem cycle_mem _) (linearGroup.pow_mem quartic_mem _)
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · refine ⟨SemidirectProduct.inl (Multiplicative.ofAdd F20.e0), ?_⟩
      rw [frobeniusAction, SemidirectProduct.lift_inl]
      exact rotationMap_e0
    · refine ⟨SemidirectProduct.inr twoUnit, ?_⟩
      rw [frobeniusAction, SemidirectProduct.lift_inr]
      exact scalarMap_twoUnit

/-- The actual row-five complement is the range of this displayed map. -/
def complementMap : F20.ScalarModel →* linearGroup :=
  (MulEquiv.subgroupCongr frobeniusAction_range).toMonoidHom.comp
    frobeniusAction.rangeRestrict

theorem complementMap_surjective : Function.Surjective complementMap :=
  (MulEquiv.subgroupCongr frobeniusAction_range).surjective.comp
    frobeniusAction.rangeRestrict_surjective

theorem linear_normal_total (A B : Subgroup linearGroup)
    (hA : A.Normal) (hB : B.Normal) : A ≤ B ∨ B ≤ A :=
  normalSubgroups_total_of_surjective complementMap complementMap_surjective
    F20.scalarModel_normal_total A B hA hB

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
    DegreeTwoPrimitiveSixteenInterfaces.row5.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  Non2UnipotentPrefixFiniteMenu.FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    DegreeTwoPrimitiveSixteenInterfaces.row5.normalRegistry topSocle

end PrimitiveAffineDegreeTwoPrimitiveSixteenRow5AffineSocles
end SymmetricSubgroupAsymptotics

end
