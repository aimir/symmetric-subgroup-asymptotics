import SymmetricSubgroupAsymptotics.DegreeTwelveNineTranslations
import SymmetricSubgroupAsymptotics.OriginalKernelArbitraryNormalQuotient

/-!
# An intrinsic binary-base owner with the whole nine-translation quotient

The witness retains the actual normal binary core, its literal whole
quotient, and the nine distinct supported permutations of the original
point type. The quotient acts faithfully and transitively on these ambient
translations by the original conjugation action. Neither a full V4 cubed
base nor an elementary ternary complement is assumed.

The original elementary binary kernel constructs its own F2 module chart.
Every original normal subgroup N then has the exact descended extension
G/N → G/(base ⊔ N), using OriginalKernelArbitraryNormalQuotient. In particular
N is not assumed to lie in the binary base.

This is a structural owner predicate, not a counting or physical coverage
theorem. No cyclicity of a correlated submodule is inferred merely from
transitivity of the ambient nine labels.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- Minimal original-action data for the binary-base/nine-top branch.
The nine translations are ambient permutations and need not lie in `base`. -/
structure C1BinaryNineTopOwnerWitness (G Ω : Type) [Group G] [MulAction G Ω] where
  base : Subgroup G
  [base_normal : base.Normal]
  [base_finite : Finite base]
  base_exponent_two : ∀ x : base, x ^ 2 = 1
  base_card_le : Nat.card base ≤ 64
  quotient_three_group : IsPGroup 3 (G ⧸ base)
  Label : Type
  label_card : Nat.card Label = 9
  translation : Label → Equiv.Perm Ω
  translation_injective : Function.Injective translation
  action : (G ⧸ base) →* Equiv.Perm Label
  action_injective : Function.Injective action
  action_transitive : ∀ s t, ∃ q : G ⧸ base, action q s = t
  conjugation : ∀ (g : G) (s : Label),
    translation (action (QuotientGroup.mk' base g) s) =
      MulAction.toPermHom G Ω g * translation s * (MulAction.toPermHom G Ω g)⁻¹

attribute [instance] C1BinaryNineTopOwnerWitness.base_normal
attribute [instance] C1BinaryNineTopOwnerWitness.base_finite

def IsC1BinaryNineTopOwner (G Ω : Type) [Group G] [MulAction G Ω] : Prop :=
  Nonempty (C1BinaryNineTopOwnerWitness G Ω)

namespace C1BinaryNineTopOwnerWitness

variable {G Ω : Type} [Group G] [MulAction G Ω]
    (W : C1BinaryNineTopOwnerWitness G Ω)

/-- The entire original quotient, as opposed to its action on three blocks. -/
abbrev projection : G →* G ⧸ W.base := QuotientGroup.mk' W.base

theorem projection_surjective : Function.Surjective W.projection :=
  QuotientGroup.mk'_surjective W.base

@[simp] theorem projection_ker : W.projection.ker = W.base :=
  QuotientGroup.ker_mk' W.base

theorem base_isPGroup : IsPGroup 2 W.base := by
  intro w
  exact ⟨1, by simpa only [pow_one] using W.base_exponent_two w⟩

/-- Exponent two makes the actual base abelian. The group law is unchanged. -/
abbrev baseCommGroup : CommGroup W.base := {
  (inferInstance : Group W.base) with
  mul_comm := fun a b =>
    (Commute.of_orderOf_dvd_two
      (fun x : W.base => orderOf_dvd_of_pow_eq_one (W.base_exponent_two x)) a b).eq }

attribute [local instance] baseCommGroup

/-- Intrinsic additive coordinates on the correlated original base. -/
abbrev BaseVector := Additive W.base

abbrev baseVectorModule : Module (ZMod 2) W.BaseVector :=
  AddCommGroup.zmodModule (n := 2) (by
    intro v
    apply Additive.toMul.injective
    change v.toMul ^ 2 = 1
    exact W.base_exponent_two v.toMul)

attribute [local instance] baseVectorModule

/-- The original base, with only the additive/multiplicative type tags changed. -/
def baseCoordinates : W.base →* Multiplicative W.BaseVector :=
  (MulEquiv.multiplicativeAdditive W.base).symm.toMonoidHom

theorem baseCoordinates_surjective : Function.Surjective W.baseCoordinates :=
  (MulEquiv.multiplicativeAdditive W.base).symm.surjective

theorem baseCoordinates_ker : W.baseCoordinates.ker = (⊥ : Subgroup G).subgroupOf W.base := by
  rw [Subgroup.bot_subgroupOf]
  exact (MonoidHom.ker_eq_bot_iff _).mpr
    (MulEquiv.multiplicativeAdditive W.base).symm.injective

/-- The actual conjugation representation of G, before quotienting the
acting group. Its construction does not require a complement. -/
def baseAmbientRepresentation : Representation (ZMod 2) G W.BaseVector :=
  normalSectionRepresentation W.base ⊥ W.baseCoordinates
    W.baseCoordinates_surjective W.baseCoordinates_ker

theorem baseAmbientRepresentation_trivial (g : W.base) (v : W.BaseVector) :
    W.baseAmbientRepresentation (g : G) v = v :=
  normalSectionRepresentation_trivial_K W.base ⊥ W.baseCoordinates
    W.baseCoordinates_surjective W.baseCoordinates_ker g v

/-- Conjugation factors through the whole original quotient G/base. -/
def baseRepresentation : Rep (ZMod 2) (G ⧸ W.base) :=
  Rep.of (QuotientGroup.lift W.base W.baseAmbientRepresentation (by
    intro g hg
    apply MonoidHom.mem_ker.mpr
    apply LinearMap.ext
    intro v
    exact W.baseAmbientRepresentation_trivial ⟨g, hg⟩ v))

@[simp] theorem baseRepresentation_apply (g : G) (k : W.base) :
    W.baseRepresentation.ρ (W.projection g) (Additive.ofMul k) =
      Additive.ofMul (MulAut.conjNormal g k) :=
  normalSectionRepresentation_apply W.base ⊥ W.baseCoordinates
    W.baseCoordinates_surjective W.baseCoordinates_ker g k

/-- A base element is the same original group element in the kernel of the
actual quotient map. -/
def projectionKernelEquiv : W.base ≃* W.projection.ker :=
  MulEquiv.subgroupCongr W.projection_ker.symm

@[simp] theorem projectionKernelEquiv_coe (k : W.base) :
    (W.projectionKernelEquiv k : G) = (k : G) := rfl

/-- Exact intrinsic chart on the original binary kernel. It is derived
from the witness and is not an extra module-capacity or splitting premise. -/
def originalKernelChart : OriginalKernelModuleChart W.projection W.baseRepresentation where
  equiv := (MulEquiv.multiplicativeAdditive W.base).trans W.projectionKernelEquiv
  conjugate g v := by
    let toBase : W.BaseVector ≃ W.base := Additive.toMul
    change (toBase (W.baseRepresentation.ρ (W.projection g) v) : G) =
      g * (toBase v : G) * g⁻¹
    exact congrArg (fun z : W.BaseVector => (toBase z : G))
      (W.baseRepresentation_apply g (toBase v))

/-- The exact original additive kernel, without loss of correlations. -/
theorem baseRepresentation_card : Nat.card W.baseRepresentation = Nat.card W.base :=
  Nat.card_congr (Additive.toMul : Additive W.base ≃ W.base)

theorem baseRepresentation_card_le : Nat.card W.baseRepresentation ≤ 64 :=
  W.baseRepresentation_card.trans_le W.base_card_le

section AllNormalAxes

variable (N : Subgroup G) [N.Normal]

/-- The literal original quotient extension. The kernel used in its target
is the exact kernel of projection, proved equal to the original base. -/
abbrev axisProjection := OriginalKernelModuleChart.base W.projection N

omit [N.Normal] in
@[simp] theorem axisTop_subgroup : W.projection.ker ⊔ N = W.base ⊔ N := by
  rw [W.projection_ker]

theorem axisProjection_surjective : Function.Surjective (W.axisProjection N) :=
  OriginalKernelModuleChart.base_surjective W.projection N

/-- The all-normal acting top is an actual quotient of the original whole
nine-translation group, even when N has nontrivial top image. -/
def axisWholeTopMap : (G ⧸ W.base) →* G ⧸ (W.projection.ker ⊔ N) :=
  QuotientGroup.lift W.base (QuotientGroup.mk' (W.projection.ker ⊔ N)) (by
    rw [QuotientGroup.ker_mk', W.projection_ker]
    exact le_sup_left)

theorem axisWholeTopMap_surjective : Function.Surjective (W.axisWholeTopMap N) := by
  intro b
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (W.projection.ker ⊔ N) b
  exact ⟨QuotientGroup.mk' W.base g, rfl⟩

theorem axisTop_isPGroup : IsPGroup 3 (G ⧸ (W.projection.ker ⊔ N)) :=
  W.quotient_three_group.of_surjective (W.axisWholeTopMap N)
    (W.axisWholeTopMap_surjective N)

/-- The original base modulo precisely its intersection with N. -/
abbrev axisRepresentation :=
  W.originalKernelChart.sectionRepresentation W.projection W.baseRepresentation N

/-- All original N are included; N may have a nontrivial whole-top image. -/
def axisChart : OriginalKernelModuleChart (W.axisProjection N) (W.axisRepresentation N) :=
  W.originalKernelChart.quotientChart W.projection W.baseRepresentation N

/-- The section map starts on the same original correlated binary base. -/
def axisBaseMap : W.base →* Multiplicative (W.axisRepresentation N) :=
  (W.originalKernelChart.sectionMap W.projection W.baseRepresentation N).comp
    W.projectionKernelEquiv.toMonoidHom

theorem axisBaseMap_surjective : Function.Surjective (W.axisBaseMap N) :=
  (W.originalKernelChart.sectionMap_surjective W.projection W.baseRepresentation N).comp
    W.projectionKernelEquiv.surjective

/-- The section denominator is exactly membership in the original N. -/
theorem axisBaseMap_ker : (W.axisBaseMap N).ker = N.subgroupOf W.base := by
  ext k
  change W.projectionKernelEquiv k ∈
    (W.originalKernelChart.sectionMap W.projection W.baseRepresentation N).ker ↔
      (k : G) ∈ N
  rw [W.originalKernelChart.sectionMap_ker W.projection W.baseRepresentation N]
  rfl

@[simp] theorem axisProjection_apply (g : G) :
    W.axisProjection N (QuotientGroup.mk' N g) =
      QuotientGroup.mk' (W.projection.ker ⊔ N) g := rfl

/-- The all-normal chart reconstructs the original quotient representative,
not a substitute lift in an abstract extension. -/
theorem axisChart_original (k : W.base) :
    (W.axisChart N).equiv (W.axisBaseMap N k) =
      OriginalKernelModuleChart.quotientKernelMap W.projection N (W.projectionKernelEquiv k) :=
  W.originalKernelChart.kernelEquiv_apply W.projection W.baseRepresentation N
    (W.projectionKernelEquiv k)

end AllNormalAxes

end C1BinaryNineTopOwnerWitness

namespace OriginalMinimalBlock

variable {A Ω : Type} [Group A] [Finite A] [Finite Ω] [MulAction A Ω]
    [FaithfulSMul A Ω] [MulAction.IsPretransitive A Ω]
    {ω₀ : Ω} (D : OriginalMinimalBlock (A := A) ω₀)

/-- Install the intrinsic owner directly from the checked saturated original
four-by-three theorem, retaining the original core and whole quotient. -/
def fourByThree_nineTopOwnerWitness
    (N : Subgroup A) [N.Normal] (c : ActualChiefSeries D.Component)
    (hPoints : Nat.card D.Points = 3) (hTopOrder : Nat.card D.Top = 3)
    (hWeight : actualChiefSeriesTernaryWeight c = 1)
    (hTop : Module.finrank (ZMod 3)
      (primeRelativeCharacters 3 (originalNormalRange D.topMap N)) = 1)
    (hRank : Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) = 2)
    (e : ∀ x : D.Points, Fin 4 ≃ originalBlockFibre D.map x) :
    C1BinaryNineTopOwnerWitness A Ω := by
  let hEven := D.fourByThree_allEven N c hPoints hTopOrder hWeight hTop hRank e
  let ρ := DegreeTwelveFourBlockCore.alternatingCoordinates D.map D.map_equivariant e hEven
  let hρ := DegreeTwelveFourBlockCore.alternatingCoordinates_injective D.map D.map_equivariant e hEven
  have hNine := D.fourByThree_nineTranslationQuotient N c hPoints hTopOrder hWeight hTop hRank e
  refine {
    base := DegreeTwelveNineTranslations.originalCore D.map D.map_equivariant e hEven
    base_normal := inferInstance
    base_finite := inferInstance
    base_exponent_two := DegreeTwelveFourBlockCore.core_exponent_two D.topMap ρ hρ
    base_card_le := ?_
    quotient_three_group := hNine.1
    Label := DegreeTwelveNineTranslations.Translations (X := D.Points)
    label_card := hNine.2.1
    translation := DegreeTwelveNineTranslations.originalLocalPermutation D.map e
    translation_injective := DegreeTwelveNineTranslations.originalLocalPermutation_injective D.map e
    action := DegreeTwelveNineTranslations.quotientAction D.map D.map_equivariant e hEven
    action_injective := hNine.2.2.1
    action_transitive := hNine.2.2.2
    conjugation := fun a s => ?_ }
  · have h := DegreeTwelveFourBlockCore.core_card_le D.topMap ρ hρ
    simpa only [hPoints] using h
  · exact DegreeTwelveNineTranslations.originalLocalPermutation_conjugation D.map D.map_equivariant e a s

/-- Structural owner installation; no final counting premise is introduced. -/
theorem fourByThree_nineTopOwner
    (N : Subgroup A) [N.Normal] (c : ActualChiefSeries D.Component)
    (hPoints : Nat.card D.Points = 3) (hTopOrder : Nat.card D.Top = 3)
    (hWeight : actualChiefSeriesTernaryWeight c = 1)
    (hTop : Module.finrank (ZMod 3)
      (primeRelativeCharacters 3 (originalNormalRange D.topMap N)) = 1)
    (hRank : Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) = 2)
    (e : ∀ x : D.Points, Fin 4 ≃ originalBlockFibre D.map x) :
    IsC1BinaryNineTopOwner A Ω :=
  ⟨D.fourByThree_nineTopOwnerWitness N c hPoints hTopOrder hWeight hTop hRank e⟩

end OriginalMinimalBlock
end SymmetricSubgroupAsymptotics
