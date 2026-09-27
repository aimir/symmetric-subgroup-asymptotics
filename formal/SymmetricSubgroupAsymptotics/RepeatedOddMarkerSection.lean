import SymmetricSubgroupAsymptotics.RepeatedOddMarkerImage
import SymmetricSubgroupAsymptotics.CocycleLifts
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# A literal section of the original repeated-marker contraction

The nontrivial sign is represented by the fixed original transposition
(0 1) on Fin 3. The exterior coordinate is carried by the identity map
on D, not replaced by its identity element.

Restricting this section to an actual image B gives a section inside the
whole original preimage of B. It need not lie in an individual original
subgroup H with image B. Quotienting that preimage by any normal subgroup
of its projection kernel retains an explicit original origin section.
There are no finiteness, independent-marker, or physical-count premises.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.RepeatedOddMarkerSection

open RepeatedOddMarkerKernel

/-- The fixed original transposition representing the nontrivial sign. -/
def transposition : OddMarkerGroup := Equiv.swap (0 : Fin 3) 1

def signSection : Multiplicative (ZMod 2) →* OddMarkerGroup where
  toFun s := if s = 1 then 1 else transposition
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

@[simp] theorem signSection_nontrivial :
    signSection (Multiplicative.ofAdd (1 : ZMod 2)) = transposition := by decide +kernel

/-- Two original sign values, checked on the three original points. -/
theorem signSection_rightInverse : Function.RightInverse signSection oddMarkerSign := by
  decide +kernel

@[simp] theorem sign_signSection (s : Multiplicative (ZMod 2)) :
    oddMarkerSign (signSection s) = s := signSection_rightInverse s

variable {ι D : Type*} [Group D]

/-- The actual exterior is retained unchanged. -/
def ambientSection : ((ι → Multiplicative (ZMod 2)) × D) →*
    ((ι → OddMarkerGroup) × D) where
  toFun b := (fun i => signSection (b.1 i), b.2)
  map_one' := by
    apply Prod.ext
    · funext i
      exact signSection.map_one
    · rfl
  map_mul' b c := by
    apply Prod.ext
    · funext i
      exact signSection.map_mul (b.1 i) (c.1 i)
    · rfl

@[simp] theorem ambientSection_coordinate (b : (ι → Multiplicative (ZMod 2)) × D)
    (i : ι) : (ambientSection b).1 i = signSection (b.1 i) := rfl

@[simp] theorem ambientSection_exterior (b : (ι → Multiplicative (ZMod 2)) × D) :
    (ambientSection b).2 = b.2 := rfl

@[simp] theorem contraction_ambientSection (b : (ι → Multiplicative (ZMod 2)) × D) :
    contraction (ambientSection b) = b := by
  apply Prod.ext
  · funext i
    exact sign_signSection (b.1 i)
  · rfl

theorem contraction_comp_ambientSection :
    contraction.comp (ambientSection (ι := ι) (D := D)) = MonoidHom.id _ := by
  apply MonoidHom.ext
  exact contraction_ambientSection

theorem ambientSection_injective :
    Function.Injective (ambientSection (ι := ι) (D := D)) :=
  (show Function.LeftInverse contraction ambientSection from contraction_ambientSection).injective

theorem contraction_surjective :
    Function.Surjective (contraction (ι := ι) (D := D)) :=
  fun b => ⟨ambientSection b, contraction_ambientSection b⟩

/-- The whole original preimage of the specified literal image B. -/
def pullback (B : Subgroup ((ι → Multiplicative (ZMod 2)) × D)) :
    Subgroup ((ι → OddMarkerGroup) × D) := B.comap contraction

def pullbackProjection (B : Subgroup ((ι → Multiplicative (ZMod 2)) × D)) :
    pullback B →* B :=
  (contraction.comp (pullback B).subtype).codRestrict B (fun x => x.2)

def pullbackSection (B : Subgroup ((ι → Multiplicative (ZMod 2)) × D)) :
    B →* pullback B :=
  (ambientSection.comp B.subtype).codRestrict (pullback B) (fun b => by
    change contraction (ambientSection b.1) ∈ B
    rw [contraction_ambientSection]
    exact b.2)

@[simp] theorem pullbackSection_coe (B : Subgroup ((ι → Multiplicative (ZMod 2)) × D))
    (b : B) : (pullbackSection B b : (ι → OddMarkerGroup) × D) = ambientSection b.1 := rfl

@[simp] theorem pullbackProjection_section
    (B : Subgroup ((ι → Multiplicative (ZMod 2)) × D)) (b : B) :
    pullbackProjection B (pullbackSection B b) = b :=
  Subtype.ext (contraction_ambientSection b.1)

theorem pullbackProjection_comp_section (B : Subgroup ((ι → Multiplicative (ZMod 2)) × D)) :
    (pullbackProjection B).comp (pullbackSection B) = MonoidHom.id B := by
  apply MonoidHom.ext
  exact pullbackProjection_section B

theorem pullbackProjection_surjective (B : Subgroup ((ι → Multiplicative (ZMod 2)) × D)) :
    Function.Surjective (pullbackProjection B) :=
  fun b => ⟨pullbackSection B b, pullbackProjection_section B b⟩

/-- An actual section in the original pullback, ready for the exact
section-subgroup/cocycle classification. -/
def pullbackSectionLift (B : Subgroup ((ι → Multiplicative (ZMod 2)) × D)) :
    HomomorphicLift (pullbackProjection B) (MonoidHom.id B) :=
  ⟨pullbackSection B, pullbackProjection_comp_section B⟩

/-- The original H maps into its full image pullback. This inclusion does
not assert that the chosen transpositions belong to H. -/
def originalInclusion (H : Subgroup ((ι → OddMarkerGroup) × D)) :
    H →* pullback (RepeatedOddMarkerImage.image H) :=
  Subgroup.inclusion (by
    intro x hx
    exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)

theorem projection_comp_originalInclusion (H : Subgroup ((ι → OddMarkerGroup) × D)) :
    (pullbackProjection (RepeatedOddMarkerImage.image H)).comp (originalInclusion H) =
      RepeatedOddMarkerImage.quotientMap H := rfl

/-- Every normal quotient by part of the literal projection kernel has
the actual induced section. No complement of the ternary submodule is
chosen and no existence-of-lifts premise is needed. -/
def quotientSectionLift (B : Subgroup ((ι → Multiplicative (ZMod 2)) × D))
    (N : Subgroup (pullback B)) [N.Normal] (hN : N ≤ (pullbackProjection B).ker) :
    HomomorphicLift (QuotientGroup.lift N (pullbackProjection B) hN) (MonoidHom.id B) :=
  ⟨(QuotientGroup.mk' N).comp (pullbackSection B), by
    apply MonoidHom.ext
    intro b
    exact pullbackProjection_section B b⟩

@[simp] theorem quotientSectionLift_apply
    (B : Subgroup ((ι → Multiplicative (ZMod 2)) × D))
    (N : Subgroup (pullback B)) [N.Normal] (hN : N ≤ (pullbackProjection B).ker) (b : B) :
    (quotientSectionLift B N hN).1 b = QuotientGroup.mk' N (pullbackSection B b) := rfl

end SymmetricSubgroupAsymptotics.RepeatedOddMarkerSection

end
