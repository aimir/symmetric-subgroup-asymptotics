import SymmetricSubgroupAsymptotics.External.CFSG.Models.Presentations.Co2
import SymmetricSubgroupAsymptotics.LinearRepresentationSelectedPrimePeriod
import Mathlib.Tactic.Group

/-!
SOURCE-ONLY architecture, not a concrete native-matrix certificate.
The SAME old ten-relator carrier maps to any actual pair satisfying those
ten whole equations. The matrix specialization only needs a selected point
period to deduce prime23, with no injectivity or model-order premise.
The pending literal GL22/F2 packet must discharge every RelatorPacket field.
-/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGCoTwoLiteralRepresentation

open CFSG.Models

def pinnedX : Presentations.Co2.Model := PresentedGroup.of (0 : Fin 2)
def pinnedY : Presentations.Co2.Model := PresentedGroup.of (1 : Fin 2)

structure RelatorPacket {G : Type} [Group G] (x y : G) : Prop where
  first : x ^ 2 = 1
  second : y ^ 5 = 1
  third : (x * y ^ 2) ^ 9 = 1
  fourth : (commWord x y) ^ 4 = 1
  fifth : (commWord x (y ^ 2)) ^ 4 = 1
  sixth : (commWord x (y * x * y)) ^ 3 = 1
  seventh : (commWord x (y * x * y ^ 2 * x * y)) ^ 2 = 1
  eighth : (commWord x (y * x * (y⁻¹) ^ 2)) ^ 3 = 1
  ninth : (commWord x ((y⁻¹) ^ 2 * x * y * x * (y⁻¹) ^ 2)) ^ 2 = 1
  tenth : (x * y * x * y ^ 2 * x * y⁻¹ * x * (y⁻¹) ^ 2) ^ 7 = 1

def generators {G : Type} [Group G] (x y : G) : Fin 2 → G :=
  fun i => if i = 0 then x else y

@[simp] theorem generators_zero {G : Type} [Group G] (x y : G) :
    generators x y 0 = x := rfl

@[simp] theorem generators_one {G : Type} [Group G] (x y : G) :
    generators x y 1 = y := rfl

theorem all_relators {G : Type} [Group G] {x y : G} (h : RelatorPacket x y) :
    ∀ r ∈ Presentations.Co2.relators, FreeGroup.lift (generators x y) r = 1 := by
  intro r hr
  simp only [Presentations.Co2.relators, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [map_pow, FreeGroup.lift_apply_of, generators_zero] using h.first
  · simpa only [map_pow, FreeGroup.lift_apply_of, generators_one] using h.second
  · simpa only [map_pow, map_mul, FreeGroup.lift_apply_of,
      generators_zero, generators_one] using h.third
  · simpa only [commWord, map_pow, map_mul, map_inv, FreeGroup.lift_apply_of,
      generators_zero, generators_one] using h.fourth
  · simpa only [commWord, map_pow, map_mul, map_inv, FreeGroup.lift_apply_of,
      generators_zero, generators_one] using h.fifth
  · simpa only [commWord, map_pow, map_mul, map_inv, FreeGroup.lift_apply_of,
      generators_zero, generators_one] using h.sixth
  · simpa only [commWord, map_pow, map_mul, map_inv, FreeGroup.lift_apply_of,
      generators_zero, generators_one] using h.seventh
  · simpa only [commWord, map_pow, map_mul, map_inv, FreeGroup.lift_apply_of,
      generators_zero, generators_one] using h.eighth
  · simpa only [commWord, map_pow, map_mul, map_inv, FreeGroup.lift_apply_of,
      generators_zero, generators_one] using h.ninth
  · simpa only [map_pow, map_mul, map_inv, pow_one, FreeGroup.lift_apply_of,
      generators_zero, generators_one] using h.tenth

def representation {G : Type} [Group G] {x y : G} (h : RelatorPacket x y) :
    Presentations.Co2.Model →* G := PresentedGroup.toGroup (all_relators h)

theorem representation_generator {G : Type} [Group G] {x y : G}
    (h : RelatorPacket x y) (i : Fin 2) :
    representation h (PresentedGroup.of i) = generators x y i :=
  PresentedGroup.toGroup.of (all_relators h)

theorem representation_pinnedX {G : Type} [Group G] {x y : G} (h : RelatorPacket x y) :
    representation h pinnedX = x := by
  simpa only [pinnedX, generators_zero] using representation_generator h (0 : Fin 2)

theorem representation_pinnedY {G : Type} [Group G] {x y : G} (h : RelatorPacket x y) :
    representation h pinnedY = y := by
  simpa only [pinnedY, generators_one] using representation_generator h (1 : Fin 2)

/-- Exact upstream r0*r1 signed word, with the upstream left-to-right product convention. -/
def nativeSignedWord {G : Type} [Group G] (x y : G) : G :=
  x * (y⁻¹) ^ 2 * x⁻¹ * y * x * y ^ 2

/-- Positive nine-letter expression used by the selected trajectory. -/
def positiveWord {G : Type} [Group G] (x y : G) : G :=
  x * y ^ 3 * x * y * x * y ^ 2

theorem nativeSignedWord_eq_positiveWord {G : Type} [Group G] (x y : G)
    (hx : x ^ 2 = 1) (hy : y ^ 5 = 1) : nativeSignedWord x y = positiveWord x y := by
  have hx2 : x * x = 1 := by simpa only [pow_two] using hx
  have hxi : x⁻¹ = x := by
    calc
      x⁻¹ = x⁻¹ * 1 := (mul_one _).symm
      _ = x⁻¹ * (x * x) := by rw [hx2]
      _ = x := by group
  have hyi : (y⁻¹) ^ 2 = y ^ 3 := by
    have hleft : (y⁻¹) ^ 2 * y ^ 2 = 1 := by group
    have hright : y ^ 3 * y ^ 2 = 1 := by
      rw [← pow_add]
      exact hy
    exact mul_right_cancel (hleft.trans hright.symm)
  simp only [nativeSignedWord, positiveWord, hxi, hyi]

theorem representation_positiveWord {G : Type} [Group G] {x y : G}
    (h : RelatorPacket x y) :
    representation h (positiveWord pinnedX pinnedY) = positiveWord x y := by
  simp only [positiveWord, map_mul, map_pow, representation_pinnedX, representation_pinnedY]

theorem representation_nativeSignedWord {G : Type} [Group G] {x y : G}
    (h : RelatorPacket x y) :
    representation h (nativeSignedWord pinnedX pinnedY) = nativeSignedWord x y := by
  simp only [nativeSignedWord, map_mul, map_pow, map_inv,
    representation_pinnedX, representation_pinnedY]

abbrev MatrixImage := Matrix.GeneralLinearGroup (Fin 22) (ZMod 2)

def matrixRepresentation {a b : MatrixImage} (h : RelatorPacket a b) :
    Presentations.Co2.Model →* MatrixImage := representation h

def matrixWordEnd (a b : MatrixImage) : Module.End (ZMod 2) (Fin 22 → ZMod 2) :=
  LinearRepresentationSelectedPrimePeriod.linearEnd (MonoidHom.id MatrixImage) (positiveWord a b)

theorem linearEnd_selectedWord {a b : MatrixImage} (h : RelatorPacket a b) :
    LinearRepresentationSelectedPrimePeriod.linearEnd (matrixRepresentation h)
      (positiveWord pinnedX pinnedY) = matrixWordEnd a b := by
  change LinearRepresentationSelectedPrimePeriod.linearEnd (MonoidHom.id MatrixImage)
    (representation h (positiveWord pinnedX pinnedY)) = _
  rw [representation_positiveWord]
  rfl

/-- This consumes genuine equations and a genuine point period, not a named
native order theorem. The future literal certificate must discharge them. -/
theorem twentyThree_dvd_card_of_selected_period
    [Finite Presentations.Co2.Model] {a b : MatrixImage}
    (h : RelatorPacket a b) (v : Fin 22 → ZMod 2)
    (hreturn : (matrixWordEnd a b ^ 23) v = v)
    (hmoved : matrixWordEnd a b v ≠ v) : 23 ∣ Nat.card Presentations.Co2.Model := by
  apply LinearRepresentationSelectedPrimePeriod.prime_dvd_card
    (matrixRepresentation h) (positiveWord pinnedX pinnedY) 23 (by decide) v
  · simpa only [linearEnd_selectedWord] using hreturn
  · simpa only [linearEnd_selectedWord] using hmoved

end SymmetricSubgroupAsymptotics.CFSGCoTwoLiteralRepresentation
