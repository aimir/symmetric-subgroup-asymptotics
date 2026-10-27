import SymmetricSubgroupAsymptotics.CFSGJankoOnePresentationGenerators
import SymmetricSubgroupAsymptotics.FiniteGeneratorWord
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Data.ZMod.Basic

/-! A genuine representation of the exact pinned J1 presentation from
five literal whole-element equations. Inherited simplicity and one
nonidentity image prove injectivity. Neither model recognition, image
order, surjectivity nor a named finite matrix group is assumed.
The final matrix specialisation is GL(7,F11), not a replacement model. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGJankoOneLiteralRepresentation
open CFSGJankoOnePresentationGenerators

def fourthWord {G : Type} [Group G] (x y : G) : G :=
  (x*y)*((x*y*x*((y⁻¹)^1))^3)

structure RelatorPacket {G : Type} [Group G] (x y : G) : Prop where
  first : x^2=1
  second : y^3=1
  third : (x*y)^7=1
  fourth : (fourthWord x y)^5=1
  fifth : (lastInvolutionWord x y)^2=1

def generators {G : Type} [Group G] (x y : G) : Fin 2 → G :=
  fun i => if i=0 then x else y

@[simp] theorem generators_zero {G : Type} [Group G] (x y : G) : generators x y 0=x := rfl
@[simp] theorem generators_one {G : Type} [Group G] (x y : G) : generators x y 1=y := rfl

theorem all_relators {G : Type} [Group G] {x y : G} (h : RelatorPacket x y) :
    ∀ r ∈ CFSG.Models.Presentations.J1.relators,FreeGroup.lift (generators x y) r=1 := by
  intro r hr
  simp only [CFSG.Models.Presentations.J1.relators,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl
  · simpa only [map_pow,FreeGroup.lift_apply_of,generators_zero] using h.first
  · simpa only [map_pow,FreeGroup.lift_apply_of,generators_one] using h.second
  · simpa only [map_pow,map_mul,FreeGroup.lift_apply_of,generators_zero,generators_one] using h.third
  · simpa only [fourthWord,map_pow,map_mul,map_inv,FreeGroup.lift_apply_of,
      generators_zero,generators_one] using h.fourth
  · simpa only [lastInvolutionWord,map_pow,map_mul,map_inv,FreeGroup.lift_apply_of,
      generators_zero,generators_one] using h.fifth

def representation {G : Type} [Group G] {x y : G} (h : RelatorPacket x y) :
    CFSG.Models.Presentations.J1.Model →* G := PresentedGroup.toGroup (all_relators h)

theorem representation_generator {G : Type} [Group G] {x y : G}
    (h : RelatorPacket x y) (i : Fin 2) :
    representation h (PresentedGroup.of i)=generators x y i := by
  exact PresentedGroup.toGroup.of (all_relators h)

theorem representation_pinnedX {G : Type} [Group G] {x y : G} (h : RelatorPacket x y) :
    representation h pinnedX=x := by
  simpa only [pinnedX,generators_zero] using representation_generator h (0 : Fin 2)

theorem representation_pinnedY {G : Type} [Group G] {x y : G} (h : RelatorPacket x y) :
    representation h pinnedY=y := by
  simpa only [pinnedY,generators_one] using representation_generator h (1 : Fin 2)

theorem representation_injective {G : Type} [Group G] {x y : G}
    (h : RelatorPacket x y) (hx : x≠1)
    [IsSimpleGroup CFSG.Models.Presentations.J1.Model] : Function.Injective (representation h) := by
  rcases (inferInstance : (representation h).ker.Normal).eq_bot_or_eq_top with hbot|htop
  · exact (representation h).ker_eq_bot_iff.mp hbot
  · have hm : pinnedX∈(representation h).ker := by rw [htop]; trivial
    have he : representation h pinnedX=1 := hm
    exact (hx ((representation_pinnedX h).symm.trans he)).elim

theorem representation_word {G : Type} [Group G] {x y : G}
    (h : RelatorPacket x y) (w : FiniteGeneratorWord (Fin 2)) :
    representation h (w.eval (fun i => (PresentedGroup.of i : CFSG.Models.Presentations.J1.Model)))=
      w.eval (generators x y) := by
  simpa only [representation_generator] using
    FiniteGeneratorWord.map_eval (representation h)
      (fun i => (PresentedGroup.of i : CFSG.Models.Presentations.J1.Model)) w

theorem word_equality_of_image {G : Type} [Group G] {x y : G}
    (h : RelatorPacket x y) (hx : x≠1)
    [IsSimpleGroup CFSG.Models.Presentations.J1.Model]
    (u v : FiniteGeneratorWord (Fin 2))
    (he : u.eval (generators x y)=v.eval (generators x y)) :
    u.eval (fun i => (PresentedGroup.of i : CFSG.Models.Presentations.J1.Model))=
      v.eval (fun i => (PresentedGroup.of i : CFSG.Models.Presentations.J1.Model)) := by
  apply representation_injective h hx
  simpa only [representation_word] using he

theorem word_power_of_image {G : Type} [Group G] {x y : G}
    (h : RelatorPacket x y) (hx : x≠1)
    [IsSimpleGroup CFSG.Models.Presentations.J1.Model]
    (w : FiniteGeneratorWord (Fin 2)) (k : ℕ)
    (he : (w.eval (generators x y))^k=1) :
    (w.eval (fun i => (PresentedGroup.of i : CFSG.Models.Presentations.J1.Model)))^k=1 := by
  apply representation_injective h hx
  simpa only [map_pow,map_one,representation_word] using he

abbrev MatrixImage := Matrix.GeneralLinearGroup (Fin 7) (ZMod 11)

def matrixRepresentation {a b : MatrixImage} (h : RelatorPacket a b) :
    CFSG.Models.Presentations.J1.Model →* MatrixImage := representation h

theorem matrixRepresentation_injective {a b : MatrixImage} (h : RelatorPacket a b) (ha : a≠1)
    [IsSimpleGroup CFSG.Models.Presentations.J1.Model] : Function.Injective (matrixRepresentation h) :=
  representation_injective h ha

end SymmetricSubgroupAsymptotics.CFSGJankoOneLiteralRepresentation
