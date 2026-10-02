import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# The projective core of `GL₂(3)`

This is the part of the literal `GL₂(3)` calculation needed by the
degree-nine affine model.  It deliberately omits the later normal-subgroup
and historical-family developments: the action on four lines has central
kernel `{±I}`, hence kernel order two.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace LinearThreeCore

open Equiv

abbrev M2 := Matrix (Fin 2) (Fin 2) (ZMod 3)
abbrev V2 := Fin 2 → ZMod 3
abbrev GL3 := Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)

def det2 (A : M2) : ZMod 3 := A 0 0 * A 1 1 - A 0 1 * A 1 0

def glSet : Finset M2 := Finset.univ.filter (fun A => det2 A ≠ 0)

theorem det_eq_det2 (A : M2) : A.det = det2 A := Matrix.det_fin_two A

theorem coe_mem_glSet (g : GL3) : (g : M2) ∈ glSet := by
  rw [glSet, Finset.mem_filter, ← det_eq_det2]
  exact ⟨Finset.mem_univ _, Matrix.GeneralLinearGroup.det_ne_zero g⟩

def lineOf (v : V2) : Fin 4 :=
  if v 0 = 0 then 1 else if v 1 = 0 then 0 else if v 1 = v 0 then 2 else 3

def lineRep : Fin 4 → V2 := ![![1, 0], ![0, 1], ![1, 1], ![1, 2]]

def lineFun (A : M2) (line : Fin 4) : Fin 4 :=
  lineOf (A.mulVec (lineRep line))

set_option maxRecDepth 100000 in
theorem lineFun_mul : ∀ A ∈ glSet, ∀ B ∈ glSet, ∀ line : Fin 4,
    lineFun (A * B) line = lineFun A (lineFun B line) := by
  decide +kernel

theorem lineFun_one : ∀ line : Fin 4, lineFun 1 line = line := by decide

def projective : GL3 →* Perm (Fin 4) where
  toFun g :=
    { toFun := lineFun g
      invFun := lineFun (↑g⁻¹ : M2)
      left_inv := fun line => by
        rw [← lineFun_mul _ (coe_mem_glSet g⁻¹) _ (coe_mem_glSet g),
          Units.inv_mul, lineFun_one]
      right_inv := fun line => by
        rw [← lineFun_mul _ (coe_mem_glSet g) _ (coe_mem_glSet g⁻¹),
          Units.mul_inv, lineFun_one] }
  map_one' := by
    refine Equiv.ext fun line => ?_
    show lineFun ((1 : GL3) : M2) line = line
    rw [Units.val_one, lineFun_one]
  map_mul' g h := by
    refine Equiv.ext fun line => ?_
    show lineFun ((g * h : GL3) : M2) line = lineFun g (lineFun h line)
    rw [Units.val_mul, lineFun_mul _ (coe_mem_glSet g) _ (coe_mem_glSet h)]

theorem projective_apply (g : GL3) (line : Fin 4) :
    projective g line = lineFun g line := rfl

set_option maxRecDepth 100000 in
theorem lineFun_trivial_iff : ∀ A ∈ glSet,
    (∀ line : Fin 4, lineFun A line = line) ↔ (A = 1 ∨ A = -1) := by
  decide +kernel

theorem mem_ker_projective (g : GL3) :
    g ∈ projective.ker ↔ (g : M2) = 1 ∨ (g : M2) = -1 := by
  rw [MonoidHom.mem_ker, ← lineFun_trivial_iff _ (coe_mem_glSet g)]
  constructor
  · intro h line
    have hline := congrArg (fun sigma : Perm (Fin 4) => sigma line) h
    simpa [projective_apply] using hline
  · intro h
    ext line
    simp [projective_apply, h line]

theorem central_of_ker (z : GL3) (hz : z ∈ projective.ker) (g : GL3) :
    z * g = g * z := by
  rcases (mem_ker_projective z).mp hz with h | h <;>
    · apply Units.ext
      simp [h]

def kernelCode (z : projective.ker) : Fin 2 :=
  if (z.1 : M2) = 1 then 0 else 1

theorem kernelCode_injective : Function.Injective kernelCode := by
  intro x y hxy
  rcases (mem_ker_projective x.1).mp x.2 with hx | hx <;>
    rcases (mem_ker_projective y.1).mp y.2 with hy | hy
  · exact Subtype.ext (Units.ext (hx.trans hy.symm))
  · have hyne : (y.1 : M2) ≠ 1 := by rw [hy]; decide
    simp [kernelCode, hx, hyne] at hxy
  · have hxne : (x.1 : M2) ≠ 1 := by rw [hx]; decide
    simp [kernelCode, hxne, hy] at hxy
  · exact Subtype.ext (Units.ext (hx.trans hy.symm))

theorem card_ker_projective_le_two : Nat.card projective.ker ≤ 2 := by
  calc
    Nat.card projective.ker ≤ Nat.card (Fin 2) :=
      Nat.card_le_card_of_injective kernelCode kernelCode_injective
    _ = 2 := by simp

end LinearThreeCore
end SymmetricSubgroupAsymptotics
