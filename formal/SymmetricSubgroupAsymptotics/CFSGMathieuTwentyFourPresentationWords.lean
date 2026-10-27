import SymmetricSubgroupAsymptotics.External.CFSG.Certificates.Mathieu24.GeneratedSubgroup
import SymmetricSubgroupAsymptotics.External.CFSG.Models.Presentations.M24
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Tactic.FinCases

/-! Seven exact pinned M24 relators for the selected actual pair
x=(a*c*d)⁶, y=c⁹*z⁻¹*c⁻⁹, z=(c³*b⁴*c⁻³*b⁴)².
Primary diagnostic JSON SHA8f854427704d9bf74ef33dc122955f704ac06d9a3d0675476940fe1eb08aa2c4
supplied data only. Whole24-point kernel bindings and relation certificates
carry the obligation. No heavy order certificate or resource-cap change
is used. The sixth relation is the identity of a product of two cubes. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourPresentationWords
open CFSG.Certificates.Mathieu24

def originalA : M24 := ⟨m24a, m24a_mem_M24Subgroup⟩
def originalB : M24 := ⟨m24b, m24b_mem_M24Subgroup⟩
def originalC : M24 := ⟨m24c, m24c_mem_M24Subgroup⟩
def originalD : M24 := ⟨m24d, m24d_mem_M24Subgroup⟩
def z : M24 := (originalC^3*originalB^4*(originalC^3)⁻¹*originalB^4)^2
def x : M24 := (originalA*originalC*originalD)^6
def y : M24 := originalC^9*z⁻¹*(originalC^9)⁻¹
def generators : Fin 2 → M24 := fun i => if i = 0 then x else y

@[simp] theorem generators_zero : generators 0 = x := rfl
@[simp] theorem generators_one : generators 1 = y := rfl

private def xForward (i : Fin 24) : Fin 24 :=
  match i.val with
  | 0 => 15 | 1 => 5 | 2 => 17 | 3 => 22 | 4 => 18 | 5 => 1
  | 6 => 19 | 7 => 14 | 8 => 11 | 9 => 23 | 10 => 12 | 11 => 8
  | 12 => 10 | 13 => 16 | 14 => 7 | 15 => 0 | 16 => 13 | 17 => 2
  | 18 => 4 | 19 => 6 | 20 => 21 | 21 => 20 | 22 => 3 | _ => 9

private def yForward (i : Fin 24) : Fin 24 :=
  match i.val with
  | 0 => 6 | 1 => 13 | 2 => 9 | 3 => 8 | 4 => 22 | 5 => 21
  | 6 => 16 | 7 => 7 | 8 => 11 | 9 => 20 | 10 => 1 | 11 => 3
  | 12 => 4 | 13 => 10 | 14 => 5 | 15 => 15 | 16 => 0 | 17 => 17
  | 18 => 18 | 19 => 19 | 20 => 2 | 21 => 14 | 22 => 12 | _ => 23

private def yInverse (i : Fin 24) : Fin 24 :=
  match i.val with
  | 0 => 16 | 1 => 10 | 2 => 20 | 3 => 11 | 4 => 12 | 5 => 14
  | 6 => 0 | 7 => 7 | 8 => 3 | 9 => 2 | 10 => 13 | 11 => 8
  | 12 => 22 | 13 => 1 | 14 => 21 | 15 => 15 | 16 => 6 | 17 => 17
  | 18 => 18 | 19 => 19 | 20 => 9 | 21 => 5 | 22 => 4 | _ => 23

def xPermutation : Perm24 where
  toFun := xForward
  invFun := xForward
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def yPermutation : Perm24 where
  toFun := yForward
  invFun := yInverse
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem x_coe_eq : x.val = xPermutation := by
  ext i
  fin_cases i <;> decide +kernel

theorem y_coe_eq : y.val = yPermutation := by
  ext i
  fin_cases i <;> decide +kernel

theorem product_cycleType : (xPermutation*yPermutation).cycleType = {23} := by
  decide +kernel

def sixthWord {G : Type*} [Group G] (u v : G) : G :=
  (u*v*u*v*u*v⁻¹)^3*(u*v*u*v⁻¹*u*v⁻¹)^3

def seventhWord {G : Type*} [Group G] (u v : G) : G :=
  (u*v*(u*v*u*v⁻¹)^3)^4

theorem relator_zero : x ^ 2 = 1 := by
  apply Subtype.ext
  change x.val ^ 2 = (1 : Perm24)
  rw [x_coe_eq]
  ext i
  fin_cases i <;> decide +kernel

theorem relator_one : y ^ 3 = 1 := by
  apply Subtype.ext
  change y.val ^ 3 = (1 : Perm24)
  rw [y_coe_eq]
  ext i
  fin_cases i <;> decide +kernel

theorem relator_two : (x*y)^23 = 1 := by
  apply Subtype.ext
  change (x.val*y.val)^23 = (1 : Perm24)
  rw [x_coe_eq, y_coe_eq]
  ext i
  fin_cases i <;> decide +kernel

theorem relator_three : (CFSG.Models.commWord x y)^12 = 1 := by
  apply Subtype.ext
  change (x.val⁻¹*y.val⁻¹*x.val*y.val)^12 = (1 : Perm24)
  rw [x_coe_eq, y_coe_eq]
  ext i
  fin_cases i <;> decide +kernel

theorem relator_four : (CFSG.Models.commWord x (y*x*y))^5 = 1 := by
  apply Subtype.ext
  change (x.val⁻¹*(y.val*x.val*y.val)⁻¹*x.val*(y.val*x.val*y.val))^5 = (1 : Perm24)
  rw [x_coe_eq, y_coe_eq]
  ext i
  fin_cases i <;> decide +kernel

theorem relator_five : sixthWord x y = 1 := by
  apply Subtype.ext
  change sixthWord x.val y.val = (1 : Perm24)
  rw [x_coe_eq, y_coe_eq]
  ext i
  fin_cases i <;> decide +kernel

theorem relator_six : seventhWord x y = 1 := by
  apply Subtype.ext
  change seventhWord x.val y.val = (1 : Perm24)
  rw [x_coe_eq, y_coe_eq]
  ext i
  fin_cases i <;> decide +kernel

theorem all_relators : ∀ r ∈ CFSG.Models.Presentations.M24.relators,
    FreeGroup.lift generators r = 1 := by
  intro r hr
  simp only [CFSG.Models.Presentations.M24.relators, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [map_pow, FreeGroup.lift_apply_of, generators_zero] using relator_zero
  · simpa only [map_pow, FreeGroup.lift_apply_of, generators_one] using relator_one
  · simpa only [map_pow, map_mul, FreeGroup.lift_apply_of, generators_zero, generators_one]
      using relator_two
  · simpa only [CFSG.Models.commWord, map_pow, map_mul, map_inv, FreeGroup.lift_apply_of,
      generators_zero, generators_one] using relator_three
  · simpa only [CFSG.Models.commWord, map_pow, map_mul, map_inv, FreeGroup.lift_apply_of,
      generators_zero, generators_one] using relator_four
  · simpa only [sixthWord, map_pow, map_mul, map_inv, pow_one, FreeGroup.lift_apply_of,
      generators_zero, generators_one] using relator_five
  · simpa only [seventhWord, map_pow, map_mul, map_inv, pow_one, FreeGroup.lift_apply_of,
      generators_zero, generators_one] using relator_six

theorem y_ne_one : y ≠ 1 := by
  have hmove : y.val (0 : Fin 24) ≠ 0 := by
    rw [y_coe_eq]
    decide +kernel
  intro h
  exact hmove (congrArg (fun g : M24 => g.val (0 : Fin 24)) h)

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourPresentationWords
