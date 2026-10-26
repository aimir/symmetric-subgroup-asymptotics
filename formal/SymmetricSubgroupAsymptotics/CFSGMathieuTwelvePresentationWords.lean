import SymmetricSubgroupAsymptotics.External.CFSG.Certificates.Mathieu12.GeneratedSubgroup
import SymmetricSubgroupAsymptotics.External.CFSG.Models.Presentations.M12
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Tactic.FinCases

/-! Six exact pinned M12 relators for the selected actual pair
x=b², y=a⁵*b*(c*a)*b⁻¹*a⁻⁵. The primary's bounded44-pair diagnostic
(output SHA428a86bb4c9909d7d29f812eb917da357b55bca70420599cae13c16270c4547a)
supplied data only. Whole-point kernel proofs bind two small table images
to the original Apache-2.0 generators before checking the relators.
No resource setting is raised and no generation or surjectivity is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwelvePresentationWords
open CFSG.Certificates.Mathieu12

def originalA : M12 := ⟨m12a, m12a_mem_M12Subgroup⟩
def originalB : M12 := ⟨m12b, m12b_mem_M12Subgroup⟩
def originalC : M12 := ⟨m12c, m12c_mem_M12Subgroup⟩
def x : M12 := originalB ^ 2
def y : M12 := originalA ^ 5 * originalB * (originalC * originalA) *
  originalB⁻¹ * (originalA ^ 5)⁻¹
def generators : Fin 2 → M12 := fun i => if i = 0 then x else y

@[simp] theorem generators_zero : generators 0 = x := rfl
@[simp] theorem generators_one : generators 1 = y := rfl

private def xForward (i : Fin 12) : Fin 12 :=
  match i.val with
  | 0 => 0 | 1 => 1 | 2 => 10 | 3 => 4 | 4 => 3 | 5 => 9
  | 6 => 7 | 7 => 6 | 8 => 8 | 9 => 5 | 10 => 2 | _ => 11

private def yForward (i : Fin 12) : Fin 12 :=
  match i.val with
  | 0 => 7 | 1 => 11 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 1
  | 6 => 8 | 7 => 10 | 8 => 9 | 9 => 6 | 10 => 0 | _ => 5

private def yInverse (i : Fin 12) : Fin 12 :=
  match i.val with
  | 0 => 10 | 1 => 5 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 11
  | 6 => 9 | 7 => 0 | 8 => 6 | 9 => 8 | 10 => 7 | _ => 1

def xPermutation : Perm12 where
  toFun := xForward
  invFun := xForward
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def yPermutation : Perm12 where
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

theorem yPermutation_cycleType : yPermutation.cycleType = Multiset.replicate 4 3 := by
  decide +kernel

theorem y_cycleType : y.val.cycleType = Multiset.replicate 4 3 := by
  rw [y_coe_eq]
  exact yPermutation_cycleType

theorem relator_zero : x ^ 2 = 1 := by
  apply Subtype.ext
  change x.val ^ 2 = (1 : Perm12)
  rw [x_coe_eq]
  ext i
  fin_cases i <;> decide +kernel

theorem relator_one : y ^ 3 = 1 := by
  apply Subtype.ext
  change y.val ^ 3 = (1 : Perm12)
  rw [y_coe_eq]
  ext i
  fin_cases i <;> decide +kernel

theorem relator_two : (x * y) ^ 11 = 1 := by
  apply Subtype.ext
  change (x.val * y.val) ^ 11 = (1 : Perm12)
  rw [x_coe_eq, y_coe_eq]
  ext i
  fin_cases i <;> decide +kernel

theorem relator_three : (CFSG.Models.commWord x y) ^ 6 = 1 := by
  apply Subtype.ext
  change (x.val⁻¹ * y.val⁻¹ * x.val * y.val) ^ 6 = (1 : Perm12)
  rw [x_coe_eq, y_coe_eq]
  ext i
  fin_cases i <;> decide +kernel

theorem relator_four : (((((x * y) * x) * y) * x) * ((y⁻¹) ^ 1)) ^ 6 = 1 := by
  apply Subtype.ext
  change (((((x.val * y.val) * x.val) * y.val) * x.val) * ((y.val⁻¹) ^ 1)) ^ 6 =
    (1 : Perm12)
  rw [x_coe_eq, y_coe_eq]
  ext i
  fin_cases i <;> decide +kernel

theorem relator_five : (CFSG.Models.commWord x ((y * x) * y)) ^ 5 = 1 := by
  apply Subtype.ext
  change (x.val⁻¹ * ((y.val * x.val) * y.val)⁻¹ * x.val *
    ((y.val * x.val) * y.val)) ^ 5 = (1 : Perm12)
  rw [x_coe_eq, y_coe_eq]
  ext i
  fin_cases i <;> decide +kernel

theorem all_relators : ∀ r ∈ CFSG.Models.Presentations.M12.relators,
    FreeGroup.lift generators r = 1 := by
  intro r hr
  simp only [CFSG.Models.Presentations.M12.relators, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [map_pow, FreeGroup.lift_apply_of, generators_zero] using relator_zero
  · simpa only [map_pow, FreeGroup.lift_apply_of, generators_one] using relator_one
  · simpa only [map_pow, map_mul, FreeGroup.lift_apply_of, generators_zero, generators_one]
      using relator_two
  · simpa only [CFSG.Models.commWord, map_pow, map_mul, map_inv, FreeGroup.lift_apply_of,
      generators_zero, generators_one] using relator_three
  · simpa only [map_pow, map_mul, map_inv, FreeGroup.lift_apply_of,
      generators_zero, generators_one] using relator_four
  · simpa only [CFSG.Models.commWord, map_pow, map_mul, map_inv, FreeGroup.lift_apply_of,
      generators_zero, generators_one] using relator_five

theorem y_ne_one : y ≠ 1 := by
  have hmove : y.val (0 : Fin 12) ≠ 0 := by
    rw [y_coe_eq]
    decide +kernel
  intro h
  exact hmove (congrArg (fun g : M12 => g.val (0 : Fin 12)) h)

end SymmetricSubgroupAsymptotics.CFSGMathieuTwelvePresentationWords
