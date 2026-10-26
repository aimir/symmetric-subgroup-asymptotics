import SymmetricSubgroupAsymptotics.External.CFSG.Certificates.Mathieu23.GeneratedSubgroup
import SymmetricSubgroupAsymptotics.External.CFSG.Models.Presentations.M23
import Mathlib.Tactic.FinCases

/-! Nine exact pinned M23 relators for x=c³*b⁴*c⁻³,y=b² in the original
actual generated subgroup. Primary pilot JSON
SHA78a9d712b5534828f0c2d758aa6f02048e9d176ee2f781fdfce0a4d46db1559d
supplied data only. Whole23-point kernel bindings and relator certificates
carry the mathematical obligation, using small table-backed permutations.
Relators7 and9 are unexponentiated words required to equal identity.
No proof resource setting is raised. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreePresentationWords
open CFSG.Certificates.Mathieu23

def originalA : M23 := ⟨m23a, m23a_mem_M23Subgroup⟩
def originalB : M23 := ⟨m23b, m23b_mem_M23Subgroup⟩
def originalC : M23 := ⟨m23c, m23c_mem_M23Subgroup⟩
def x : M23 := originalC ^ 3 * originalB ^ 4 * (originalC ^ 3)⁻¹
def y : M23 := originalB ^ 2
def generators : Fin 2 → M23 := fun i => if i = 0 then x else y

@[simp] theorem generators_zero : generators 0 = x := rfl
@[simp] theorem generators_one : generators 1 = y := rfl

private def xForward (i : Fin 23) : Fin 23 :=
  match i.val with
  | 0 => 14 | 1 => 13 | 2 => 21 | 3 => 3 | 4 => 5 | 5 => 4
  | 6 => 22 | 7 => 7 | 8 => 15 | 9 => 9 | 10 => 10 | 11 => 11
  | 12 => 20 | 13 => 1 | 14 => 0 | 15 => 8 | 16 => 16 | 17 => 18
  | 18 => 17 | 19 => 19 | 20 => 12 | 21 => 2 | _ => 6

private def yForward (i : Fin 23) : Fin 23 :=
  match i.val with
  | 0 => 10 | 1 => 17 | 2 => 2 | 3 => 0 | 4 => 6 | 5 => 12
  | 6 => 4 | 7 => 15 | 8 => 1 | 9 => 16 | 10 => 18 | 11 => 20
  | 12 => 9 | 13 => 11 | 14 => 14 | 15 => 7 | 16 => 5 | 17 => 19
  | 18 => 3 | 19 => 8 | 20 => 21 | 21 => 13 | _ => 22

private def yInverse (i : Fin 23) : Fin 23 :=
  match i.val with
  | 0 => 3 | 1 => 8 | 2 => 2 | 3 => 18 | 4 => 6 | 5 => 16
  | 6 => 4 | 7 => 15 | 8 => 19 | 9 => 12 | 10 => 0 | 11 => 13
  | 12 => 5 | 13 => 21 | 14 => 14 | 15 => 7 | 16 => 9 | 17 => 1
  | 18 => 10 | 19 => 17 | 20 => 11 | 21 => 20 | _ => 22

def xPermutation : Perm23 where
  toFun := xForward
  invFun := xForward
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def yPermutation : Perm23 where
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

def seventhWord {G : Type*} [Group G] (u v : G) : G :=
  (u*v)^3*u*v⁻¹*u*v^2*(u*v*u*v⁻¹)^2*(u*v)^3*(u*v⁻¹)^3

def ninthWord {G : Type*} [Group G] (u v : G) : G :=
  (u*v*u*v^2)^3*(u*v^2*u*v⁻¹)^2*u*v*u*v^2*u*v*u*v⁻¹*u*v^2

theorem relator_zero : x ^ 2 = 1 := by
  apply Subtype.ext
  change x.val ^ 2 = (1 : Perm23)
  rw [x_coe_eq]
  ext i
  fin_cases i <;> decide +kernel

theorem relator_one : y ^ 4 = 1 := by
  apply Subtype.ext
  change y.val ^ 4 = (1 : Perm23)
  rw [y_coe_eq]
  ext i
  fin_cases i <;> decide +kernel

theorem relator_two : (x * y) ^ 23 = 1 := by
  apply Subtype.ext
  change (x.val * y.val) ^ 23 = (1 : Perm23)
  rw [x_coe_eq, y_coe_eq]
  ext i
  fin_cases i <;> decide +kernel

theorem relator_three : (x * y ^ 2) ^ 6 = 1 := by
  apply Subtype.ext
  change (x.val * y.val ^ 2) ^ 6 = (1 : Perm23)
  rw [x_coe_eq, y_coe_eq]
  ext i
  fin_cases i <;> decide +kernel

theorem relator_four : (CFSG.Models.commWord x y) ^ 6 = 1 := by
  apply Subtype.ext
  change (x.val⁻¹ * y.val⁻¹ * x.val * y.val) ^ 6 = (1 : Perm23)
  rw [x_coe_eq, y_coe_eq]
  ext i
  fin_cases i <;> decide +kernel

theorem relator_five : (x*y*x*y⁻¹*x*y^2)^4 = 1 := by
  apply Subtype.ext
  change (x.val*y.val*x.val*y.val⁻¹*x.val*y.val^2)^4 = (1 : Perm23)
  rw [x_coe_eq, y_coe_eq]
  ext i
  fin_cases i <;> decide +kernel

theorem relator_six : seventhWord x y = 1 := by
  apply Subtype.ext
  change seventhWord x.val y.val = (1 : Perm23)
  rw [x_coe_eq, y_coe_eq]
  ext i
  fin_cases i <;> decide +kernel

theorem relator_seven : (x*y*x*y^2*x*y^2)^6 = 1 := by
  apply Subtype.ext
  change (x.val*y.val*x.val*y.val^2*x.val*y.val^2)^6 = (1 : Perm23)
  rw [x_coe_eq, y_coe_eq]
  ext i
  fin_cases i <;> decide +kernel

theorem relator_eight : ninthWord x y = 1 := by
  apply Subtype.ext
  change ninthWord x.val y.val = (1 : Perm23)
  rw [x_coe_eq, y_coe_eq]
  ext i
  fin_cases i <;> decide +kernel

theorem all_relators : ∀ r ∈ CFSG.Models.Presentations.M23.relators,
    FreeGroup.lift generators r = 1 := by
  intro r hr
  simp only [CFSG.Models.Presentations.M23.relators, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [map_pow, FreeGroup.lift_apply_of, generators_zero] using relator_zero
  · simpa only [map_pow, FreeGroup.lift_apply_of, generators_one] using relator_one
  · simpa only [map_pow, map_mul, FreeGroup.lift_apply_of, generators_zero, generators_one]
      using relator_two
  · simpa only [map_pow, map_mul, FreeGroup.lift_apply_of, generators_zero, generators_one]
      using relator_three
  · simpa only [CFSG.Models.commWord, map_pow, map_mul, map_inv, FreeGroup.lift_apply_of,
      generators_zero, generators_one] using relator_four
  · simpa only [map_pow, map_mul, map_inv, pow_one, FreeGroup.lift_apply_of,
      generators_zero, generators_one] using relator_five
  · simpa only [seventhWord, map_pow, map_mul, map_inv, pow_one, FreeGroup.lift_apply_of,
      generators_zero, generators_one] using relator_six
  · simpa only [map_pow, map_mul, FreeGroup.lift_apply_of, generators_zero, generators_one]
      using relator_seven
  · simpa only [ninthWord, map_pow, map_mul, map_inv, pow_one, FreeGroup.lift_apply_of,
      generators_zero, generators_one] using relator_eight

theorem y_ne_one : y ≠ 1 := by
  have hmove : y.val (0 : Fin 23) ≠ 0 := by
    rw [y_coe_eq]
    decide +kernel
  intro h
  exact hmove (congrArg (fun g : M23 => g.val (0 : Fin 23)) h)

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreePresentationWords
