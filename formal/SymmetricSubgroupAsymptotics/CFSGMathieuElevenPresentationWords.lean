import SymmetricSubgroupAsymptotics.External.CFSG.Certificates.Mathieu11.GeneratedSubgroup
import SymmetricSubgroupAsymptotics.External.CFSG.Models.Presentations.M11
import Mathlib.Tactic.FinCases

/-! The selected literal pair x=a²b²a⁻²,y=b in Kenta's original11-point
generated subgroup satisfies all FIVE exact pinned M11 relators. The
primary's bounded20-pair diagnostic supplied data only; the whole-point
certificates here carry the mathematical obligation. Original Apache-2.0
generator data remain in the independently ported source unchanged. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuElevenPresentationWords
open CFSG.Certificates.Mathieu11

def originalA : M11 := ⟨m11a,m11a_mem_M11Subgroup⟩
def originalB : M11 := ⟨m11b,m11b_mem_M11Subgroup⟩
def x : M11 := originalA^2*originalB^2*(originalA^2)⁻¹
def y : M11 := originalB
def generators : Fin 2 → M11 := fun i => if i=0 then x else y

@[simp] theorem generators_zero : generators 0=x := rfl
@[simp] theorem generators_one : generators 1=y := rfl

theorem relator_zero : x^2=1 := by
  apply Subtype.ext
  ext i
  fin_cases i <;> decide +kernel

theorem relator_one : y^4=1 := by
  apply Subtype.ext
  ext i
  fin_cases i <;> decide +kernel

theorem relator_two : (x*y)^11=1 := by
  apply Subtype.ext
  ext i
  fin_cases i <;> decide +kernel

theorem relator_three : (x*y^2)^6=1 := by
  apply Subtype.ext
  ext i
  fin_cases i <;> decide +kernel

theorem relator_four :
    (((((((((((((((((x*y)*x)*y)*x)*((y⁻¹)^1))*x)*y)*x)*(y^2))*x)*((y⁻¹)^1))*x)*y)*x)*((y⁻¹)^1))*x)*((y⁻¹)^1))=1 := by
  apply Subtype.ext
  ext i
  fin_cases i <;> decide +kernel

theorem all_relators : ∀ r ∈ CFSG.Models.Presentations.M11.relators,
    FreeGroup.lift generators r=1 := by
  intro r hr
  simp only [CFSG.Models.Presentations.M11.relators,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl
  · simpa only [map_pow,FreeGroup.lift_apply_of,generators_zero] using relator_zero
  · simpa only [map_pow,FreeGroup.lift_apply_of,generators_one] using relator_one
  · simpa only [map_pow,map_mul,FreeGroup.lift_apply_of,generators_zero,generators_one]
      using relator_two
  · simpa only [map_pow,map_mul,FreeGroup.lift_apply_of,generators_zero,generators_one]
      using relator_three
  · simpa only [map_pow,map_mul,map_inv,FreeGroup.lift_apply_of,generators_zero,generators_one]
      using relator_four

theorem y_ne_one : y≠1 := by
  have hmove : y.val (2 : Fin 11)≠2 := by decide +kernel
  intro h
  exact hmove (congrArg (fun g : M11 => g.val (2 : Fin 11)) h)

end SymmetricSubgroupAsymptotics.CFSGMathieuElevenPresentationWords
