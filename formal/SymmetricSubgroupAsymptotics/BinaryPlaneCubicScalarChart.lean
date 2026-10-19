import SymmetricSubgroupAsymptotics.BinaryPlanePermutationAffineEquiv
import SymmetricSubgroupAsymptotics.BinaryQuadraticField
import Mathlib.Data.Fintype.Perm

/-! An exact scalar chart for an actual fixed-point-free cubic operator
on the binary plane. The finite calculation ranges over permutations of
four points, not over subgroups or a catalogue of quartet extensions. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPlaneCubicScalarChart
open BinaryPlanePermutationAffineEquiv
open BinaryQuadraticField (Scalar omega)

def standard : Plane ≃ₗ[ZMod 2] Scalar :=
  (QuadraticAlgebra.linearEquivTuple (R := ZMod 2) (a := 1) (b := 1)).symm

private def swap : Linear where
  toFun v := ![v 1,v 0]
  invFun v := ![v 1,v 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_add' := by decide +kernel
  map_smul' := by decide +kernel

private def matrix (a b c d : ZMod 2) (v : Plane) : Plane :=
  ![a*v 0+b*v 1,c*v 0+d*v 1]

private theorem matrix_chart : ∀ a b c d : ZMod 2,
    (∀ v, matrix a b c d (matrix a b c d (matrix a b c d v))=v) →
    (∀ v, matrix a b c d v=v → v=0) →
    (∀ v, standard (matrix a b c d v)=omega*standard v) ∨
      (∀ v, standard (swap (matrix a b c d v))=omega*standard (swap v)) := by
  decide +kernel

/-- The finite witness considers only sixteen binary matrices, avoiding
function-space enumeration or a noncomputable permutation instance. -/
theorem exists_chart (L : Linear) (hc : L^3=1)
    (hf : ∀ v, L v=v → v=0) :
    ∃ E : Plane ≃ₗ[ZMod 2] Scalar, ∀ v, E (L v)=omega*E v := by
  let a := L ![1,0] 0
  let b := L ![0,1] 0
  let c := L ![1,0] 1
  let d := L ![0,1] 1
  have hL : ∀ v, L v=matrix a b c d v := by
    intro v
    have hv : v=v 0 • (![1,0] : Plane)+v 1 • (![0,1] : Plane) := by
      ext i
      fin_cases i <;> simp
    calc
      L v=L (v 0 • (![1,0] : Plane)+v 1 • (![0,1] : Plane)) := congrArg L hv
      _=matrix a b c d v := by
        rw [map_add,map_smul,map_smul]
        ext i
        fin_cases i <;> simp [matrix,a,b,c,d,mul_comm]
  have hs : ∀ v, matrix a b c d (matrix a b c d (matrix a b c d v))=v := by
    intro v
    simp only [← hL]
    change (L^3) v=v
    rw [hc]
    rfl
  have hfixed : ∀ v, matrix a b c d v=v → v=0 := by
    intro v hv
    exact hf v ((hL v).trans hv)
  rcases matrix_chart a b c d hs hfixed with h | h
  · exact ⟨standard,fun v => by rw [hL]; exact h v⟩
  · exact ⟨swap.trans standard,fun v => by change standard (swap (L v))=_; rw [hL]; exact h v⟩

/-- The coordinatewise extension of one actual local scalar chart. -/
def functionChart {I : Type} (E : Plane ≃ₗ[ZMod 2] Scalar) :
    (I → Plane) ≃ₗ[ZMod 2] (I → Scalar) :=
  LinearEquiv.piCongrRight (fun _ => E)

theorem functionChart_cubic {I : Type} (L : Linear)
    (E : Plane ≃ₗ[ZMod 2] Scalar) (hE : ∀ v, E (L v)=omega*E v)
    (v : I → Plane) (i : I) :
    functionChart E (fun j => L (v j)) i=omega*functionChart E v i :=
  hE (v i)

end SymmetricSubgroupAsymptotics.BinaryPlaneCubicScalarChart
