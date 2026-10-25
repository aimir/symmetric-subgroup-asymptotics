import SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryPointTailAction

/-! The native C3 vector coordinates used by the actual F4 centre chart.
The checked coordinate equivalence is (u,v) ↦ (v,-u), so the positive
native simple parameters, rather than the negative ones, give the
required short shears and the Y-axis long transvection in characteristic two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGFFourBinaryLeviNativeVectorCoordinates
open CFSGSymplecticSerreMatrices CFSGSymplecticBinaryPointTailAction
open CFSGSymplecticHeisenbergVectorAction
variable (K : Type) [Field K] [CharP K 2]

def nativePositive (i : Fin 3) (a : K) : elementaryRootGroup K 3 :=
  ⟨rootTransvection K 3 false i a,rootTransvection_mem K 3 false i a⟩

theorem native_short_vector (n : Fin 2) (a : K) (v : (Fin 3 → K) × (Fin 3 → K)) :
    vectorLinearHom K 3 (nativePositive K n.castSucc a) v =
      (v.1+Pi.single n.succ (a*v.1 n.castSucc),
       v.2+Pi.single n.castSucc (a*v.2 n.succ)) := by
  rw [vectorLinearHom_apply]
  apply Prod.ext <;> funext i
  all_goals
    fin_cases n <;> fin_cases i <;>
      simp [nativePositive,rootTransvection,rootMatrix,positive,vectorEquiv,
        Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.sub_mulVec,Matrix.one_mulVec,
        Matrix.single_mulVec,CharTwo.sub_eq_add,CharTwo.neg_eq,Pi.single_apply]

theorem native_long_vector (a : K) (v : (Fin 3 → K) × (Fin 3 → K)) :
    vectorLinearHom K 3 (nativePositive K 2 a) v =
      (v.1,v.2+Pi.single 2 (a*v.1 2)) := by
  rw [vectorLinearHom_apply]
  apply Prod.ext <;> funext i
  all_goals
    fin_cases i <;>
      simp [nativePositive,rootTransvection,rootMatrix,positive,vectorEquiv,
        Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,
        Matrix.single_mulVec,CharTwo.neg_eq,Pi.single_apply]

end SymmetricSubgroupAsymptotics.CFSGFFourBinaryLeviNativeVectorCoordinates
