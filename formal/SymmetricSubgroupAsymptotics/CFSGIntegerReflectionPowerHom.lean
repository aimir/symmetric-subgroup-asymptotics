import SymmetricSubgroupAsymptotics.CFSGIntegerMatrixPowerHom

/-! Integer cocharacter reflections act on finite multiplicative tuples.
The single-coordinate formula supplies actual torus conjugation proofs;
no root-system or group-realization assertion is encoded here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGIntegerReflectionPowerHom
open CFSGIntegerMatrixPowerHom
variable {I G : Type*} [Fintype I] [DecidableEq I] [CommGroup G]

theorem powerHom_mulSingle (A : Matrix I I ℤ) (j : I) (t : G) :
    powerHom A (Pi.mulSingle j t)=fun i=>t^(A i j) := by
  classical
  funext i
  change (∏k : I,(Pi.mulSingle j t k)^(A i k))=t^(A i j)
  rw [Finset.prod_eq_single j]
  · simp
  · intro k _ hkj
    simp [hkj]
  · simp

def reflectionExponents (A : Matrix I I ℤ) (i : I) : Matrix I I ℤ :=
  fun k j=>(if k=j then 1 else 0)+(if k=i then -A i j else 0)

theorem reflection_mulSingle (A : Matrix I I ℤ) (i j : I) (t : G) :
    powerHom (reflectionExponents A i) (Pi.mulSingle j t)=
      Pi.mulSingle j t*Pi.mulSingle i (t^(-A i j)) := by
  rw [powerHom_mulSingle]
  funext k
  change t^((if k=j then (1:ℤ) else 0)+(if k=i then -A i j else 0))=
    (Pi.mulSingle j t : I→G) k*(Pi.mulSingle i (t^(-A i j)) : I→G) k
  rw [zpow_add]
  by_cases hkj : k=j <;> by_cases hki : k=i <;>
    simp [hkj,hki,Pi.mulSingle_apply,eq_comm]

omit [DecidableEq I] in
theorem powerHom_neg (A : Matrix I I ℤ) (x : I→G) :
    powerHom (-A) x=(powerHom A x)⁻¹ := by
  funext i
  simp only [powerHom_apply,Matrix.neg_apply,zpow_neg,Finset.prod_inv_distrib,Pi.inv_apply]

end SymmetricSubgroupAsymptotics.CFSGIntegerReflectionPowerHom
