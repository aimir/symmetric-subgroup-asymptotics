import SymmetricSubgroupAsymptotics.CFSGFFourOriginalHeightFourRaising
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! A bounded integer coefficient block for the shared source-table
induction: the twelve checked raises on roots 7,8,9, now expressed in
one finite coefficient family. The source equation is derived from
the existing original identities, not from a proposed basis table. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourOriginalHeightThreeActionTable
open CFSG.Models.Chevalley CFSGFFourOriginalFiftyTwoFamily
open CFSGFFourOriginalHeightFourRaising
local notation "A" => CartanMatrix.F₄
local notation "L" => RationalLie A

def rootIndex (j:Fin 3) : Fin 24:=⟨j.val+7,by omega⟩

def raisingCoefficients (i:Fin 4) (j:Fin 3) : Fin 24→ℤ :=
  ![![Pi.single 11 (-1),Pi.single 10 (-2),0,0],
    ![Pi.single 12 1,0,0,Pi.single 10 1],
    ![0,Pi.single 12 1,0,Pi.single 11 1]] j i

private theorem cast_single (j:Fin 24) (c:ℤ) :
    (fun k:Fin 24=>(((Pi.single j c:Fin 24→ℤ) k):ℚ))=
      (Pi.single j (c:ℚ):Fin 24→ℚ) := by
  funext k
  by_cases hk:j=k <;> simp [Pi.single_apply,hk]

private theorem combination_zero {V:Type*} [AddCommGroup V] [Module ℚ V]
    (v:Fin 24→V) : Fintype.linearCombination ℚ v (fun _:Fin 24=>(0:ℚ))=0 := by
  change Fintype.linearCombination ℚ v (0:Fin 24→ℚ)=0
  exact map_zero _

private theorem table_combination {V:Type*} [AddCommGroup V] [Module ℚ V]
    (v:Fin 24→V) (i:Fin 4) (j:Fin 3) :
    Fintype.linearCombination ℚ v (fun k=>(raisingCoefficients i j k:ℚ))=
      ![![-v 11,(-2:ℚ) • v 10,0,0],![v 12,0,0,v 10],![0,v 12,0,v 11]] j i := by
  fin_cases j <;> fin_cases i <;>
    simp [raisingCoefficients,cast_single,Fintype.linearCombination_apply_single,combination_zero]

theorem raising_eq_table (neg:Bool) (i:Fin 4) (j:Fin 3) :
    ⁅rootVector A neg i,(rootVectors neg (rootIndex j)).val⁆=
      Fintype.linearCombination ℚ (fun k:Fin 24=>(rootVectors neg k).val)
        (fun k=>(raisingCoefficients i j k:ℚ)) := by
  rw [table_combination]
  fin_cases j
  · change ⁅rootVector A neg i,(rootVectors neg 7).val⁆=
      ![-(rootVectors neg 11).val,(-2:ℚ) • (rootVectors neg 10).val,0,0] i
    exact raising_seven neg i
  · change ⁅rootVector A neg i,(rootVectors neg 8).val⁆=
      ![(rootVectors neg 12).val,0,0,(rootVectors neg 10).val] i
    exact raising_eight neg i
  · change ⁅rootVector A neg i,(rootVectors neg 9).val⁆=
      ![0,(rootVectors neg 12).val,0,(rootVectors neg 11).val] i
    exact raising_nine neg i

end SymmetricSubgroupAsymptotics.CFSGFFourOriginalHeightThreeActionTable
