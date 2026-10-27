import SymmetricSubgroupAsymptotics.CFSGMonsterSelectedDerivedInvolution
import SymmetricSubgroupAsymptotics.InvolutionBraidTrace
import Mathlib.Tactic.FinCases

/-! Eight literal original Bimonster involutions in the selected E8-shaped
subdiagram. Only original presentation relations are used; no root action
or finite Coxeter recognition is a premise. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMonsterE8BraidBinding
open CFSG.Models.MonsterConstruction InvolutionBraidTrace

def node (i : Fin 8) : Node :=
  ![none,some (0,0),some (0,1),some (0,2),some (0,3),some (1,0),some (1,1),some (2,0)] i

def adjacent (i j : Fin 8) : Bool :=
  match i.val,j.val with
  | 0,1 | 1,0 | 1,2 | 2,1 | 2,3 | 3,2 | 3,4 | 4,3 |
    0,5 | 5,0 | 5,6 | 6,5 | 0,7 | 7,0 => true
  | _,_ => false

def generator (i : Fin 8) : Bimonster :=
  CFSGMonsterSelectedDerivedInvolution.generator (node i)

theorem node_injective : Function.Injective node := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [node]

theorem adjacent_node (i j : Fin 8) : adjacent i j=true ↔ Adjacent (node i) (node j) := by
  fin_cases i <;> fin_cases j <;> simp [adjacent,node,Adjacent]

theorem generator_square (i : Fin 8) : generator i*generator i=1 := by
  simpa only [pow_two] using CFSGMonsterSelectedDerivedInvolution.generator_square (node i)

theorem generator_commute (i j : Fin 8) (hij : adjacent i j=false) :
    generator i*generator j=generator j*generator i := by
  by_cases he : i=j
  · subst j
    rfl
  have hn : ¬Adjacent (node i) (node j) := by
    intro h
    have ht := (adjacent_node i j).mpr h
    rw [hij] at ht
    cases ht
  have hne : node i≠node j := fun h => he (node_injective h)
  have hp := CFSGMonsterSelectedDerivedInvolution.nonadjacent_square (node i) (node j) hne hn
  have hi : (generator i)⁻¹=generator i := inv_eq_of_mul_eq_one_right (generator_square i)
  have hj : (generator j)⁻¹=generator j := inv_eq_of_mul_eq_one_right (generator_square j)
  have ht : (generator i*generator j)⁻¹=generator i*generator j :=
    inv_eq_of_mul_eq_one_right (by simpa only [generator,pow_two] using hp)
  have hh : generator j*generator i=generator i*generator j := by
    simpa only [mul_inv_rev,hi,hj] using ht
  exact hh.symm

theorem generator_braid (i j : Fin 8) (hij : adjacent i j=true) :
    generator i*generator j*generator i=generator j*generator i*generator j := by
  have hc : (generator i*generator j)^3=1 :=
    CFSGMonsterSelectedDerivedInvolution.adjacent_cube (node i) (node j) ((adjacent_node i j).mp hij)
  have hi : (generator i)⁻¹=generator i := inv_eq_of_mul_eq_one_right (generator_square i)
  have hj : (generator j)⁻¹=generator j := inv_eq_of_mul_eq_one_right (generator_square j)
  have hinv : (generator i*generator j*generator i)⁻¹=generator i*generator j*generator i := by
    simp only [mul_inv_rev,hi,hj,mul_assoc]
  have hm : (generator i*generator j*generator i)*(generator j*generator i*generator j)=1 := by
    simpa only [pow_succ,pow_zero,mul_one,mul_assoc] using hc
  calc
    _=(generator i*generator j*generator i)⁻¹ := hinv.symm
    _=(generator i*generator j*generator i)⁻¹*
        ((generator i*generator j*generator i)*(generator j*generator i*generator j)) := by rw [hm,mul_one]
    _=_ := by group

theorem reflection_square (w : List (Fin 8)) (i : Fin 8) :
    value generator (w++[i]++w.reverse)*value generator (w++[i]++w.reverse)=1 := by
  simp only [value_append,value_reverse generator generator_square]
  simp only [value,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]
  calc
    _=(value generator w)*(generator i*generator i)*(value generator w)⁻¹ := by
      change (value generator w*generator i*(value generator w)⁻¹)*
        (value generator w*generator i*(value generator w)⁻¹)=_
      group
    _=1 := by rw [generator_square]; group

end SymmetricSubgroupAsymptotics.CFSGMonsterE8BraidBinding
