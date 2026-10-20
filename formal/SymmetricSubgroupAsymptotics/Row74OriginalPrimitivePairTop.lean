import SymmetricSubgroupAsymptotics.Row74OriginalSixPairFrame
import SymmetricSubgroupAsymptotics.PrimitiveReferencePairWitness
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row74OriginalPrimitivePairTop
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
open Row74OriginalSixPairFrame

def original : Fin 2 → row74Interface.top := closureGenerators row74Generators
private theorem top_zero : frame.top (original 0)=Row74OriginalSixPairFrame.rotation := top_generator 0
private theorem top_one : frame.top (original 1)=swap := top_generator 1

def mover (a : Fin 6) : row74Interface.top :=
  if a=0 then 1 else original 0^(a.val-1)*original 1
def candidate (a : Fin 6) (j : Fin 5) : row74Interface.top := mover a*original 0^j.val
def model (a : Fin 6) (j : Fin 5) : Equiv.Perm (Fin 6) :=
  (if a=0 then 1 else Row74OriginalSixPairFrame.rotation^(a.val-1)*swap)*Row74OriginalSixPairFrame.rotation^j.val
private theorem candidate_top (a : Fin 6) (j : Fin 5) :
    frame.top (candidate a j)=model a j := by
  by_cases ha : a=0
  · simp [candidate,mover,model,ha,map_mul,map_pow,top_zero,top_one]
  · simp [candidate,mover,model,ha,map_mul,map_pow,top_zero,top_one]
private theorem reference_cover : ∀ x y : Fin 6,x≠y →
    ∃ (a : Fin 6) (j : Fin 5),model a j 0=x ∧ model a j 1=y := by
  decide +kernel

theorem two_pretransitive : MulAction.IsMultiplyPretransitive frame.top.range (Fin 6) 2 := by
  apply two_pretransitive_of_reference_pair (0 : Fin 6) 1
  intro x y hxy
  obtain ⟨a,j,hx,hy⟩ := reference_cover x y hxy
  refine ⟨frame.top.rangeRestrict (candidate a j),?_,?_⟩
  · change frame.top (candidate a j) 0=x
    rw [candidate_top]
    exact hx
  · change frame.top (candidate a j) 1=y
    rw [candidate_top]
    exact hy

instance primitive : MulAction.IsPreprimitive frame.top.range (Fin 6) :=
  MulAction.isPreprimitive_of_is_two_pretransitive two_pretransitive
end SymmetricSubgroupAsymptotics.Row74OriginalPrimitivePairTop
