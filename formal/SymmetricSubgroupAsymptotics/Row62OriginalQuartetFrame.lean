import SymmetricSubgroupAsymptotics.ProductBlockFrameGenerators
import SymmetricSubgroupAsymptotics.DerivedGeneratorWords
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows51To100
import Mathlib.GroupTheory.Perm.Closure
import Mathlib.GroupTheory.Perm.Fin
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row62OriginalQuartetFrame
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

def points : Fin 3 × Fin 4 ≃ Fin 12 where
  toFun x := (#[0,3,6,9,4,7,10,1,8,11,2,5] : Array (Fin 12))[4*x.1.val+x.2.val]!
  invFun x := (#[(0,0),(1,3),(2,2),(0,1),(1,0),(2,3),
    (0,2),(1,1),(2,0),(0,3),(1,2),(2,1)] : Array (Fin 3 × Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def tops : Fin 3 → Equiv.Perm (Fin 3) := ![1,finRotate 3,Equiv.swap 0 1]
private theorem preserves : ∀ (i : Fin 3) (x : Fin 3 × Fin 4),
    (points.symm (row62Generators i (points x))).1=tops i x.1 := by decide +kernel

def frame : ProductBlockFrame Row62Top (Fin 3) (Fin 4) :=
  ProductBlockFrame.ofGenerators points row62Generators tops preserves

def original : Fin 3 → Row62Top := closureGenerators row62Generators

theorem generator_top (i : Fin 3) : frame.top (original i)=tops i :=
  ProductBlockFrame.ofGenerators_top_generator points row62Generators tops preserves i

theorem pure_cycle : ∀ x : Fin 3 × Fin 4,
    points.symm (row62Generators 1 (points x))=(finRotate 3 x.1,x.2) := by decide +kernel
theorem pure_swap : ∀ x : Fin 3 × Fin 4,
    points.symm (row62Generators 2 (points x))=(Equiv.swap 0 1 x.1,x.2) := by decide +kernel

theorem top_surjective : Function.Surjective frame.top := by
  have hc : Subgroup.closure ({finRotate 3,Equiv.swap (0 : Fin 3) 1} :
      Set (Equiv.Perm (Fin 3)))=⊤ :=
    Equiv.Perm.closure_cycle_adjacent_swap isCycle_finRotate
      support_finRotate (0 : Fin 3)
  have hle : Subgroup.closure ({finRotate 3,Equiv.swap (0 : Fin 3) 1} :
      Set (Equiv.Perm (Fin 3)))≤frame.top.range := by
    apply (Subgroup.closure_le _).mpr
    intro p hp
    rcases Set.mem_insert_iff.mp hp with rfl | hp
    · exact ⟨original 1,generator_top 1⟩
    · have he : p=Equiv.swap (0 : Fin 3) 1 := Set.mem_singleton_iff.mp hp
      subst p
      exact ⟨original 2,generator_top 2⟩
  rw [hc] at hle
  exact fun p => hle (Subgroup.mem_top p)
end SymmetricSubgroupAsymptotics.Row62OriginalQuartetFrame
