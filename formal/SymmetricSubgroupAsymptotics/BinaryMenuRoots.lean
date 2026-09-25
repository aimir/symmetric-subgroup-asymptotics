import SymmetricSubgroupAsymptotics.BinaryWreathRoots
import SymmetricSubgroupAsymptotics.BinaryPermutationBlocks

/-! Literal original menu roots, checked against structural Sylow actions.
The generator rows and conjugators are taken from the committed menu.
Only the small two-way generator words are checked by finite evaluation.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics

namespace BinaryMenuRoot2

def generator0 : Equiv.Perm (Fin 2) where
  toFun x := (#[1,0] : Array (Fin 2))[x.val]!
  invFun x := (#[1,0] : Array (Fin 2))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def conjugator : Equiv.Perm (Fin 2) where
  toFun x := (#[0,1] : Array (Fin 2))[x.val]!
  invFun x := (#[0,1] : Array (Fin 2))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generators (i : Fin 1) : Equiv.Perm (Fin 2) :=
  #[generator0][i.val]!

private def conjugateGenerators (i : Fin 1) : Equiv.Perm (Fin 2) :=
  MulAut.conj conjugator (binaryWreathPermGenerator 1 i)

theorem root_eq : Subgroup.closure (Set.range generators) =
    MulAut.conj conjugator • (binaryWreathSylow 1 :
      Subgroup (Equiv.Perm (Fin 2))) := by
  have hw := subgroup_closure_eq_of_generator_words generators conjugateGenerators
    (fun i => (#[[0]] :
      Array (List (Fin 1)))[i.val]!)
    (fun i => (#[[0]] :
      Array (List (Fin 1)))[i.val]!)
    (by decide +kernel) (by decide +kernel)
  rw [binaryWreathSylow_eq_closure, Subgroup.pointwise_smul_def,
    MonoidHom.map_closure]
  simpa only [← Set.range_comp, Function.comp_def, conjugateGenerators] using hw

def sylow : Sylow 2 (Equiv.Perm (Fin 2)) :=
  conjugator • binaryWreathSylow 1

theorem sylow_eq : (sylow : Subgroup (Equiv.Perm (Fin 2))) =
    Subgroup.closure (Set.range generators) := root_eq.symm

end BinaryMenuRoot2

namespace BinaryMenuRoot4

def generator0 : Equiv.Perm (Fin 4) where
  toFun x := (#[1,2,3,0] : Array (Fin 4))[x.val]!
  invFun x := (#[3,0,1,2] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generator1 : Equiv.Perm (Fin 4) where
  toFun x := (#[2,1,0,3] : Array (Fin 4))[x.val]!
  invFun x := (#[2,1,0,3] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def conjugator : Equiv.Perm (Fin 4) where
  toFun x := (#[0,2,1,3] : Array (Fin 4))[x.val]!
  invFun x := (#[0,2,1,3] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generators (i : Fin 2) : Equiv.Perm (Fin 4) :=
  #[generator0,generator1][i.val]!

private def conjugateGenerators (i : Fin 2) : Equiv.Perm (Fin 4) :=
  MulAut.conj conjugator (binaryWreathPermGenerator 2 i)

theorem root_eq : Subgroup.closure (Set.range generators) =
    MulAut.conj conjugator • (binaryWreathSylow 2 :
      Subgroup (Equiv.Perm (Fin 4))) := by
  have hw := subgroup_closure_eq_of_generator_words generators conjugateGenerators
    (fun i => (#[[0,1],[0]] :
      Array (List (Fin 2)))[i.val]!)
    (fun i => (#[[1],[1,0]] :
      Array (List (Fin 2)))[i.val]!)
    (by decide +kernel) (by decide +kernel)
  rw [binaryWreathSylow_eq_closure, Subgroup.pointwise_smul_def,
    MonoidHom.map_closure]
  simpa only [← Set.range_comp, Function.comp_def, conjugateGenerators] using hw

def sylow : Sylow 2 (Equiv.Perm (Fin 4)) :=
  conjugator • binaryWreathSylow 2

theorem sylow_eq : (sylow : Subgroup (Equiv.Perm (Fin 4))) =
    Subgroup.closure (Set.range generators) := root_eq.symm

end BinaryMenuRoot4

namespace BinaryMenuRoot8

def generator0 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,1,2,7,4,5,6,3] : Array (Fin 8))[x.val]!
  invFun x := (#[0,1,2,7,4,5,6,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generator1 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,1,0,3,6,5,4,7] : Array (Fin 8))[x.val]!
  invFun x := (#[2,1,0,3,6,5,4,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generator2 : Equiv.Perm (Fin 8) where
  toFun x := (#[1,2,7,4,5,6,3,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,0,1,6,3,4,5,2] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def conjugator : Equiv.Perm (Fin 8) where
  toFun x := (#[0,4,2,6,1,5,3,7] : Array (Fin 8))[x.val]!
  invFun x := (#[0,4,2,6,1,5,3,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generators (i : Fin 3) : Equiv.Perm (Fin 8) :=
  #[generator0,generator1,generator2][i.val]!

private def conjugateGenerators (i : Fin 3) : Equiv.Perm (Fin 8) :=
  MulAut.conj conjugator (binaryWreathPermGenerator 3 i)

theorem root_eq : Subgroup.closure (Set.range generators) =
    MulAut.conj conjugator • (binaryWreathSylow 3 :
      Subgroup (Equiv.Perm (Fin 8))) := by
  have hw := subgroup_closure_eq_of_generator_words generators conjugateGenerators
    (fun i => (#[[2,1,0,1,2],[1],[0,1,2,1,0,1]] :
      Array (List (Fin 3)))[i.val]!)
    (fun i => (#[[2,0,1,2,1],[1],[0,1,2,0]] :
      Array (List (Fin 3)))[i.val]!)
    (by decide +kernel) (by decide +kernel)
  rw [binaryWreathSylow_eq_closure, Subgroup.pointwise_smul_def,
    MonoidHom.map_closure]
  simpa only [← Set.range_comp, Function.comp_def, conjugateGenerators] using hw

def sylow : Sylow 2 (Equiv.Perm (Fin 8)) :=
  conjugator • binaryWreathSylow 3

theorem sylow_eq : (sylow : Subgroup (Equiv.Perm (Fin 8))) =
    Subgroup.closure (Set.range generators) := root_eq.symm

end BinaryMenuRoot8

namespace BinaryMenuRoot16

def generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,13,12,6,7,8,9,10,11,4,5,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,12,13,6,7,8,9,10,11,5,4,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,4,5,15,14,8,9,10,11,12,13,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,1,0,2,3,12,13,6,7,8,9,10,11,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,2,3,1,0,6,7,12,13,10,11,8,9,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,2,3,0,1,6,7,12,13,10,11,8,9,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def conjugator : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,8,9,4,5,12,13,2,3,10,11,6,7,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,8,9,4,5,12,13,2,3,10,11,6,7,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generators (i : Fin 4) : Equiv.Perm (Fin 16) :=
  #[generator0,generator1,generator2,generator3][i.val]!

private def conjugateGenerators (i : Fin 4) : Equiv.Perm (Fin 16) :=
  MulAut.conj conjugator (binaryWreathPermGenerator 4 i)

theorem root_eq : Subgroup.closure (Set.range generators) =
    MulAut.conj conjugator • (binaryWreathSylow 4 :
      Subgroup (Equiv.Perm (Fin 16))) := by
  have hw := subgroup_closure_eq_of_generator_words generators conjugateGenerators
    (fun i => (#[[3,2,1,0,1,2,3],[0,2,1,0,2,3,0,3],[0,1,2,3,0,2,1,0,2],[0,2]] :
      Array (List (Fin 4)))[i.val]!)
    (fun i => (#[[2,0,3,2,3],[2,2,0,1,2,2],[2,0,3,2,3,3],[0,1,2,0,1,2,2,2,3,2]] :
      Array (List (Fin 4)))[i.val]!)
    (by decide +kernel) (by decide +kernel)
  rw [binaryWreathSylow_eq_closure, Subgroup.pointwise_smul_def,
    MonoidHom.map_closure]
  simpa only [← Set.range_comp, Function.comp_def, conjugateGenerators] using hw

def sylow : Sylow 2 (Equiv.Perm (Fin 16)) :=
  conjugator • binaryWreathSylow 4

theorem sylow_eq : (sylow : Subgroup (Equiv.Perm (Fin 16))) =
    Subgroup.closure (Set.range generators) := root_eq.symm

end BinaryMenuRoot16

end SymmetricSubgroupAsymptotics
