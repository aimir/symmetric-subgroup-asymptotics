import SymmetricSubgroupAsymptotics.BinaryPairFrames

/-! Light original generator definitions for action25. No Cayley or normal certificate. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction025Generators

private def generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[1,0,2,3,5,4,7,6,8,9,11,10] : Array (Fin 12))[x.val]!
  invFun x := (#[1,0,2,3,5,4,7,6,8,9,11,10] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[1,0,3,2,4,5,7,6,9,8,10,11] : Array (Fin 12))[x.val]!
  invFun x := (#[1,0,3,2,4,5,7,6,9,8,10,11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[10,11,6,7,2,3,4,5,0,1,8,9] : Array (Fin 12))[x.val]!
  invFun x := (#[8,9,4,5,6,7,2,3,10,11,0,1] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def generator3 : Equiv.Perm (Fin 12) where
  toFun x := (#[0,1,8,9,10,11,6,7,2,3,4,5] : Array (Fin 12))[x.val]!
  invFun x := (#[0,1,8,9,10,11,6,7,2,3,4,5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def generator4 : Equiv.Perm (Fin 12) where
  toFun x := (#[6,7,2,3,10,11,0,1,8,9,4,5] : Array (Fin 12))[x.val]!
  invFun x := (#[6,7,2,3,10,11,0,1,8,9,4,5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generators (j : Fin 5) : Equiv.Perm (Fin 12) :=
  (if j.val < 2 then (if j.val < 1 then generator0 else generator1) else (if j.val < 3 then generator2 else (if j.val < 4 then generator3 else generator4)))


end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction025Generators
end
