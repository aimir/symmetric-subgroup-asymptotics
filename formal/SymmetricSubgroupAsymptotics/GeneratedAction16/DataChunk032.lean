import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Basic

/-! Original degree-16 generator tuples at common-family indices
1024 through 1055. Only literal permutations and
their finite inverse checks are defined here; no registry claim is made. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryActionData16

def node1213Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1213Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,6,7,4,5,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,6,7,4,5,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1213Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1213Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,0,1,2,3,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,3,2,1,0,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1213Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,14,15,12,13,3,2,0,1,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,14,15,12,13,3,2,0,1,6,7,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1213Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1213Generator0 else node1213Generator1) else (if j.val < 3 then node1213Generator2 else (if j.val < 4 then node1213Generator3 else node1213Generator4)))

def node1214Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,12,13,15,14,9,8,10,11,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,12,13,15,14,9,8,10,11,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1214Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,2,3,0,1,14,15,13,12,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,2,3,0,1,12,13,15,14,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1214Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1214Generator0 else node1214Generator1)

def node1215Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,5,4,7,6,0,1,2,3,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,5,4,7,6,1,0,3,2,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1215Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,8,9,10,11,15,14,12,13,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,0,1,3,2,4,5,6,7,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1215Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,15,14,12,13,0,1,3,2,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,13,12,14,15,2,3,1,0,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1215Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1215Generator0 else (if j.val < 2 then node1215Generator1 else node1215Generator2))

def node1216Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,13,12,3,2,0,1,5,4,7,6,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,9,8,11,10,13,12,14,15,3,2,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1216Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,4,5,7,6,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,4,5,7,6,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1216Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1216Generator0 else node1216Generator1)

def node1217Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,4,5,6,7,8,9,10,11,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,4,5,6,7,8,9,10,11,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1217Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,8,9,10,11,15,14,13,12,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,1,0,2,3,4,5,6,7,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1217Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1217Generator0 else node1217Generator1)

def node1218Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1218Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,7,6,4,5,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,6,7,5,4,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1218Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,6,7,4,5,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,6,7,4,5,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1218Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1218Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,4,5,6,7,3,2,0,1,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,4,5,6,7,2,3,1,0,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1218Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1218Generator0 else node1218Generator1) else (if j.val < 3 then node1218Generator2 else (if j.val < 4 then node1218Generator3 else node1218Generator4)))

def node1219Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,2,3,0,1,13,12,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,1,0,2,3,13,12,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1219Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,13,12,14,15,1,0,2,3,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,12,13,15,14,0,1,3,2,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1219Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,10,11,8,9,6,7,5,4,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,11,10,8,9,6,7,4,5,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1219Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1219Generator0 else (if j.val < 2 then node1219Generator1 else node1219Generator2))

def node1220Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1220Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,1,0,2,3,12,13,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,0,1,2,3,13,12,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1220Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,3,2,4,5,1,0,11,10,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,3,2,4,5,1,0,10,11,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1220Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,9,8,10,11,14,15,5,4,3,2,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,11,10,9,8,12,13,3,2,4,5,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1220Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1220Generator0 else node1220Generator1) else (if j.val < 3 then node1220Generator2 else node1220Generator3))

def node1221Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,4,5,6,7,8,9,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,4,5,6,7,8,9,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1221Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,5,4,14,15,9,8,11,10,13,12,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,0,1,3,2,12,13,7,6,9,8,11,10,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1221Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,12,13,14,15,1,0,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,13,12,14,15,1,0,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1221Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1221Generator0 else (if j.val < 2 then node1221Generator1 else node1221Generator2))

def node1222Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,4,5,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,5,4,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1222Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,14,15,9,8,10,11,3,2,0,1,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,12,13,15,14,5,4,6,7,0,1,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1222Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1222Generator0 else node1222Generator1)

def node1223Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,1,0,2,3,5,4,7,6,8,9,11,10,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,4,5,7,6,9,8,10,11,13,12,15,14,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1223Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,8,9,11,10,12,13,15,14,1,0,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,15,14,1,0,2,3,5,4,6,7,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1223Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1223Generator0 else node1223Generator1)

def node1224Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,13,12,15,14,6,7,5,4,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,11,10,8,9,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1224Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,1,0,3,2,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,0,1,2,3,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1224Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1224Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1224Generator0 else (if j.val < 2 then node1224Generator1 else node1224Generator2))

def node1225Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1225Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,7,6,4,5,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,6,7,5,4,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1225Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1225Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,0,1,2,3,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,2,3,1,0,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1225Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,14,15,12,13,3,2,0,1,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,14,15,12,13,3,2,0,1,6,7,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1225Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1225Generator0 else node1225Generator1) else (if j.val < 3 then node1225Generator2 else (if j.val < 4 then node1225Generator3 else node1225Generator4)))

def node1226Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1226Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,6,7,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,6,7,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1226Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,5,4,6,7,8,9,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,5,4,6,7,8,9,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1226Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1226Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,13,12,15,14,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,13,12,15,14,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1226Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1226Generator0 else node1226Generator1) else (if j.val < 3 then node1226Generator2 else (if j.val < 4 then node1226Generator3 else node1226Generator4)))

def node1227Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,14,15,12,13,3,2,0,1,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,14,15,12,13,3,2,0,1,6,7,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1227Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,0,1,2,3,4,5,7,6,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,8,9,11,10,14,15,13,12,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1227Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,4,5,7,6,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,4,5,7,6,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1227Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1227Generator0 else (if j.val < 2 then node1227Generator1 else node1227Generator2))

def node1228Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1228Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,2,3,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,2,3,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1228Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,3,2,4,5,1,0,11,10,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,3,2,4,5,1,0,10,11,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1228Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,9,8,10,11,14,15,5,4,3,2,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,11,10,9,8,12,13,3,2,4,5,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1228Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1228Generator0 else node1228Generator1) else (if j.val < 3 then node1228Generator2 else node1228Generator3))

def node1229Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,6,7,1,0,3,2,5,4,14,15,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,9,8,11,10,4,5,14,15,0,1,2,3,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1229Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,12,13,14,15,1,0,2,3,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,12,13,14,15,0,1,2,3,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1229Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1229Generator0 else node1229Generator1)

def node1230Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,2,3,0,1,14,15,13,12,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,3,2,1,0,12,13,14,15,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1230Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,8,9,10,11,6,7,4,5,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,10,11,8,9,4,5,6,7,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1230Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,13,12,14,15,2,3,0,1,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,15,14,13,12,1,0,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1230Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1230Generator0 else (if j.val < 2 then node1230Generator1 else node1230Generator2))

def node1231Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1231Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,4,5,11,10,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,5,4,10,11,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1231Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,4,5,7,6,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,4,5,7,6,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1231Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,2,3,0,1,14,15,13,12,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,0,1,3,2,12,13,14,15,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1231Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,13,12,15,14,3,2,0,1,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,15,14,12,13,1,0,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1231Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1231Generator0 else node1231Generator1) else (if j.val < 3 then node1231Generator2 else (if j.val < 4 then node1231Generator3 else node1231Generator4)))

def node1232Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,15,14,12,13,1,0,3,2,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,15,14,13,12,0,1,3,2,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1232Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,2,3,1,0,13,12,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,1,0,3,2,13,12,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1232Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1232Generator0 else node1232Generator1)

def node1233Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1233Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,15,14,13,12,1,0,2,3,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,13,12,15,14,2,3,1,0,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1233Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,13,12,7,6,5,4,10,11,8,9,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,7,6,5,4,10,11,8,9,3,2,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1233Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1233Generator0 else (if j.val < 2 then node1233Generator1 else node1233Generator2))

def node1234Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1234Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,5,4,7,6,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,5,4,7,6,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1234Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,0,1,3,2,12,13,15,14,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,2,3,0,1,14,15,12,13,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1234Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,14,15,11,10,9,8,4,5,7,6,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,8,9,11,10,7,6,5,4,0,1,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1234Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,13,12,11,10,9,8,6,7,4,5,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,10,11,8,9,7,6,5,4,3,2,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1234Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1234Generator0 else node1234Generator1) else (if j.val < 3 then node1234Generator2 else (if j.val < 4 then node1234Generator3 else node1234Generator4)))

def node1235Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,12,13,14,15,3,2,1,0,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,1,0,2,3,13,12,14,15,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1235Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,9,8,11,10,6,7,4,5,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,10,11,8,9,5,4,7,6,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1235Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,9,8,10,11,7,6,4,5,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,10,11,9,8,5,4,6,7,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1235Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1235Generator0 else (if j.val < 2 then node1235Generator1 else node1235Generator2))

def node1236Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,7,6,4,5,10,11,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,6,7,5,4,11,10,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1236Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,12,13,10,11,7,6,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,14,15,9,8,0,1,6,7,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1236Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,2,3,0,1,14,15,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,2,3,1,0,14,15,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1236Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1236Generator0 else (if j.val < 2 then node1236Generator1 else node1236Generator2))

def node1237Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,13,12,15,14,1,0,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,13,12,15,14,1,0,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1237Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,1,0,3,2,6,7,5,4,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,11,10,8,9,14,15,12,13,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1237Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,2,3,0,1,7,6,4,5,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,10,11,9,8,15,14,13,12,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1237Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1237Generator0 else (if j.val < 2 then node1237Generator1 else node1237Generator2))

def node1238Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1238Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1238Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,2,3,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,2,3,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1238Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,1,0,2,3,5,4,14,15,9,8,10,11,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,4,5,7,6,0,1,11,10,12,13,15,14,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1238Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,12,13,14,15,4,5,7,6,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,8,9,11,10,0,1,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1238Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1238Generator0 else node1238Generator1) else (if j.val < 3 then node1238Generator2 else (if j.val < 4 then node1238Generator3 else node1238Generator4)))

def node1239Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,8,9,11,10,14,15,13,12,0,1,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,15,14,1,0,2,3,4,5,7,6,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1239Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,12,13,14,15,2,3,0,1,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,14,15,12,13,0,1,2,3,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1239Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,5,4,7,6,9,8,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,5,4,7,6,9,8,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1239Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1239Generator0 else (if j.val < 2 then node1239Generator1 else node1239Generator2))

def node1240Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,12,13,15,14,2,3,0,1,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,14,15,12,13,1,0,2,3,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1240Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,1,0,2,3,13,12,14,15,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,2,3,0,1,14,15,12,13,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1240Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,2,3,0,1,15,14,13,12,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,12,13,14,15,3,2,0,1,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1240Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1240Generator0 else (if j.val < 2 then node1240Generator1 else node1240Generator2))

def node1241Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1241Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,1,0,2,3,12,13,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,0,1,2,3,13,12,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1241Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,3,2,4,5,1,0,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,3,2,4,5,0,1,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1241Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,9,8,10,11,14,15,5,4,3,2,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,11,10,9,8,12,13,3,2,4,5,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1241Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1241Generator0 else node1241Generator1) else (if j.val < 3 then node1241Generator2 else node1241Generator3))

def node1242Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1242Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1242Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,1,0,2,3,8,9,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,0,1,2,3,8,9,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1242Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,1,0,2,3,5,4,14,15,9,8,10,11,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,4,5,7,6,0,1,11,10,12,13,15,14,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1242Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,12,13,14,15,4,5,7,6,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,8,9,11,10,0,1,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1242Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1242Generator0 else node1242Generator1) else (if j.val < 3 then node1242Generator2 else (if j.val < 4 then node1242Generator3 else node1242Generator4)))

def node1243Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,4,5,8,9,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,6,7,4,5,8,9,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1243Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,13,12,1,0,2,3,7,6,4,5,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,10,11,9,8,14,15,12,13,3,2,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1243Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1243Generator0 else node1243Generator1)

def node1244Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,15,14,0,1,3,2,7,6,5,4,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,11,10,9,8,13,12,14,15,1,0,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1244Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,4,5,6,7,9,8,11,10,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,4,5,6,7,9,8,11,10,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1244Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1244Generator0 else node1244Generator1)

end SymmetricSubgroupAsymptotics.BinaryActionData16
