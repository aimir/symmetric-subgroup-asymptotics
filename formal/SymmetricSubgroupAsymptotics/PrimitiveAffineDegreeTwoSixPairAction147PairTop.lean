import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction147ClassBase
import Mathlib.Tactic.FinCases

/-!
# Selected six-pair action 147: pair-top action

This is a resource-bounded split of the selected action-147 certificate.
All finite equations remain kernel checked.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction147ClassPilot

private def topRow0 : Equiv.Perm (Fin 6) where
  toFun x := (#[3,5,2,4,1,0] : Array (Fin 6))[x.val]!
  invFun x := (#[5,4,2,0,3,1] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow1 : Equiv.Perm (Fin 6) where
  toFun x := (#[5,1,4,3,2,0] : Array (Fin 6))[x.val]!
  invFun x := (#[5,1,4,3,2,0] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow2 : Equiv.Perm (Fin 6) where
  toFun x := (#[2,4,5,1,3,0] : Array (Fin 6))[x.val]!
  invFun x := (#[5,3,0,4,1,2] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow3 : Equiv.Perm (Fin 6) where
  toFun x := (#[1,2,3,5,4,0] : Array (Fin 6))[x.val]!
  invFun x := (#[5,0,1,2,4,3] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow4 : Equiv.Perm (Fin 6) where
  toFun x := (#[4,3,1,2,5,0] : Array (Fin 6))[x.val]!
  invFun x := (#[5,2,3,1,0,4] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow5 : Equiv.Perm (Fin 6) where
  toFun x := (#[4,2,5,3,1,0] : Array (Fin 6))[x.val]!
  invFun x := (#[5,4,1,3,0,2] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow6 : Equiv.Perm (Fin 6) where
  toFun x := (#[3,4,1,5,2,0] : Array (Fin 6))[x.val]!
  invFun x := (#[5,2,4,0,1,3] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow7 : Equiv.Perm (Fin 6) where
  toFun x := (#[1,5,4,2,3,0] : Array (Fin 6))[x.val]!
  invFun x := (#[5,0,3,4,2,1] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow8 : Equiv.Perm (Fin 6) where
  toFun x := (#[5,3,2,1,4,0] : Array (Fin 6))[x.val]!
  invFun x := (#[5,3,2,1,4,0] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow9 : Equiv.Perm (Fin 6) where
  toFun x := (#[2,1,3,4,5,0] : Array (Fin 6))[x.val]!
  invFun x := (#[5,1,0,2,3,4] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow10 : Equiv.Perm (Fin 6) where
  toFun x := (#[3,2,5,4,0,1] : Array (Fin 6))[x.val]!
  invFun x := (#[4,5,1,0,3,2] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow11 : Equiv.Perm (Fin 6) where
  toFun x := (#[4,3,0,5,2,1] : Array (Fin 6))[x.val]!
  invFun x := (#[2,5,4,1,0,3] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow12 : Equiv.Perm (Fin 6) where
  toFun x := (#[5,4,2,0,3,1] : Array (Fin 6))[x.val]!
  invFun x := (#[3,5,2,4,1,0] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow13 : Equiv.Perm (Fin 6) where
  toFun x := (#[0,5,3,2,4,1] : Array (Fin 6))[x.val]!
  invFun x := (#[0,5,3,2,4,1] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow14 : Equiv.Perm (Fin 6) where
  toFun x := (#[2,0,4,3,5,1] : Array (Fin 6))[x.val]!
  invFun x := (#[1,5,0,3,2,4] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow15 : Equiv.Perm (Fin 6) where
  toFun x := (#[4,5,2,3,0,1] : Array (Fin 6))[x.val]!
  invFun x := (#[4,5,2,3,0,1] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow16 : Equiv.Perm (Fin 6) where
  toFun x := (#[5,0,3,4,2,1] : Array (Fin 6))[x.val]!
  invFun x := (#[1,5,4,2,3,0] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow17 : Equiv.Perm (Fin 6) where
  toFun x := (#[0,2,4,5,3,1] : Array (Fin 6))[x.val]!
  invFun x := (#[0,5,1,4,2,3] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow18 : Equiv.Perm (Fin 6) where
  toFun x := (#[2,3,5,0,4,1] : Array (Fin 6))[x.val]!
  invFun x := (#[3,5,0,1,4,2] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow19 : Equiv.Perm (Fin 6) where
  toFun x := (#[3,4,0,2,5,1] : Array (Fin 6))[x.val]!
  invFun x := (#[2,5,3,0,1,4] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow20 : Equiv.Perm (Fin 6) where
  toFun x := (#[5,4,1,3,0,2] : Array (Fin 6))[x.val]!
  invFun x := (#[4,2,5,3,1,0] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow21 : Equiv.Perm (Fin 6) where
  toFun x := (#[4,0,3,5,1,2] : Array (Fin 6))[x.val]!
  invFun x := (#[1,4,5,2,0,3] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow22 : Equiv.Perm (Fin 6) where
  toFun x := (#[0,1,5,4,3,2] : Array (Fin 6))[x.val]!
  invFun x := (#[0,1,5,4,3,2] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow23 : Equiv.Perm (Fin 6) where
  toFun x := (#[3,5,0,1,4,2] : Array (Fin 6))[x.val]!
  invFun x := (#[2,3,5,0,4,1] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow24 : Equiv.Perm (Fin 6) where
  toFun x := (#[1,3,4,0,5,2] : Array (Fin 6))[x.val]!
  invFun x := (#[3,0,5,1,2,4] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow25 : Equiv.Perm (Fin 6) where
  toFun x := (#[3,1,4,5,0,2] : Array (Fin 6))[x.val]!
  invFun x := (#[4,1,5,0,2,3] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow26 : Equiv.Perm (Fin 6) where
  toFun x := (#[5,3,0,4,1,2] : Array (Fin 6))[x.val]!
  invFun x := (#[2,4,5,1,3,0] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow27 : Equiv.Perm (Fin 6) where
  toFun x := (#[4,5,1,0,3,2] : Array (Fin 6))[x.val]!
  invFun x := (#[3,2,5,4,0,1] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow28 : Equiv.Perm (Fin 6) where
  toFun x := (#[1,0,5,3,4,2] : Array (Fin 6))[x.val]!
  invFun x := (#[1,0,5,3,4,2] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow29 : Equiv.Perm (Fin 6) where
  toFun x := (#[0,4,3,1,5,2] : Array (Fin 6))[x.val]!
  invFun x := (#[0,3,5,2,1,4] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow30 : Equiv.Perm (Fin 6) where
  toFun x := (#[1,4,5,2,0,3] : Array (Fin 6))[x.val]!
  invFun x := (#[4,0,3,5,1,2] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow31 : Equiv.Perm (Fin 6) where
  toFun x := (#[5,2,4,0,1,3] : Array (Fin 6))[x.val]!
  invFun x := (#[3,4,1,5,2,0] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow32 : Equiv.Perm (Fin 6) where
  toFun x := (#[0,5,1,4,2,3] : Array (Fin 6))[x.val]!
  invFun x := (#[0,2,4,5,3,1] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow33 : Equiv.Perm (Fin 6) where
  toFun x := (#[2,1,0,5,4,3] : Array (Fin 6))[x.val]!
  invFun x := (#[2,1,0,5,4,3] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow34 : Equiv.Perm (Fin 6) where
  toFun x := (#[4,0,2,1,5,3] : Array (Fin 6))[x.val]!
  invFun x := (#[1,3,2,5,0,4] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow35 : Equiv.Perm (Fin 6) where
  toFun x := (#[2,5,4,1,0,3] : Array (Fin 6))[x.val]!
  invFun x := (#[4,3,0,5,2,1] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow36 : Equiv.Perm (Fin 6) where
  toFun x := (#[0,4,2,5,1,3] : Array (Fin 6))[x.val]!
  invFun x := (#[0,4,2,5,1,3] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow37 : Equiv.Perm (Fin 6) where
  toFun x := (#[4,1,5,0,2,3] : Array (Fin 6))[x.val]!
  invFun x := (#[3,1,4,5,0,2] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow38 : Equiv.Perm (Fin 6) where
  toFun x := (#[5,0,1,2,4,3] : Array (Fin 6))[x.val]!
  invFun x := (#[1,2,3,5,4,0] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow39 : Equiv.Perm (Fin 6) where
  toFun x := (#[1,2,0,4,5,3] : Array (Fin 6))[x.val]!
  invFun x := (#[2,0,1,5,3,4] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow40 : Equiv.Perm (Fin 6) where
  toFun x := (#[5,2,3,1,0,4] : Array (Fin 6))[x.val]!
  invFun x := (#[4,3,1,2,5,0] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow41 : Equiv.Perm (Fin 6) where
  toFun x := (#[0,3,5,2,1,4] : Array (Fin 6))[x.val]!
  invFun x := (#[0,4,3,1,5,2] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow42 : Equiv.Perm (Fin 6) where
  toFun x := (#[1,5,0,3,2,4] : Array (Fin 6))[x.val]!
  invFun x := (#[2,0,4,3,5,1] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow43 : Equiv.Perm (Fin 6) where
  toFun x := (#[2,0,1,5,3,4] : Array (Fin 6))[x.val]!
  invFun x := (#[1,2,0,4,5,3] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow44 : Equiv.Perm (Fin 6) where
  toFun x := (#[3,1,2,0,5,4] : Array (Fin 6))[x.val]!
  invFun x := (#[3,1,2,0,5,4] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow45 : Equiv.Perm (Fin 6) where
  toFun x := (#[1,3,2,5,0,4] : Array (Fin 6))[x.val]!
  invFun x := (#[4,0,2,1,5,3] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow46 : Equiv.Perm (Fin 6) where
  toFun x := (#[2,5,3,0,1,4] : Array (Fin 6))[x.val]!
  invFun x := (#[3,4,0,2,5,1] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow47 : Equiv.Perm (Fin 6) where
  toFun x := (#[3,0,5,1,2,4] : Array (Fin 6))[x.val]!
  invFun x := (#[1,3,4,0,5,2] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow48 : Equiv.Perm (Fin 6) where
  toFun x := (#[5,1,0,2,3,4] : Array (Fin 6))[x.val]!
  invFun x := (#[2,1,3,4,5,0] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow49 : Equiv.Perm (Fin 6) where
  toFun x := (#[0,2,1,3,5,4] : Array (Fin 6))[x.val]!
  invFun x := (#[0,2,1,3,5,4] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow50 : Equiv.Perm (Fin 6) where
  toFun x := (#[4,1,3,2,0,5] : Array (Fin 6))[x.val]!
  invFun x := (#[4,1,3,2,0,5] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow51 : Equiv.Perm (Fin 6) where
  toFun x := (#[2,4,0,3,1,5] : Array (Fin 6))[x.val]!
  invFun x := (#[2,4,0,3,1,5] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow52 : Equiv.Perm (Fin 6) where
  toFun x := (#[0,3,4,1,2,5] : Array (Fin 6))[x.val]!
  invFun x := (#[0,3,4,1,2,5] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow53 : Equiv.Perm (Fin 6) where
  toFun x := (#[1,0,2,4,3,5] : Array (Fin 6))[x.val]!
  invFun x := (#[1,0,2,4,3,5] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow54 : Equiv.Perm (Fin 6) where
  toFun x := (#[3,2,1,0,4,5] : Array (Fin 6))[x.val]!
  invFun x := (#[3,2,1,0,4,5] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow55 : Equiv.Perm (Fin 6) where
  toFun x := (#[2,3,1,4,0,5] : Array (Fin 6))[x.val]!
  invFun x := (#[4,2,0,1,3,5] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow56 : Equiv.Perm (Fin 6) where
  toFun x := (#[3,0,4,2,1,5] : Array (Fin 6))[x.val]!
  invFun x := (#[1,4,3,0,2,5] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow57 : Equiv.Perm (Fin 6) where
  toFun x := (#[1,4,3,0,2,5] : Array (Fin 6))[x.val]!
  invFun x := (#[3,0,4,2,1,5] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow58 : Equiv.Perm (Fin 6) where
  toFun x := (#[4,2,0,1,3,5] : Array (Fin 6))[x.val]!
  invFun x := (#[2,3,1,4,0,5] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow59 : Equiv.Perm (Fin 6) where
  toFun x := (#[0,1,2,3,4,5] : Array (Fin 6))[x.val]!
  invFun x := (#[0,1,2,3,4,5] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRows (i : Fin 60) : Equiv.Perm (Fin 6) :=
  (if i.val < 30 then (if i.val < 15 then (if i.val < 7 then (if i.val < 3 then (if i.val < 1 then topRow0 else (if i.val < 2 then topRow1 else topRow2)) else (if i.val < 5 then (if i.val < 4 then topRow3 else topRow4) else (if i.val < 6 then topRow5 else topRow6))) else (if i.val < 11 then (if i.val < 9 then (if i.val < 8 then topRow7 else topRow8) else (if i.val < 10 then topRow9 else topRow10)) else (if i.val < 13 then (if i.val < 12 then topRow11 else topRow12) else (if i.val < 14 then topRow13 else topRow14)))) else (if i.val < 22 then (if i.val < 18 then (if i.val < 16 then topRow15 else (if i.val < 17 then topRow16 else topRow17)) else (if i.val < 20 then (if i.val < 19 then topRow18 else topRow19) else (if i.val < 21 then topRow20 else topRow21))) else (if i.val < 26 then (if i.val < 24 then (if i.val < 23 then topRow22 else topRow23) else (if i.val < 25 then topRow24 else topRow25)) else (if i.val < 28 then (if i.val < 27 then topRow26 else topRow27) else (if i.val < 29 then topRow28 else topRow29))))) else (if i.val < 45 then (if i.val < 37 then (if i.val < 33 then (if i.val < 31 then topRow30 else (if i.val < 32 then topRow31 else topRow32)) else (if i.val < 35 then (if i.val < 34 then topRow33 else topRow34) else (if i.val < 36 then topRow35 else topRow36))) else (if i.val < 41 then (if i.val < 39 then (if i.val < 38 then topRow37 else topRow38) else (if i.val < 40 then topRow39 else topRow40)) else (if i.val < 43 then (if i.val < 42 then topRow41 else topRow42) else (if i.val < 44 then topRow43 else topRow44)))) else (if i.val < 52 then (if i.val < 48 then (if i.val < 46 then topRow45 else (if i.val < 47 then topRow46 else topRow47)) else (if i.val < 50 then (if i.val < 49 then topRow48 else topRow49) else (if i.val < 51 then topRow50 else topRow51))) else (if i.val < 56 then (if i.val < 54 then (if i.val < 53 then topRow52 else topRow53) else (if i.val < 55 then topRow54 else topRow55)) else (if i.val < 58 then (if i.val < 57 then topRow56 else topRow57) else (if i.val < 59 then topRow58 else topRow59))))))

/-- The executable six-block action of the literal row group. -/
def pairTop : Source →* Equiv.Perm (Fin 6) where
  toFun x := topRows x.index
  map_one' := by decide +kernel
  map_mul' := by
    rintro ⟨i⟩ ⟨j⟩
    apply Equiv.ext
    intro p
    fin_cases i <;> fin_cases j <;> fin_cases p <;> decide +kernel
end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction147ClassPilot

end
