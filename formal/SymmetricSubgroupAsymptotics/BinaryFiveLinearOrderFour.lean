import SymmetricSubgroupAsymptotics.CFSGTypeAElementaryMatrices
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! One literal upper-unitriangular word of order four in GL5(F2).
Only its selected matrix entries are reduced; the group is not enumerated. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.BinaryFiveLinearOrderFour
open CFSGTypeAElementaryMatrices

abbrev General := Matrix.GeneralLinearGroup (Fin 5) (ZMod 2)

def element : General := Matrix.SpecialLinearGroup.toGL
  (elementary (show (0 : Fin 5)≠1 by decide) (1 : ZMod 2) *
    elementary (show (1 : Fin 5)≠2 by decide) (1 : ZMod 2))

theorem fourth_power : element^4=1 := by
  apply Units.ext
  change ((Matrix.transvection (0 : Fin 5) 1 (1 : ZMod 2)) *
    Matrix.transvection 1 2 1)^4 = 1
  decide +kernel

theorem square_ne_one : element^2≠1 := by
  intro h
  have hh := congrArg (fun a : General =>
    (a : Matrix (Fin 5) (Fin 5) (ZMod 2)) 0 2) h
  have hv : (((Matrix.transvection (0 : Fin 5) 1 (1 : ZMod 2)) *
      Matrix.transvection 1 2 1)^2 : Matrix (Fin 5) (Fin 5) (ZMod 2)) 0 2 ≠
      (1 : Matrix (Fin 5) (Fin 5) (ZMod 2)) 0 2 := by decide +kernel
  exact hv hh

theorem order_four : orderOf element=4 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by decide) fourth_power
  intro p hp hpd
  have hd : p∣2 := hp.dvd_of_dvd_pow (show p∣2^2 by simpa using hpd)
  have hp2 : p=2 := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2)).mp hd
  subst p
  exact square_ne_one

end SymmetricSubgroupAsymptotics.BinaryFiveLinearOrderFour
