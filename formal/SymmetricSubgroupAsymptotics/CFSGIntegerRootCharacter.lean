import SymmetricSubgroupAsymptotics.CFSGIntegerMatrixPairing
import SymmetricSubgroupAsymptotics.CFSGIntegerMatrixPowerHom

/-! Root characters of a product torus, on the integral root lattice.
These identities concern only bilinear pairings and commutative groups. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGIntegerRootCharacter
open CFSGIntegerMatrixPairing CFSGIntegerMatrixPowerHom
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {G : Type*} [CommGroup G]

def character (A : Matrix I I ℤ) (x : I → G) (v : I → ℤ) : G :=
  ∏ i,x i ^ integerPairing A (Pi.single i 1) v

theorem character_add (A : Matrix I I ℤ) (x : I → G) (v w : I → ℤ) :
    character A x (v+w)=character A x v*character A x w := by
  simp only [character,map_add,zpow_add,Finset.prod_mul_distrib]

theorem character_zero (A : Matrix I I ℤ) (x : I → G) : character A x 0=1 := by
  simp only [character,map_zero,zpow_zero,Finset.prod_const_one]

theorem character_single (A : Matrix I I ℤ) (hs : A.transpose=A)
    (x : I → G) (j : I) :
    character A x (Pi.single j 1)=powerHom A x j := by
  apply Finset.prod_congr rfl
  intro i hi
  congr 1
  change A.toBilin' (Pi.single i 1) (Pi.single j 1)=A j i
  rw [Matrix.toBilin'_single]
  exact congrFun (congrFun hs j) i

end SymmetricSubgroupAsymptotics.CFSGIntegerRootCharacter
