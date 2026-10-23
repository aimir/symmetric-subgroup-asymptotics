import SymmetricSubgroupAsymptotics.CFSGExceptionalGeckIntegralData
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveRootGenerators

/-! A selected twenty-one-root Heisenberg configuration in the actual
E6 integer lattice. The ten complementary pairs share a genuine central
sum. All other pairs commute by their integral Gram values. These are
small selected kernel certificates, not an exhaustive root census or an
assumed Heisenberg subgroup in the original group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGExceptionalHeisenbergRootPilot
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoCoordinatePositiveRootGenerators

structure RootConfig {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (m : ℕ) where
  x : Fin m→Fin r→ℤ
  y : Fin m→Fin r→ℤ
  z : Fin r→ℤ
  head : Fin r
  norm_x : ∀i,integerPairing A (x i) (x i)=2
  norm_y : ∀i,integerPairing A (y i) (y i)=2
  norm_z : integerPairing A z z=2
  positive_x : ∀i j,0≤x i j
  positive_y : ∀i j,0≤y i j
  positive_z : ∀j,0≤z j
  injective : Function.Injective (Sum.elim x y)
  grade_x : ∀i,x i head=1
  grade_y : ∀i,y i head=1
  grade_z : z head=2
  sum : ∀i,x i+y i=z
  paired : ∀i,integerPairing A (x i) (y i)= -1
  within_x : ∀i j,i≠j→integerPairing A (x i) (x j)=0 ∨ integerPairing A (x i) (x j)=1
  within_y : ∀i j,i≠j→integerPairing A (y i) (y j)=0 ∨ integerPairing A (y i) (y j)=1
  cross : ∀i j,i≠j→integerPairing A (x i) (y j)=0 ∨ integerPairing A (x i) (y j)=1
  central_x : ∀i,integerPairing A (x i) z=1
  central_y : ∀i,integerPairing A (y i) z=1

def RootConfig.xRoot {r m : ℕ} {A : Matrix (Fin r) (Fin r) ℤ}
    (C : RootConfig A m) (i : Fin m) : PositiveRoot A :=
  ⟨⟨C.x i,C.norm_x i⟩,C.positive_x i⟩

def RootConfig.yRoot {r m : ℕ} {A : Matrix (Fin r) (Fin r) ℤ}
    (C : RootConfig A m) (i : Fin m) : PositiveRoot A :=
  ⟨⟨C.y i,C.norm_y i⟩,C.positive_y i⟩

def RootConfig.zRoot {r m : ℕ} {A : Matrix (Fin r) (Fin r) ℤ}
    (C : RootConfig A m) : PositiveRoot A :=
  ⟨⟨C.z,C.norm_z⟩,C.positive_z⟩

theorem RootConfig.roots_injective {r m : ℕ} {A : Matrix (Fin r) (Fin r) ℤ}
    (C : RootConfig A m) : Function.Injective (Sum.elim C.xRoot C.yRoot) := by
  intro i j he
  apply C.injective
  cases i <;> cases j <;> exact congrArg (fun k:PositiveRoot A=>k.val.val) he

private def theta : Fin 6→ℤ := ![1,2,2,3,2,1]
private def lower : Fin 10→Fin 6→ℤ :=
  ![![0,1,0,0,0,0], ![0,1,0,1,0,0], ![0,1,0,1,1,0],
    ![0,1,0,1,1,1], ![0,1,1,1,0,0], ![0,1,1,1,1,0],
    ![0,1,1,1,1,1], ![0,1,1,2,1,0], ![0,1,1,2,1,1], ![0,1,1,2,2,1]]
private def upper (i:Fin 10) : Fin 6→ℤ := theta-lower i

def E6 : RootConfig CartanMatrix.E₆ 10 where
  x := lower
  y := upper
  z := theta
  head := 1
  norm_x := by decide
  norm_y := by decide
  norm_z := by decide
  positive_x := by decide
  positive_y := by decide
  positive_z := by decide
  injective := by decide
  grade_x := by decide
  grade_y := by decide
  grade_z := by decide
  sum := by decide
  paired := by decide
  within_x := by decide
  within_y := by decide
  cross := by decide
  central_x := by decide
  central_y := by decide

end SymmetricSubgroupAsymptotics.CFSGExceptionalHeisenbergRootPilot
