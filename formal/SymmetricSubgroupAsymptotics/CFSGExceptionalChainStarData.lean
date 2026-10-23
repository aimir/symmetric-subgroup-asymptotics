import SymmetricSubgroupAsymptotics.CFSGExceptionalGeckIntegralData
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveRootGenerators

/-! Selected A-chain prefixes in the actual exceptional integer root lattices.
Only two, three and five roots are used. The Gram and adjacent-string
certificates precede every field specialization; in particular no modular
root separation or source-faithfulness premise is built into this data. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGExceptionalChainStarData
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoCoordinatePositiveRootGenerators

structure ChainStar {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (n : ℕ) where
  row : Fin (n+1) → Fin r → ℤ
  step : Fin n → Fin r
  head : Fin r
  norm : ∀j, integerPairing A (row j) (row j)=2
  positive : ∀j i, 0≤row j i
  injective : Function.Injective row
  head_one : ∀j, row j head=1
  pair : ∀i j, i≠j → integerPairing A (row i) (row j)=1
  successor : ∀j, row j.succ=row j.castSucc+Pi.single (step j) 1
  simple_pair : ∀j k, integerPairing A (row k) (Pi.single (step j) 1)=
    if k=j.castSucc then -1 else if k=j.succ then 1 else 0

def ChainStar.root {r n : ℕ} {A : Matrix (Fin r) (Fin r) ℤ}
    (C : ChainStar A n) (j : Fin (n+1)) : PositiveRoot A :=
  ⟨⟨C.row j,C.norm j⟩,C.positive j⟩

theorem ChainStar.root_injective {r n : ℕ} {A : Matrix (Fin r) (Fin r) ℤ}
    (C : ChainStar A n) : Function.Injective C.root := by
  intro i j he
  exact C.injective (congrArg (fun k : PositiveRoot A=>k.val.val) he)

def E6 : ChainStar CartanMatrix.E₆ 1 where
  row := ![![1,0,0,0,0,0], ![1,0,1,0,0,0]]
  step := ![2]
  head := 0
  norm := by decide
  positive := by decide
  injective := by decide
  head_one := by decide
  pair := by decide
  successor := by decide
  simple_pair := by decide

def E7 : ChainStar CartanMatrix.E₇ 2 where
  row := ![![1,0,0,0,0,0,0], ![1,0,1,0,0,0,0], ![1,0,1,1,0,0,0]]
  step := ![2,3]
  head := 0
  norm := by decide
  positive := by decide
  injective := by decide
  head_one := by decide
  pair := by decide
  successor := by decide
  simple_pair := by decide

def E8 : ChainStar CartanMatrix.E₈ 4 where
  row := ![![1,0,0,0,0,0,0,0], ![1,0,1,0,0,0,0,0],
    ![1,0,1,1,0,0,0,0], ![1,0,1,1,1,0,0,0], ![1,0,1,1,1,1,0,0]]
  step := ![2,3,4,5]
  head := 0
  norm := by decide
  positive := by decide
  injective := by decide
  head_one := by decide
  pair := by decide
  successor := by decide
  simple_pair := by decide

end SymmetricSubgroupAsymptotics.CFSGExceptionalChainStarData
