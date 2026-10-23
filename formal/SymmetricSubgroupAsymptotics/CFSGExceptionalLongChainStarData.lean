import SymmetricSubgroupAsymptotics.CFSGExceptionalChainStarData

/-! The longest literal A-chain prefixes in E6/E7/E8. These small
integral certificates reuse the proved chain-star action machinery and
increase the parameter dimensions to five, six and seven. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGExceptionalLongChainStarData
open CFSGExceptionalChainStarData

def E6 : ChainStar CartanMatrix.E₆ 4 where
  row := ![![1,0,0,0,0,0], ![1,0,1,0,0,0], ![1,0,1,1,0,0],
    ![1,0,1,1,1,0], ![1,0,1,1,1,1]]
  step := ![2,3,4,5]
  head := 0
  norm := by decide
  positive := by decide
  injective := by decide
  head_one := by decide
  pair := by decide
  successor := by decide
  simple_pair := by decide

def E7 : ChainStar CartanMatrix.E₇ 5 where
  row := ![![1,0,0,0,0,0,0], ![1,0,1,0,0,0,0], ![1,0,1,1,0,0,0],
    ![1,0,1,1,1,0,0], ![1,0,1,1,1,1,0], ![1,0,1,1,1,1,1]]
  step := ![2,3,4,5,6]
  head := 0
  norm := by decide
  positive := by decide
  injective := by decide
  head_one := by decide
  pair := by decide
  successor := by decide
  simple_pair := by decide

def E8 : ChainStar CartanMatrix.E₈ 6 where
  row := ![![1,0,0,0,0,0,0,0], ![1,0,1,0,0,0,0,0], ![1,0,1,1,0,0,0,0],
    ![1,0,1,1,1,0,0,0], ![1,0,1,1,1,1,0,0], ![1,0,1,1,1,1,1,0], ![1,0,1,1,1,1,1,1]]
  step := ![2,3,4,5,6,7]
  head := 0
  norm := by decide
  positive := by decide
  injective := by decide
  head_one := by decide
  pair := by decide
  successor := by decide
  simple_pair := by decide

end SymmetricSubgroupAsymptotics.CFSGExceptionalLongChainStarData
