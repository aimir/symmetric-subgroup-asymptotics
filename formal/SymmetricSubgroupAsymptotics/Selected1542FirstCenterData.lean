import SymmetricSubgroupAsymptotics.Selected1542QuotientStructureData
import SymmetricSubgroupAsymptotics.Selected1542TargetLocalGenerators
import SymmetricSubgroupAsymptotics.NaturalA4ScalarFourHead
import SymmetricSubgroupAsymptotics.OrbitWordCentralizer
set_option autoImplicit false
set_option maxRecDepth 8192
noncomputable section
namespace SymmetricSubgroupAsymptotics.Selected1542QuotientStructure
def firstCenterSourceWord (j : Fin 9) : List (Fin 6) := (#[[0, 3], [1], [2, 5], [0, 0, 5], [0, 1, 3], [0, 2], [2, 0], [2, 1, 5], [2, 2, 3]] : Array (List (Fin 6)))[j.val]!
def firstCenterGenerator (j : Fin 9) : Equiv.Perm (Fin 16) := ((firstCenterSourceWord j).map signedSource).prod
def firstCenterOrbitWord (i : Fin 16) : List (Fin 9) := (#[[], [3, 1], [4], [5], [5, 3], [7], [3], [7, 4], [1, 1], [8, 4], [1, 7], [7, 3], [5, 1], [4, 1], [1], [6]] : Array (List (Fin 9)))[i.val]!
def firstCenterZ : Equiv.Perm (Fin 16) := preimageElements 26
def firstCenterCubicLetter (i : Fin 6) : CyclicThree :=
  if h : i.val<3 then NaturalA4ScalarFourHead.top (alternatingGenerator ⟨i.val,h⟩ 0)
  else (NaturalA4ScalarFourHead.top (alternatingGenerator ⟨i.val-3,by omega⟩ 0))⁻¹
end SymmetricSubgroupAsymptotics.Selected1542QuotientStructure
