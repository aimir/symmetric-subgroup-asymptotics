import SymmetricSubgroupAsymptotics.Selected1542SecondCenterData
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Selected1542QuotientStructure
def secondCenterRow (i : Fin 1024) : Prop :=
  (secondCenterInNormal i=true → ∃ n : Fin 8, ∀ p : Fin 16, secondCenterGrid i p=normalElements n p) ∧
  (secondCenterInNormal i=false →
    (∃ p : Fin 16, (secondCenterGrid i*secondCenterSchreier (secondCenterWitness i)) p≠
      (secondCenterSchreier (secondCenterWitness i)*secondCenterGrid i) p) ∧
    (∃ p : Fin 16, (secondCenterGrid i*secondCenterSchreier (secondCenterWitness i)) p≠
      (secondCenterZ*secondCenterSchreier (secondCenterWitness i)*secondCenterGrid i) p))
end SymmetricSubgroupAsymptotics.Selected1542QuotientStructure
