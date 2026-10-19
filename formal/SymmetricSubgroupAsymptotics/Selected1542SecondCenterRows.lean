import SymmetricSubgroupAsymptotics.Selected1542SecondCenterRows00
import SymmetricSubgroupAsymptotics.Selected1542SecondCenterRows01
import SymmetricSubgroupAsymptotics.Selected1542SecondCenterRows02
import SymmetricSubgroupAsymptotics.Selected1542SecondCenterRows03
import SymmetricSubgroupAsymptotics.Selected1542SecondCenterRows04
import SymmetricSubgroupAsymptotics.Selected1542SecondCenterRows05
import SymmetricSubgroupAsymptotics.Selected1542SecondCenterRows06
import SymmetricSubgroupAsymptotics.Selected1542SecondCenterRows07
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Selected1542QuotientStructure
private theorem assemble (Q : Fin 1024 → Prop)
    (h0 : ∀ r : Fin 128, Q (finProdFinEquiv ((0 : Fin 8),r)))
    (h1 : ∀ r : Fin 128, Q (finProdFinEquiv ((1 : Fin 8),r)))
    (h2 : ∀ r : Fin 128, Q (finProdFinEquiv ((2 : Fin 8),r)))
    (h3 : ∀ r : Fin 128, Q (finProdFinEquiv ((3 : Fin 8),r)))
    (h4 : ∀ r : Fin 128, Q (finProdFinEquiv ((4 : Fin 8),r)))
    (h5 : ∀ r : Fin 128, Q (finProdFinEquiv ((5 : Fin 8),r)))
    (h6 : ∀ r : Fin 128, Q (finProdFinEquiv ((6 : Fin 8),r)))
    (h7 : ∀ r : Fin 128, Q (finProdFinEquiv ((7 : Fin 8),r)))
    (i : Fin 1024) : Q i := by
  obtain ⟨⟨k,r⟩,rfl⟩ := (finProdFinEquiv : Fin 8 × Fin 128 ≃ Fin 1024).surjective i
  fin_cases k
  · exact h0 r
  · exact h1 r
  · exact h2 r
  · exact h3 r
  · exact h4 r
  · exact h5 r
  · exact h6 r
  · exact h7 r

theorem secondCenter_all_rows (i : Fin 1024) : secondCenterRow i :=
  assemble secondCenterRow secondCenterRows00 secondCenterRows01 secondCenterRows02 secondCenterRows03 secondCenterRows04 secondCenterRows05 secondCenterRows06 secondCenterRows07 i
end SymmetricSubgroupAsymptotics.Selected1542QuotientStructure
