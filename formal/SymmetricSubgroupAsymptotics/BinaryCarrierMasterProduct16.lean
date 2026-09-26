import SymmetricSubgroupAsymptotics.BinaryCarrierTerminalFamily
import SymmetricSubgroupAsymptotics.BinaryCarrierMasterTerminal16

/-! A reserve for actual subgroups of the fixed original critical-plus-
master product. The exact tail equivalence removes the fibre presentation
without changing any physical profile normalizer or original survival test.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.BinaryCarrierMasterWords16

open BinaryCarrierWord

/-- Count the actual original product subgroups. Fullness is required on
each carrier and each nonabelian critical factor, not on the whole critical
product. Any extra regular-factor fullness or survival is retained in P. -/
theorem terminal_product_subgroups_le_reserve
    {ι : Type} [Fintype ι] (a : ℕ) (s : ι → Bool)
    (masters : List Master)
    (P : Subgroup (CriticalProductGroup a s × Product (word masters)) → Prop) :
    (Nat.card (TerminalProductFamily a s (word masters) P) : ℝ) ≤
      (((binaryStructuredOrderConstant 12 *
        (12*masters.length+2)^(binaryStructuredOrderConstant 12) : ℕ) : ℝ)^masters.length) *
        (((eulerProduct⁻¹)^3 * ((criticalProductRank a s+1 : ℕ) : ℝ) *
          (∑ ell ∈ Finset.range (Fintype.card ι+1), (72 : ℝ)^ell)) *
            ((2 : ℝ)^(4096*masters.length) *
              (2 : ℝ)^(((criticalProductRank a s : ℝ)+4*(2*(masters.length : ℝ)))^2/4 -
                (25/82)*(criticalProductRank a s)*(2*(masters.length : ℝ)) -
                (29/164)*(2*(masters.length : ℝ))^2))) := by
  rw [terminalProductFamily_card_real]
  exact terminal_subfamilies_le_reserve a s masters
    (fun H J => P (J.map (SubdirectTailImage.inclusion H.1)))

end SymmetricSubgroupAsymptotics.BinaryCarrierMasterWords16
