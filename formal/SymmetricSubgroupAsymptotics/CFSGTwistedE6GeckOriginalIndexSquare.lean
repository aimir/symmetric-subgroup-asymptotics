import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalHighestRootLine
import SymmetricSubgroupAsymptotics.CFSGFFourE6QuadraticCentralizerCapacity
import SymmetricSubgroupAsymptotics.CFSGHomRootFamilyCoverCardinality

/-! Least-index square for the ORIGINAL simple twisted E6 model.
The fixed-upper cardinal stays symbolic. Nine actual base-field root
parameters centralize every seed line, including all extension-field
points, and absorb the common 512-element menu even at q=2. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalIndexSquare
open CFSGTwistedE6GeckOriginalHighestRootLine CFSGTwistedE6GeckOriginalRootFamily
open CFSGTwistedE6GeckOriginalRootCentralizer CFSGTwistedE6GeckOriginalProjection
open CFSGTwistedE6GeckFixedPositiveProjection CFSGFFourE6QuadraticCentralizerCapacity
open CFSGTwistedE6GeckFixedRootFamilyCover CFSGHomRootFamilyCoverCardinality
open PrimitiveSocleRawStructure

theorem original_menu_centralizer_capacity (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (k : relativeRootMenu theta) :
    q.order^9 ≤ Nat.card (originalRootCentralizer q k.val) :=
  (quadratic_menu_matrix_centralizer_card_lower_nine q k).trans
    (matrixRootCentralizer_card_le_original q k.val)

theorem original_index_square (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.TwistedE6 q) ell) :
    ell^2 < Nat.card (CFSG.Models.TwistedE6 q) := by
  letI : Finite (CFSG.Models.TwistedE6 q) := original_finite q
  letI : Fintype (relativeRootMenu theta) := Fintype.ofFinite _
  have hq : 2 ≤ q.order := by
    rw [← q.card_field]
    exact Finite.one_lt_card
  have h512 : 512 ≤ q.order^9 := by
    calc
      512 = 2^9 := by decide
      _ ≤ q.order^9 := Nat.pow_le_pow_left hq 9
  apply least_index_square_lt (fixedPositiveToOriginal q)
    (fun k : relativeRootMenu theta => originalRootLine q k.val)
    (originalHighestRootLine q) (originalHighestRootLine_ne_bot q)
    (originalHighestRootLine_ne_top q) (q.order^9) (pow_pos (by omega) 9)
    ((original_root_menu_card_le theta).trans h512) _ _
    (fixedPositive_square_lt_original_order q) ell hell
  · intro g
    obtain ⟨k, u, he⟩ := original_highest_family_cover q g
    exact ⟨k, u, he.symm⟩
  · exact original_menu_centralizer_capacity q

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalIndexSquare
