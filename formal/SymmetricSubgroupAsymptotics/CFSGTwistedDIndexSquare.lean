import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeOrderRecurrence
import SymmetricSubgroupAsymptotics.CFSGTwistedDIndexPointUpper
import SymmetricSubgroupAsymptotics.CFSGTwistedDIndexNumerics

/-! The squared least-index inequality for the SAME original twisted-D
model in every classified rank. Actual fixed-vector orbits and two
root-word hyperbolic-frame charts supply both quantitative bounds;
no classical order formula or outer-automorphism bound is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDIndexSquare
open CFSGTwistedDRelativeElementaryGroup CFSGTwistedDRelativeProjectiveModel
open CFSGTwistedDRelativeOrderRecurrence CFSGTwistedDIndexPointUpper
open PrimitiveSocleRawStructure

theorem relative_projective_card_lower (s : ℕ) (q : CFSG.PrimePower) :
    q.order ^ (8 * s + 20) ≤
      Nat.card (Subgroup.center (relativeRootGroup (s + 2) q)) *
        Nat.card (relativeRootGroup (s + 2) q ⧸ Subgroup.center (relativeRootGroup (s + 2) q)) :=
  (relative_card_two_steps s q).trans_eq
    (Subgroup.center (relativeRootGroup (s + 2) q)).card_mul_index.symm

theorem relative_leastProperIndex_square_lt_card (s : ℕ) (q : CFSG.PrimePower) (ell : ℕ)
    (hell : LeastProperIndex
      (relativeRootGroup (s + 2) q ⧸ Subgroup.center (relativeRootGroup (s + 2) q)) ell) :
    ell ^ 2 <
      Nat.card (relativeRootGroup (s + 2) q ⧸ Subgroup.center (relativeRootGroup (s + 2) q)) :=
  CFSGTwistedDIndexNumerics.square_lt_of_frame_lower q.order s ell _ _
    (CFSGTwistedAQuadraticTrace.order_two_le q) (relative_center_card_le_two s q)
    (relative_leastProperIndex_le s q ell hell) (relative_projective_card_lower s q)

theorem original_leastProperIndex_square_lt_card (s : ℕ) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedD (s + 4) q)] (ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.TwistedD (s + 4) q) ell) :
    ell ^ 2 < Nat.card (CFSG.Models.TwistedD (s + 4) q) := by
  let e := originalRelativeProjectiveEquiv s q
  have h := relative_leastProperIndex_square_lt_card s q ell
    (CFSGReduction.leastProperIndex_of_mulEquiv e ell hell)
  simpa only [Nat.card_congr e.toEquiv] using h

end SymmetricSubgroupAsymptotics.CFSGTwistedDIndexSquare

namespace SymmetricSubgroupAsymptotics.CFSGReduction
open PrimitiveSocleRawStructure

theorem typeTwistedD_leastProperIndex_square_lt_card (r : ℕ) (q : CFSG.PrimePower)
    (hr : 4 ≤ r) [IsSimpleGroup (CFSG.Models.TwistedD r q)] (ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.TwistedD r q) ell) :
    ell ^ 2 < Nat.card (CFSG.Models.TwistedD r q) := by
  obtain ⟨s, rfl⟩ : ∃ s : ℕ, r = s + 4 := ⟨r - 4, by omega⟩
  exact CFSGTwistedDIndexSquare.original_leastProperIndex_square_lt_card s q ell hell

end SymmetricSubgroupAsymptotics.CFSGReduction
