import SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalHighestRootLine
import SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalRootCentralizer
import SymmetricSubgroupAsymptotics.CFSGFFourE6RestrictedCentralizerCapacity
import SymmetricSubgroupAsymptotics.CFSGHomRootFamilyCoverCardinality

/-! The least proper subgroup index of the ORIGINAL simple F4 model
has square strictly below its order. The actual fixed-upper family has
at most 512 seeds, each with nine independent field parameters in its
literal centralizer. The full upper cardinal remains symbolic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalIndexSquare
open CFSGFFourE6OriginalHighestRootLine CFSGFFourE6OriginalRootFamily
open CFSGFFourE6OriginalRootCentralizer CFSGFFourE6OriginalProjection
open CFSGFFourE6FixedPositiveProjection CFSGFFourE6RestrictedCentralizerCapacity
open CFSGFFourE6CentralizerRootTransport CFSGTwistedE6GeckFixedRootFamilyCover
open CFSGHomRootFamilyCoverCardinality PrimitiveSocleRawStructure CFSG.Models.Chevalley

theorem original_menu_centralizer_capacity (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)]
    (k : relativeRootMenu theta) :
    Nat.card K^9 ≤ Nat.card (originalRootCentralizer K p k.val) := by
  apply le_trans _ (matrixRootCentralizer_card_le_original K p k.val)
  obtain ⟨r, hr⟩ := k.property
  change Nat.card K^9 ≤ Nat.card (fixedRootCentralizer K (RingEquiv.refl K) k.val)
  rw [← hr]
  exact fixed_root_centralizer_card_lower_nine (RingHom.id K) (RingEquiv.refl K)
    (fun _ => rfl) r

theorem original_index_square (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)]
    (ell : ℕ) (hell : LeastProperIndex (Projective CartanMatrix.F₄ K) ell) :
    ell^2 < Nat.card (Projective CartanMatrix.F₄ K) := by
  letI : Finite (Projective CartanMatrix.F₄ K) := original_finite K
  letI : Fintype (relativeRootMenu theta) := Fintype.ofFinite _
  have h512 : 512 ≤ Nat.card K^9 := by
    calc
      512 = 2^9 := by decide
      _ ≤ Nat.card K^9 := Nat.pow_le_pow_left (Finite.one_lt_card (α := K)) 9
  apply least_index_square_lt (fixedPositiveToOriginal K p)
    (fun k : relativeRootMenu theta => originalRootLine K k.val)
    (originalHighestRootLine K) (originalHighestRootLine_ne_bot K p)
    (originalHighestRootLine_ne_top K p) (Nat.card K^9)
    (pow_pos (Nat.card_pos (α := K)) 9)
    ((original_root_menu_card_le theta).trans h512) _ _
    (fixedPositive_square_lt_original_order K p) ell hell
  · intro g
    obtain ⟨k, u, he⟩ := original_highest_family_cover K p g
    exact ⟨k, u, he.symm⟩
  · exact original_menu_centralizer_capacity K p

end SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalIndexSquare
