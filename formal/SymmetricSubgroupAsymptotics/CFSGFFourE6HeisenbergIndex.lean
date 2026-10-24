import SymmetricSubgroupAsymptotics.CFSGFFourE6HeisenbergEmbedding
import SymmetricSubgroupAsymptotics.CFSGHeisenbergFiniteFieldIndex

/-! The actual four-pair Heisenberg subgroup gives p*q^4 as a lower
bound for every proper index of the original F4 model. The coset action
is the original simple group's action, and its Heisenberg stabilizer is
only restricted to the prime field. The same faithful subgroup also
gives the order lower bound q^9 needed in the power degree form. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6HeisenbergIndex
open CFSGHeisenbergCoordinateGroup CFSGHeisenbergFiniteFieldIndex
open CFSGFFourE6HeisenbergEmbedding CFSGFFourE6OriginalProjection
open CFSG.Models.Chevalley

theorem card_nine_le_original_order (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective CartanMatrix.F₄ K)] :
    Nat.card K ^ 9 ≤ Nat.card (Projective CartanMatrix.F₄ K) := by
  letI : Finite (Projective CartanMatrix.F₄ K) := original_finite K
  have hb := Nat.card_le_card_of_injective (originalHom K p) (originalHom_injective K p)
  simpa only [CFSGHeisenbergCoordinateGroup.card] using hb

theorem prime_mul_card_four_le_proper_index (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective CartanMatrix.F₄ K)]
    (H : Subgroup (Projective CartanMatrix.F₄ K)) (hH : H ≠ ⊤) :
    p * Nat.card K ^ 4 ≤ H.index := by
  letI : Finite (Projective CartanMatrix.F₄ K) := original_finite K
  let f := originalHom K p
  let c : Multiplicative K := Multiplicative.ofAdd 1
  have hc : (central (K := K) (m := 4)) c ≠ 1 := by
    intro he
    have hh : c = 1 := central_injective
      (he.trans (map_one (central (K := K) (m := 4))).symm)
    exact one_ne_zero (congrArg (fun z : Multiplicative K => z.toAdd) hh)
  have hfc : f ((central (K := K) (m := 4)) c) ≠ 1 := by
    intro he
    exact hc (originalHom_injective K p (he.trans (map_one f).symm))
  obtain ⟨x, hx⟩ := CFSGConjugateSubgroupDegree.exists_moved_coset_of_ne_one H hH _ hfc
  letI : MulAction (Element K 4) (Projective CartanMatrix.F₄ K ⧸ H) :=
    MulAction.compHom _ f
  have hb := degree_le_of_central_motion (K := K) (m := 4) p x c hx
  simpa only [Subgroup.index_eq_card] using hb

theorem typeFFour_order_nine_le (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.F4 q)] :
    q.order ^ 9 ≤ Nat.card (CFSG.Models.F4 q) := by
  have hb := card_nine_le_original_order q.Field q.prime
  simpa only [q.card_field] using hb

theorem typeFFour_heisenberg_le_proper_index (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.F4 q)]
    (H : Subgroup (CFSG.Models.F4 q)) (hH : H ≠ ⊤) :
    q.prime * q.order ^ 4 ≤ H.index := by
  have hb := prime_mul_card_four_le_proper_index q.Field q.prime H hH
  simpa only [q.card_field] using hb

end SymmetricSubgroupAsymptotics.CFSGFFourE6HeisenbergIndex
