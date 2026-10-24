import SymmetricSubgroupAsymptotics.CFSGTwistedE6FixedHeisenbergEmbedding
import SymmetricSubgroupAsymptotics.CFSGHeisenbergFiniteFieldIndex

/-! Every proper subgroup of the SAME original twisted-E6 model has
index at least p*q^10.  The actual nonzero central root coordinate moves
a coset by inherited simplicity; the Heisenberg isotropy bound uses
only prime-field annihilators of the actual stabilizer. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6HeisenbergIndex
open CFSGSerreOrdinaryTwists CFSGTwistedA2FixedField
open CFSGHeisenbergCoordinateGroup CFSGHeisenbergFiniteFieldIndex
open CFSGTwistedE6HeisenbergCoordinateTwist CFSGQuadraticSignedFixedCoordinates
open CFSGTwistedE6FixedHeisenbergEmbedding
open CFSGTwistedE6GeckOriginalProjection
local instance (q : CFSG.PrimePower) : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
local instance (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TwistedE6 q)] :
    Finite (CFSG.Models.TwistedE6 q) := original_finite q

theorem prime_mul_order_ten_le_proper_index (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)]
    (H : Subgroup (CFSG.Models.TwistedE6 q)) (hH : H ≠ ⊤) :
    q.prime * q.order ^ 10 ≤ H.index := by
  obtain ⟨delta, hdelta⟩ := exists_signed_nonzero q centralWeight centralWeight_unit
  let f := originalHom q delta hdelta
  let c : Multiplicative (fixedField q) := Multiplicative.ofAdd 1
  have hc : (central (K := fixedField q) (m := 10)) c ≠ 1 := by
    intro he
    have hh : c = 1 := central_injective
      (he.trans (map_one (central (K := fixedField q) (m := 10))).symm)
    exact one_ne_zero (congrArg (fun z : Multiplicative (fixedField q) => z.toAdd) hh)
  have hfc : f ((central (K := fixedField q) (m := 10)) c) ≠ 1 := by
    intro he
    exact hc (originalHom_injective q delta hdelta (he.trans (map_one f).symm))
  obtain ⟨x, hx⟩ := CFSGConjugateSubgroupDegree.exists_moved_coset_of_ne_one H hH _ hfc
  letI : MulAction (Element (fixedField q) 10) (CFSG.Models.TwistedE6 q ⧸ H) :=
    MulAction.compHom _ f
  have hb := degree_le_of_central_motion (K := fixedField q) (m := 10) q.prime x c hx
  simpa only [fixedField_card, Subgroup.index_eq_card] using hb

theorem proper_index_ge_2048 (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)]
    (H : Subgroup (CFSG.Models.TwistedE6 q)) (hH : H ≠ ⊤) : 2048 ≤ H.index := by
  calc
    2048 = 2 * 2 ^ 10 := by decide
    _ ≤ q.prime * q.order ^ 10 := Nat.mul_le_mul q.prime_isPrime.two_le
      (Nat.pow_le_pow_left (CFSGTwistedAQuadraticTrace.order_two_le q) 10)
    _ ≤ H.index := prime_mul_order_ten_le_proper_index q H hH

end SymmetricSubgroupAsymptotics.CFSGTwistedE6HeisenbergIndex
