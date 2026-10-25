import SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleTwoOrbits
import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalProjectiveNaturalEquivalence
import SymmetricSubgroupAsymptotics.CFSGConjugateSubgroupDegree
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawSimpleIndex
import Mathlib.Data.Nat.Prime.Int

/-! The actual two-source orbit bound acts on the SAME original G2
central quotient. Its checked Model equivalence supplies honest moved
root parameters; simplicity is used only for moved cosets of a proper
subgroup. No finite action census or automorphism lift is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleIndex
open CFSG.Models.Chevalley CFSGGTwoOriginalNaturalEquivalence
open CFSGGTwoOriginalProjectiveNaturalEquivalence
open CFSGGTwoOriginalPositiveRootWords
open CFSGGTwoCharacteristicThreeMiddleExchange
open CFSGGTwoCharacteristicThreeMiddleTwoOrbits
variable (K : Type) [Field K] [Finite K] [CharP K 3]

def modelEquivOriginal (hcard : Nat.card K = 3) :
    Model CartanMatrix.G₂ K ≃* Projective CartanMatrix.G₂ K :=
  (modelEquivNatural K).trans (projectiveEquivNatural K (by omega)).symm

theorem field_three_le_proper_index (hcard : Nat.card K = 3)
    [IsSimpleGroup (Projective CartanMatrix.G₂ K)]
    (H : Subgroup (Projective CartanMatrix.G₂ K)) (hH : H ≠ ⊤) : 54 ≤ H.index := by
  let e := modelEquivOriginal K hcard
  letI : Finite (Model CartanMatrix.G₂ K) :=
    Finite.of_injective (modelEquivNatural K) (modelEquivNatural K).injective
  letI : Finite (Projective CartanMatrix.G₂ K) := Finite.of_equiv (Model CartanMatrix.G₂ K) e.toEquiv
  have hne (j : Fin 6) : e (positiveModel K j 1) ≠ 1 := by
    intro he
    exact positive_one_ne_one K j (e.injective (he.trans (map_one e).symm))
  obtain ⟨x,hx⟩ := CFSGConjugateSubgroupDegree.exists_moved_coset_of_ne_one
    H hH (e (positiveModel K 5 1)) (hne 5)
  obtain ⟨y,hy⟩ := CFSGConjugateSubgroupDegree.exists_moved_coset_of_ne_one
    H hH (e (positiveModel K 3 1)) (hne 3)
  letI : MulAction (Model CartanMatrix.G₂ K) (Projective CartanMatrix.G₂ K ⧸ H) :=
    MulAction.compHom _ e.toMonoidHom
  exact degree_ge_fiftyFour K hcard ⟨x,hx⟩ ⟨y,hy⟩

theorem typeGTwo_field_three_le_proper_index (q : CFSG.PrimePower) (hq : q.order = 3)
    [IsSimpleGroup (CFSG.Models.G2 q)]
    (H : Subgroup (CFSG.Models.G2 q)) (hH : H ≠ ⊤) : 54 ≤ H.index := by
  have hp : q.prime = 3 :=
    (Nat.Prime.pow_inj' q.prime_isPrime (by decide : Nat.Prime 3)
      q.exponent_pos.ne' (by decide : (1 : ℕ) ≠ 0)
      (show q.prime^q.exponent = 3^1 from hq)).1
  letI : CharP q.Field 3 := by rw [←hp]; infer_instance
  have hc : Nat.card q.Field = 3 := q.card_field.trans hq
  exact field_three_le_proper_index q.Field hc H hH

end SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleIndex
