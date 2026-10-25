import SymmetricSubgroupAsymptotics.CFSGSLTwoPrimeIndexLower
import SymmetricSubgroupAsymptotics.CFSGPSLTwoRootCoordinates
import SymmetricSubgroupAsymptotics.ClassicalClassEquationSmallParameters

/-! The checked SL2 characteristic-prime index bound transfers through
the actual FULL central quotient. No simplicity or subgroup recognition
is needed. Prime fields therefore pay their full field order. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGPSLTwoCharacteristicIndex
open CFSGPSLTwoRootCoordinates

theorem prime_le_proper_index (q : CFSG.PrimePower)
    (H : Subgroup (CFSG.Models.A 1 q)) (hH : H≠⊤) : q.prime≤H.index := by
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  have hpre : H.comap (projection (F:=q.Field))≠⊤ := by
    intro ht
    apply hH
    apply top_unique
    intro x _
    obtain ⟨g,rfl⟩ := projection_surjective (F:=q.Field) x
    have hg : g∈H.comap (projection (F:=q.Field)) := by rw [ht]; trivial
    exact hg
  have hh := CFSGSLTwoPrimeIndexLower.prime_le_proper_index (K:=q.Field) q.prime
    (H.comap (projection (F:=q.Field))) hpre
  rw [H.index_comap_of_surjective (projection_surjective (F:=q.Field))] at hh
  exact hh

theorem field_le_proper_index_of_prime_order (q : CFSG.PrimePower)
    (hq : q.order.Prime) (H : Subgroup (CFSG.Models.A 1 q)) (hH : H≠⊤) :
    q.order≤H.index := by
  have he := ClassicalClassEquationCapacity.exponent_eq_one_of_prime_order q hq
  have horder : q.order=q.prime := by change q.prime^q.exponent=q.prime; rw [he,pow_one]
  rw [horder]
  exact prime_le_proper_index q H hH

end SymmetricSubgroupAsymptotics.CFSGPSLTwoCharacteristicIndex
