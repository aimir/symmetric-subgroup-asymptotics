import SymmetricSubgroupAsymptotics.PrimeEvaluationKernelOrder
import SymmetricSubgroupAsymptotics.BinaryCarrierFormTransport16T1082
import SymmetricSubgroupAsymptotics.BinaryCarrierFormTransport16T1083
import SymmetricSubgroupAsymptotics.BinaryCarrierFormTransport16T1084
import SymmetricSubgroupAsymptotics.BinaryCarrierStarTransport16T1332
import SymmetricSubgroupAsymptotics.BinaryCarrierFormTransport16T1547

/-! Exact orders of the five original carrier closures. The quotient
coordinate maps are proved equivalences by the actual commutator forms;
combining their dimensions with the checked derived orders proves the
whole-group orders and p-group property without ambient enumeration. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

namespace BinaryCarrierExactOrder16T1082

abbrev Original := BinaryCarrierDerivedOrder16T1082.Original

theorem evaluation_finrank :
    Module.finrank (ZMod 2) (PrimeAbelianization 2 Original) = 6 := by
  simpa using BinaryCarrierFormTransport16T1082.generatorEquiv.finrank_eq.symm

theorem character_finrank :
    Module.finrank (ZMod 2) (PrimeCharacters 2 Original) = 6 := by
  simpa only [PrimeAbelianization, Subspace.dual_finrank_eq] using evaluation_finrank

theorem quotient_card : Nat.card (Original ⧸ commutator Original) = 2^6 := by
  rw [card_quotient_commutator_of_evaluationKernel_eq 2
    BinaryCarrierDerived16T1082.evaluationKernel_eq_commutator, character_finrank]

theorem original_card : Nat.card Original = 2^10 := by
  have h := card_eq_prime_pow_of_evaluationKernel_eq 2
    BinaryCarrierDerived16T1082.evaluationKernel_eq_commutator 4
    (show Nat.card (commutator Original) = 2^4 by
      simpa only [show (2 : ℕ)^4 = 16 from by decide] using
        BinaryCarrierDerivedOrder16T1082.card_commutator)
  rw [character_finrank] at h
  exact h

theorem original_isPGroup : IsPGroup 2 Original := IsPGroup.of_card original_card

end BinaryCarrierExactOrder16T1082

namespace BinaryCarrierExactOrder16T1083

abbrev Original := BinaryCarrierDerivedOrder16T1083.Original

theorem evaluation_finrank :
    Module.finrank (ZMod 2) (PrimeAbelianization 2 Original) = 6 := by
  simpa using BinaryCarrierFormTransport16T1083.generatorEquiv.finrank_eq.symm

theorem character_finrank :
    Module.finrank (ZMod 2) (PrimeCharacters 2 Original) = 6 := by
  simpa only [PrimeAbelianization, Subspace.dual_finrank_eq] using evaluation_finrank

theorem quotient_card : Nat.card (Original ⧸ commutator Original) = 2^6 := by
  rw [card_quotient_commutator_of_evaluationKernel_eq 2
    BinaryCarrierDerived16T1083.evaluationKernel_eq_commutator, character_finrank]

theorem original_card : Nat.card Original = 2^10 := by
  have h := card_eq_prime_pow_of_evaluationKernel_eq 2
    BinaryCarrierDerived16T1083.evaluationKernel_eq_commutator 4
    (show Nat.card (commutator Original) = 2^4 by
      simpa only [show (2 : ℕ)^4 = 16 from by decide] using
        BinaryCarrierDerivedOrder16T1083.card_commutator)
  rw [character_finrank] at h
  exact h

theorem original_isPGroup : IsPGroup 2 Original := IsPGroup.of_card original_card

end BinaryCarrierExactOrder16T1083

namespace BinaryCarrierExactOrder16T1084

abbrev Original := BinaryCarrierDerivedOrder16T1084.Original

theorem evaluation_finrank :
    Module.finrank (ZMod 2) (PrimeAbelianization 2 Original) = 6 := by
  simpa using BinaryCarrierFormTransport16T1084.generatorEquiv.finrank_eq.symm

theorem character_finrank :
    Module.finrank (ZMod 2) (PrimeCharacters 2 Original) = 6 := by
  simpa only [PrimeAbelianization, Subspace.dual_finrank_eq] using evaluation_finrank

theorem quotient_card : Nat.card (Original ⧸ commutator Original) = 2^6 := by
  rw [card_quotient_commutator_of_evaluationKernel_eq 2
    BinaryCarrierDerived16T1084.evaluationKernel_eq_commutator, character_finrank]

theorem original_card : Nat.card Original = 2^10 := by
  have h := card_eq_prime_pow_of_evaluationKernel_eq 2
    BinaryCarrierDerived16T1084.evaluationKernel_eq_commutator 4
    (show Nat.card (commutator Original) = 2^4 by
      simpa only [show (2 : ℕ)^4 = 16 from by decide] using
        BinaryCarrierDerivedOrder16T1084.card_commutator)
  rw [character_finrank] at h
  exact h

theorem original_isPGroup : IsPGroup 2 Original := IsPGroup.of_card original_card

end BinaryCarrierExactOrder16T1084

namespace BinaryCarrierExactOrder16T1332

abbrev Original := BinaryCarrierDerivedOrder16T1332.Original

theorem evaluation_finrank :
    Module.finrank (ZMod 2) (PrimeAbelianization 2 Original) = 5 := by
  simpa using BinaryCarrierStarTransport16T1332.generatorEquiv.finrank_eq.symm

theorem character_finrank :
    Module.finrank (ZMod 2) (PrimeCharacters 2 Original) = 5 := by
  simpa only [PrimeAbelianization, Subspace.dual_finrank_eq] using evaluation_finrank

theorem quotient_card : Nat.card (Original ⧸ commutator Original) = 2^5 := by
  rw [card_quotient_commutator_of_evaluationKernel_eq 2
    BinaryCarrierDerived16T1332.evaluationKernel_eq_commutator, character_finrank]

theorem original_card : Nat.card Original = 2^11 := by
  have h := card_eq_prime_pow_of_evaluationKernel_eq 2
    BinaryCarrierDerived16T1332.evaluationKernel_eq_commutator 6
    (show Nat.card (commutator Original) = 2^6 by
      simpa only [show (2 : ℕ)^6 = 64 from by decide] using
        BinaryCarrierDerivedOrder16T1332.card_commutator)
  rw [character_finrank] at h
  exact h

theorem original_isPGroup : IsPGroup 2 Original := IsPGroup.of_card original_card

end BinaryCarrierExactOrder16T1332

namespace BinaryCarrierExactOrder16T1547

abbrev Original := BinaryCarrierDerivedOrder16T1547.Original

theorem evaluation_finrank :
    Module.finrank (ZMod 2) (PrimeAbelianization 2 Original) = 6 := by
  simpa using BinaryCarrierFormTransport16T1547.generatorEquiv.finrank_eq.symm

theorem character_finrank :
    Module.finrank (ZMod 2) (PrimeCharacters 2 Original) = 6 := by
  simpa only [PrimeAbelianization, Subspace.dual_finrank_eq] using evaluation_finrank

theorem quotient_card : Nat.card (Original ⧸ commutator Original) = 2^6 := by
  rw [card_quotient_commutator_of_evaluationKernel_eq 2
    BinaryCarrierDerived16T1547.evaluationKernel_eq_commutator, character_finrank]

theorem original_card : Nat.card Original = 2^12 := by
  have h := card_eq_prime_pow_of_evaluationKernel_eq 2
    BinaryCarrierDerived16T1547.evaluationKernel_eq_commutator 6
    (show Nat.card (commutator Original) = 2^6 by
      simpa only [show (2 : ℕ)^6 = 64 from by decide] using
        BinaryCarrierDerivedOrder16T1547.card_commutator)
  rw [character_finrank] at h
  exact h

theorem original_isPGroup : IsPGroup 2 Original := IsPGroup.of_card original_card

end BinaryCarrierExactOrder16T1547

end SymmetricSubgroupAsymptotics
