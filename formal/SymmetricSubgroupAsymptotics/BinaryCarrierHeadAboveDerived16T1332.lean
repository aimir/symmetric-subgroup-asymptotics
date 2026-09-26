import SymmetricSubgroupAsymptotics.BinaryCarrierStarTransport16T1332
import SymmetricSubgroupAsymptotics.PrimeDerivedStarHead

/-! Every original 16T1332 normal subgroup above its actual derived
subgroup obeys the uniform star-family bound. This does not claim coverage
of the remaining normal axes or of physical weighted carrier rows. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryCarrierHeadAboveDerived16T1332

abbrev Original := BinaryCarrierDerivedOrder16T1332.Original

private abbrev kernelIdentity := BinaryCarrierDerived16T1332.evaluationKernel_eq_commutator

theorem head_le_max_four_image (N : Subgroup Original) [N.Normal]
    (hDN : commutator Original ≤ N) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) ≤
      max 4 (Module.finrank (ZMod 2) (primeDerivedImage 2 N)) := by
  simpa [BinaryCarrierStarTransport16T1332.U] using
    primeRelativeHead_above_derived_le_max_of_star 2 kernelIdentity
      BinaryCarrierStarTransport16T1332.characterEquiv
      BinaryCarrierStarTransport16T1332.evaluationEquiv
      BinaryCarrierStarTransport16T1332.actual_form_eq_star N hDN

theorem head_le_max_four_log_quotient (N : Subgroup Original) [N.Normal]
    (hDN : commutator Original ≤ N) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) ≤
      max 4 (Nat.log 2 (Nat.card (normalChainQuotient (commutator Original) N))) := by
  rw [derivedNormalImage_log_card 2 kernelIdentity N]
  exact head_le_max_four_image N hDN

theorem head_le_max_four_log_div_sixtyfour (N : Subgroup Original) [N.Normal]
    (hDN : commutator Original ≤ N) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) ≤
      max 4 (Nat.log 2 (Nat.card N / 64)) := by
  have hc := normalChainQuotient_card_mul (commutator Original) N hDN
  rw [BinaryCarrierDerivedOrder16T1332.card_commutator] at hc
  have hQ : Nat.card (normalChainQuotient (commutator Original) N) = Nat.card N / 64 := by
    rw [← hc, Nat.mul_div_cancel _ (by decide : 0 < (64 : ℕ))]
  rw [← hQ]
  exact head_le_max_four_log_quotient N hDN

end SymmetricSubgroupAsymptotics.BinaryCarrierHeadAboveDerived16T1332
