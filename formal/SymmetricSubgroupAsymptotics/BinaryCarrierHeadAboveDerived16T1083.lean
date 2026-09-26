import SymmetricSubgroupAsymptotics.BinaryCarrierFormTransport16T1083
import SymmetricSubgroupAsymptotics.PrimeDerivedJointHead
import Lean.Elab.Tactic.Omega

/-! A uniform head bound for every original 16T1083 normal subgroup
containing its actual derived subgroup. The finite commutator-form
certificates replace normal-by-normal rank checks on this branch.
No assertion about the remaining normal axes or full row coverage is made.
-/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryCarrierHeadAboveDerived16T1083

abbrev Original := BinaryCarrierDerivedOrder16T1083.Original

private abbrev kernelIdentity := BinaryCarrierDerived16T1083.evaluationKernel_eq_commutator

private theorem relative_character_rank :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 (commutator Original)) = 3 := by
  rw [BinaryCarrierDerivedCharacters16T1083.coordinateEquiv.finrank_eq]
  simp

/-- Every nonzero original image retains at most one extra character. -/
theorem head_le_image_add_one (N : Subgroup Original) [N.Normal]
    (hDN : commutator Original ≤ N) (hW : primeDerivedImage 2 N ≠ ⊥) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) ≤
      Module.finrank (ZMod 2) (primeDerivedImage 2 N) + 1 :=
  primeRelativeHead_above_derived_le_image_add_one 2 kernelIdentity
    BinaryCarrierFormTransport16T1083.actual_form_ker_inf_eq_bot_of_independent N hDN hW

/-- Images of dimension at least three have no retained contribution. -/
theorem head_le_image_of_two_lt (N : Subgroup Original) [N.Normal]
    (hDN : commutator Original ≤ N)
    (hW : 2 < Module.finrank (ZMod 2) (primeDerivedImage 2 N)) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) ≤
      Module.finrank (ZMod 2) (primeDerivedImage 2 N) :=
  primeRelativeHead_above_derived_le_image_of_radical_bounds 2 kernelIdentity 2
    BinaryCarrierFormTransport16T1083.actual_form_finrank_ker_le_two N hDN hW

/-- The zero-image case uses the actual three-dimensional invariant
derived-character space; no extension of its characters is assumed. -/
theorem head_le_max_three_image (N : Subgroup Original) [N.Normal]
    (hDN : commutator Original ≤ N) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) ≤
      max 3 (Module.finrank (ZMod 2) (primeDerivedImage 2 N)) := by
  by_cases hzero : Module.finrank (ZMod 2) (primeDerivedImage 2 N) = 0
  · have h := primeRelativeHead_above_derived_le_image_add_joint 2 kernelIdentity N hDN
    rw [hzero, Nat.zero_add] at h
    have hJ : Module.finrank (ZMod 2)
        (linearJointAnnihilator (derivedEvaluationBilinearMap 2 kernelIdentity)
          (primeDerivedImage 2 N)) ≤ 3 :=
      (Submodule.finrank_le _).trans_eq
        relative_character_rank
    exact (h.trans hJ).trans (le_max_left _ _)
  · by_cases hsmall : Module.finrank (ZMod 2) (primeDerivedImage 2 N) ≤ 2
    · have hW : primeDerivedImage 2 N ≠ ⊥ := by
        intro hbot
        apply hzero
        rw [hbot]
        exact finrank_bot (ZMod 2) (PrimeAbelianization 2 Original)
      have h := head_le_image_add_one N hDN hW
      have hthree : Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) ≤ 3 := by omega
      exact hthree.trans (le_max_left _ _)
    · exact (head_le_image_of_two_lt N hDN (lt_of_not_ge hsmall)).trans
        (le_max_right _ _)

/-- The same bound stated using the literal image N/G' in the original
quotient, not a stored quotient order or an abstract replacement group. -/
theorem head_le_max_three_log_quotient (N : Subgroup Original) [N.Normal]
    (hDN : commutator Original ≤ N) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) ≤
      max 3 (Nat.log 2 (Nat.card (normalChainQuotient (commutator Original) N))) := by
  rw [derivedNormalImage_log_card 2 kernelIdentity N]
  exact head_le_max_three_image N hDN

/-- The checked sixteen-element derived subgroup also gives the same
bound directly in terms of the original normal subgroup's cardinality. -/
theorem head_le_max_three_log_div_sixteen (N : Subgroup Original) [N.Normal]
    (hDN : commutator Original ≤ N) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) ≤
      max 3 (Nat.log 2 (Nat.card N / 16)) := by
  have hc := normalChainQuotient_card_mul (commutator Original) N hDN
  rw [BinaryCarrierDerivedOrder16T1083.card_commutator] at hc
  have hQ : Nat.card (normalChainQuotient (commutator Original) N) = Nat.card N / 16 := by
    rw [← hc, Nat.mul_div_cancel _ (by decide : 0 < (16 : ℕ))]
  rw [← hQ]
  exact head_le_max_three_log_quotient N hDN

end SymmetricSubgroupAsymptotics.BinaryCarrierHeadAboveDerived16T1083
