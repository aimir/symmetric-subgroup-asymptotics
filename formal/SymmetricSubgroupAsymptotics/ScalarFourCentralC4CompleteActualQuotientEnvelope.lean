import SymmetricSubgroupAsymptotics.ScalarFourCentralC4CompleteQuotientEnvelope
import SymmetricSubgroupAsymptotics.ScalarFourCentralC4CubicBinaryMenu
import SymmetricSubgroupAsymptotics.ScalarFourCentralC4SymmetricQuotientDichotomy

/-! Both actual finite tops discharge the full original-normal menu.
The resulting source sum has no supplied quotient-capacity hypothesis. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.ScalarFourCentralC4TopCoordinates
open Non2UnipotentPrefixFiniteMenu
variable {Q T : Type} [Group Q] [Finite Q] [Group T] [Finite T] {c d : ℕ}

 theorem complete_cubic_quotient_envelope
    (D : ScalarFourCentralC4TopCoordinates Q CyclicThree c d)
    (hc : c≤3) (hd : d≤3) (hcubic : D.cubic=Multiplicative.ofAdd (1 : ZMod 3))
    (f : CyclicThree →* Equiv.Perm (Fin 3)) (hf : Function.Injective f)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature) (b : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)), completeQuotientWeight (R := Q) J) ≤
      (2 : ℝ)^(512 : ℕ)*(2 : ℝ)^((381/192 : ℝ)*(b : ℝ))*(subgroupCount b : ℝ)+
        BinaryKernelRankTailNumerics.raw ((2 : ℝ)^(256 : ℕ)) 7 b+
        MarkedC4KernelRankTailNumerics.raw ((2 : ℝ)^(256 : ℕ)) 22 b := by
  apply D.complete_quotient_envelope_of_menu f hf hc hd _ hZmud lit b
  intro N hN
  rcases D.cubic_all_original_binary_menu hcubic N with hret | hbin
  · exact Or.inl hret
  · exact Or.inr ⟨hbin.1,hbin.2.trans (Nat.pow_le_pow_right (by decide) (by omega))⟩

 theorem complete_symmetric_quotient_envelope
    (D : ScalarFourCentralC4TopCoordinates Q T c d)
    (e : T ≃* Equiv.Perm (Fin 3)) (hc : c≤3) (hd : d≤3)
    (hcubic : orderOf D.cubic=3)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature) (b : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)), completeQuotientWeight (R := Q) J) ≤
      (2 : ℝ)^(512 : ℕ)*(2 : ℝ)^((381/192 : ℝ)*(b : ℝ))*(subgroupCount b : ℝ)+
        BinaryKernelRankTailNumerics.raw ((2 : ℝ)^(256 : ℕ)) 7 b+
        MarkedC4KernelRankTailNumerics.raw ((2 : ℝ)^(256 : ℕ)) 22 b := by
  apply D.complete_quotient_envelope_of_menu e.toMonoidHom e.injective hc hd _ hZmud lit b
  intro N hN
  rcases D.symmetric_all_original_quotients e hcubic N with hret | hbin
  · exact Or.inl hret
  · exact Or.inr ⟨hbin.1,hbin.2.trans (Nat.pow_le_pow_right (by decide) (by omega))⟩

end SymmetricSubgroupAsymptotics.ScalarFourCentralC4TopCoordinates
