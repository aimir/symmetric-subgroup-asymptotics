import SymmetricSubgroupAsymptotics.SmallFibreReeFFourFieldEightClassResidual
import SymmetricSubgroupAsymptotics.SimplePrimeProperIndexBandExclusion
import SymmetricSubgroupAsymptotics.CFSGReeFFourSixteenCellCardinality

/-! The actual no11 divisor excludes original indices110..217. The
SAME original small-fibre action is therefore paid except for one socle
factor and a retained actual original subgroup of index109. Index109
is not excluded or replaced by a global numerical assertion. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SmallFibreReeFFourFieldEightSingleIndexResidual
open PrimitiveSocleRawStructure OriginalBlockClassBound

private instance fixedFinite : Finite (CFSGReeFFourFixedModelEquivalence.originalModelFixed 1) :=
  Finite.of_injective (CFSGReeFFourFixedAmbientHom.fixedAmbientHom 1)
    (CFSGReeFFourFixedAmbientHom.fixedAmbientHom_injective 1)

theorem proper_index_eq_oneOhNine_or_large
    [IsSimpleGroup (CFSG.Models.ReeF4 1)]
    (K : Subgroup (CFSG.Models.ReeF4 1)) (hK : K≠⊤) :
    K.index=109 ∨ 218≤K.index := by
  letI : Finite (CFSG.Models.ReeF4 1) := Finite.of_surjective
    (CFSGReeFFourPerfectProjection.fixedToOriginal 1 (by omega))
    (CFSGReeFFourPerfectProjection.fixedToOriginal_surjective 1 (by omega))
  have hnext : ¬110 ∣ Nat.card (CFSG.Models.ReeF4 1) := by
    intro hd
    exact CFSGReeFFourSixteenCellCardinality.eleven_not_dvd_original_fieldEight
      ((by decide : 11 ∣ (110:ℕ)).trans hd)
  exact SimplePrimeProperIndexBandExclusion.index_eq_prime_or_two_mul_le
    109 (by decide +kernel)
    (fun L hL => CFSGReeFFourFieldEightPrimeIndex.proper_index_le L hL)
    CFSGReeFFourFieldEightProperIndexBand.prime_oneOhNine_dvd_original_card hnext K hK

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]

theorem subnormal_gap_or_same_index_oneOhNine
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω), π (g • ω)=g • π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x, Nat.card (originalBlockFibre π x)=c)
    (E : NonaffineData (Top (A:=A) (X:=X)) X)
    (e : E.Simple ≃* CFSG.Models.ReeF4 1)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3≤5^(Nat.card Ω-2) ∨
      (E.factorCount=1 ∧ ∃ K : Subgroup E.Simple, K≠⊤ ∧
        Nat.card X=K.index ∧ K.index=109) := by
  letI : IsSimpleGroup (CFSG.Models.ReeF4 1) := e.symm.isSimpleGroup
  rcases SmallFibreReeFFourFieldEightClassResidual.subnormal_gap_or_same_short_index
      π hπ c hc hsize E e H hH with hgap | ⟨hk,K,hK,hdegree,hlo,hhi⟩
  · exact Or.inl hgap
  · have hmap : K.map e.toMonoidHom≠⊤ := by
      intro ht
      apply hK
      apply Subgroup.map_injective (f:=e.toMonoidHom) e.injective
      exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
    have hband := proper_index_eq_oneOhNine_or_large (K.map e.toMonoidHom) hmap
    have heq : (K.map e.toMonoidHom).index=K.index := K.index_map_equiv e
    rw [heq] at hband
    rcases hband with he | he
    · exact Or.inr ⟨hk,K,hK,hdegree,he⟩
    · omega

end SymmetricSubgroupAsymptotics.SmallFibreReeFFourFieldEightSingleIndexResidual
