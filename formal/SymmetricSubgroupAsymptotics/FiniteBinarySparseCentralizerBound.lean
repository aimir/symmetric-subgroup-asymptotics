import SymmetricSubgroupAsymptotics.LinearCentralizerSparseEvaluation

/-! In every binary vector space, a nonidentity invertible operator is
nonscalar. The existing sparse evaluation chart therefore applies in
every dimension, with no operator classification or matrix census. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FiniteBinarySparseCentralizerBound

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Finite V] [Nontrivial V]

theorem centralizer_card_le (hK : Nat.card K=2) (e : V ≃ₗ[K] V) (he : e≠1) :
    Nat.card {a : V ≃ₗ[K] V // Commute e a} ≤
      (Nat.card V-1)*Nat.card V^(Module.finrank K V-2) := by
  have hnon : ¬∃ c : K, e.toLinearMap=c • (1 : V →ₗ[K] V) := by
    rintro ⟨c,hc⟩
    have hc0 : c≠0 := by
      intro hz
      obtain ⟨v,hv⟩ := exists_ne (0 : V)
      have hz' : e v=0 := by
        have hh := DFunLike.congr_fun hc v
        simpa only [hz,zero_smul,LinearMap.zero_apply] using hh
      exact hv (e.injective (hz'.trans (map_zero e).symm))
    obtain ⟨a,ha,huniq⟩ := (Nat.card_eq_two_iff' (0 : K)).mp hK
    have hc1 : c=1 := (huniq c hc0).trans (huniq 1 one_ne_zero).symm
    apply he
    apply LinearEquiv.toLinearMap_injective
    simpa only [hc1,one_smul] using hc
  exact LinearCentralizerSparseEvaluation.card_le_of_nonscalar e hnon

end SymmetricSubgroupAsymptotics.FiniteBinarySparseCentralizerBound
