import SymmetricSubgroupAsymptotics.LinearCentralizerSparseEvaluation
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.FieldTheory.Finiteness

/-! Uniform bounds for an actual 32-element vector space over a
two-element field: a nonidentity automorphism has at most16 fixed
vectors and at most31*32^3 commuting automorphisms. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FiniteBinaryFiveSpaceBounds

variable {K V : Type*} [Field K] [Finite K]
    [AddCommGroup V] [Module K V] [Finite V]

theorem finrank_eq_five (hK : Nat.card K = 2) (hV : Nat.card V = 32) :
    Module.finrank K V = 5 := by
  letI : FiniteDimensional K V := Module.Finite.of_finite
  have hc := Module.natCard_eq_pow_finrank (K := K) (V := V)
  rw [hK, hV] at hc
  apply Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ))
  simpa only [show (2 : ℕ)^5 = 32 by decide] using hc.symm

theorem fixed_card_le_sixteen (hK : Nat.card K = 2) (hV : Nat.card V = 32)
    (e : V ≃ₗ[K] V) (he : e ≠ 1) :
    Nat.card {v : V // e v = v} ≤ 16 := by
  letI : FiniteDimensional K V := Module.Finite.of_finite
  let W : Submodule K V := (e.toLinearMap - LinearMap.id).ker
  have hproper : W ≠ ⊤ := by
    intro htop
    apply he
    ext v
    have hv : v ∈ W := by rw [htop]; trivial
    exact sub_eq_zero.mp (show e v-v=0 from hv)
  have hd := Submodule.finrank_lt hproper
  rw [finrank_eq_five hK hV] at hd
  let a : {v : V // e v=v} ≃ W := {
    toFun := fun v => ⟨v.val, by change e v.val-v.val=0; rw [v.property, sub_self]⟩
    invFun := fun v => ⟨v.val, sub_eq_zero.mp v.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  calc
    Nat.card {v : V // e v=v} = Nat.card W := Nat.card_congr a
    _ = 2^Module.finrank K W := by
      rw [Module.natCard_eq_pow_finrank (K := K) (V := W), hK]
    _ ≤ 2^4 := Nat.pow_le_pow_right (by decide) (by omega)
    _ = 16 := by decide

theorem centralizer_card_le (hK : Nat.card K = 2) (hV : Nat.card V = 32)
    (e : V ≃ₗ[K] V) (he : e ≠ 1) :
    Nat.card {a : V ≃ₗ[K] V // Commute e a} ≤ 1015808 := by
  letI : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hnon : ¬ ∃ c : K, e.toLinearMap = c • (1 : V →ₗ[K] V) := by
    rintro ⟨c, hc⟩
    have hc0 : c ≠ 0 := by
      intro hz
      obtain ⟨v, hv⟩ := exists_ne (0 : V)
      have hz' : e v=0 := by
        have hh := DFunLike.congr_fun hc v
        simpa only [hz, zero_smul, LinearMap.zero_apply] using hh
      exact hv (e.injective (hz'.trans (map_zero e).symm))
    obtain ⟨a, ha, huniq⟩ := (Nat.card_eq_two_iff' (0 : K)).mp hK
    have hc1 : c=1 := (huniq c hc0).trans (huniq 1 one_ne_zero).symm
    apply he
    apply LinearEquiv.toLinearMap_injective
    simpa only [hc1, one_smul] using hc
  have hb := LinearCentralizerSparseEvaluation.card_le_of_nonscalar e hnon
  rw [hV, finrank_eq_five hK hV] at hb
  exact hb

end SymmetricSubgroupAsymptotics.FiniteBinaryFiveSpaceBounds
