import SymmetricSubgroupAsymptotics.FiniteBinarySmallCentralizerBounds
import SymmetricSubgroupAsymptotics.LinearCentralizerTwoPairSharpEvaluation
import SymmetricSubgroupAsymptotics.LinearCentralizerTripleSharpEvaluation
import SymmetricSubgroupAsymptotics.RankOneSquareZeroCentralizerSharp

/-! Every nonidentity automorphism of an actual binary four-dimensional
space has centralizer of cardinal at most 192. The structural orbit /
quadratic dichotomy is proved independently; each branch here uses an
injective sparse evaluation chart retaining independence of its images. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FiniteBinaryFourCentralizerSharpBound
open BinaryLinearQuadraticDichotomy

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Finite V]

omit [Finite V] in
private theorem difference_square_zero (hK : Nat.card K = 2)
    (e : V ≃ₗ[K] V) (he : ∀ v : V, e (e v) = v) (v : V) :
    (e.toLinearMap - LinearMap.id : V →ₗ[K] V)
      ((e.toLinearMap - LinearMap.id : V →ₗ[K] V) v) = 0 := by
  change e (e v - v) - (e v - v) = 0
  rw [map_sub, he v]
  have hd (x : V) : x + x = 0 := by
    calc
      x + x = -x + x := congrArg (fun z : V => z + x) (neg_eq_self hK x).symm
      _ = 0 := neg_add_cancel x
  calc
    v - e v - (e v - v) = (v + v) - (e v + e v) := by abel
    _ = 0 := by simp only [hd, sub_self]

omit [Finite V] in
private theorem difference_range_pos [FiniteDimensional K V]
    (e : V ≃ₗ[K] V) (he : e ≠ 1) :
    0 < Module.finrank K (e.toLinearMap - LinearMap.id).range := by
  apply Nat.pos_of_ne_zero
  intro hr
  have hz := LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hr)
  apply he
  ext v
  have hh := DFunLike.congr_fun hz v
  exact sub_eq_zero.mp (show e v - v = 0 from hh)

theorem centralizer_card_le_oneNinetyTwo (hK : Nat.card K = 2) (hV : Nat.card V = 16)
    (e : V ≃ₗ[K] V) (he : e ≠ 1) :
    Nat.card {a : V ≃ₗ[K] V // Commute e a} ≤ 192 := by
  letI : FiniteDimensional K V := Module.Finite.of_finite
  have hd : Module.finrank K V = 4 :=
    FiniteBinarySmallCentralizerBounds.finrank_eq_of_card_pow hK 4 (by simpa using hV)
  rcases independent_triple_or_quadratic hK e with ⟨v, hv⟩ | hinv | hquad
  · have hb := LinearCentralizerTripleSharpEvaluation.card_le_of_independent_triple e v hv
    rw [hV, hK, hd] at hb
    exact hb.trans (by decide)
  · let N := e.toLinearMap - LinearMap.id
    have hN : ∀ v : V, N (N v) = 0 := difference_square_zero hK e hinv
    have heN (v : V) : e v = v + N v := by change e v = v + (e v - v); abel
    have hrpos : 0 < Module.finrank K N.range := difference_range_pos e he
    have hrle := SquareZeroLinearBasisPairs.twice_range_finrank_le N hN
    have hr : Module.finrank K N.range = 1 ∨ Module.finrank K N.range = 2 := by
      rw [hd] at hrle
      omega
    rcases hr with hr | hr
    · have hkdim : Module.finrank K N.ker = 3 := by
        have hh := N.finrank_range_add_finrank_ker
        rw [hr, hd] at hh
        omega
      have hk : Nat.card N.ker = 8 := by
        rw [Module.natCard_eq_pow_finrank (K := K) (V := N.ker), hK, hkdim]
        decide
      have hb := RankOneSquareZeroCentralizerSharp.card_le hK N hN hr hkdim e heN
      simpa only [hk, hK] using hb
    · obtain ⟨b, hb0, hb2⟩ :=
        SquareZeroLinearBasisPairs.exists_basis_difference_pairs N hN hr hd e heN
      have hb := LinearCentralizerTwoPairSharpEvaluation.card_le_of_basis_difference_pairs b e hb0 hb2
      rw [hV, hK] at hb
      exact hb.trans (by decide)
  · obtain ⟨b, hb0, hb2⟩ := BinaryIrreducibleQuadraticBases.exists_basis_pairs hK e hquad hd
    have hb := LinearCentralizerTwoPairSharpEvaluation.card_le_of_basis_pairs b e hb0 hb2
    rw [hV, hK] at hb
    exact hb.trans (by decide)

end SymmetricSubgroupAsymptotics.FiniteBinaryFourCentralizerSharpBound
