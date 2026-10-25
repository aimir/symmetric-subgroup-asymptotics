import SymmetricSubgroupAsymptotics.FiniteBinarySmallCentralizerBounds
import SymmetricSubgroupAsymptotics.LinearCentralizerTwoStringEvaluation

/-! A binary five-space centralizer bound from the same actual orbit /
quadratic dichotomy as in dimension four. The independent strings are
extended to an actual basis; no conjugacy or subgroup census occurs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FiniteBinaryFiveCentralizerRefinedBound
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

theorem centralizer_card_le (hK : Nat.card K = 2) (hV : Nat.card V = 32)
    (e : V ≃ₗ[K] V) (he : e ≠ 1) :
    Nat.card {a : V ≃ₗ[K] V // Commute e a} ≤ 43904 := by
  letI : FiniteDimensional K V := Module.Finite.of_finite
  have hd : Module.finrank K V = 5 :=
    FiniteBinarySmallCentralizerBounds.finrank_eq_of_card_pow hK 5 (by simpa using hV)
  rcases independent_triple_or_quadratic hK e with ⟨v, hv⟩ | hinv | hquad
  · have hb := LinearCentralizerTripleEvaluation.card_le_of_independent_triple e v hv
    rw [hV, hd] at hb
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
    · have hkdim : Module.finrank K N.ker = 4 := by
        have hh := N.finrank_range_add_finrank_ker
        rw [hr, hd] at hh
        omega
      have hk : Nat.card N.ker = 16 := by
        rw [Module.natCard_eq_pow_finrank (K := K) (V := N.ker), hK, hkdim]
        decide
      have hb := RankOneSquareZeroCentralizer.card_le hK N hN hr e heN
      simpa only [hk, hkdim] using hb
    · let c : Module.Basis (Fin 2) K N.range := Module.finBasisOfFinrankEq K N.range hr
      obtain ⟨v, hv⟩ := (c 0).property
      obtain ⟨u, hu⟩ := (c 1).property
      have hci := c.linearIndependent.map' N.range.subtype N.range.ker_subtype
      have hcf : (fun i : Fin 2 => ((c i : N.range) : V)) = ![N v, N u] := by
        funext i
        fin_cases i
        · exact hv.symm
        · exact hu.symm
      change LinearIndependent K (fun i : Fin 2 => ((c i : N.range) : V)) at hci
      rw [hcf] at hci
      have hfour := SquareZeroLinearBasisPairs.four_independent_of_independent_images N hN v u hci
      have hcomm (a : V ≃ₗ[K] V) (ha : Commute e a) (x : V) : a (N x) = N (a x) := by
        change a (e x - x) = e (a x) - a x
        rw [map_sub]
        exact congrArg (fun y : V => y - a x)
          (congrArg (fun f : V ≃ₗ[K] V => f x) ha).symm
      have hb := LinearCentralizerTwoStringEvaluation.card_le_of_independent_strings
        e N v u hfour hcomm
      rw [hV, hd] at hb
      exact hb.trans (by decide)
  · obtain ⟨v, u, hfour⟩ :=
      BinaryIrreducibleQuadraticBases.exists_independent_four hK e hquad (by omega)
    have hb := LinearCentralizerTwoStringEvaluation.card_le_of_independent_strings
      e e.toLinearMap v u hfour (fun a ha x =>
        (congrArg (fun f : V ≃ₗ[K] V => f x) ha).symm)
    rw [hV, hd] at hb
    exact hb.trans (by decide)

end SymmetricSubgroupAsymptotics.FiniteBinaryFiveCentralizerRefinedBound
