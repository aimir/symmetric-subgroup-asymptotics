import SymmetricSubgroupAsymptotics.BinaryIrreducibleQuadraticBases
import SymmetricSubgroupAsymptotics.RankOneSquareZeroCentralizer
import SymmetricSubgroupAsymptotics.LinearCentralizerTwoPairEvaluation
import Mathlib.Tactic.NormNum

/-! Actual binary spaces of cardinal8 and16 have nonidentity
automorphism centralizers bounded by8 and288 respectively. The only
branches are the proved independent-triple and two quadratic identities;
all bases and constrained evaluation charts are constructed internally. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FiniteBinarySmallCentralizerBounds
open BinaryLinearQuadraticDichotomy

variable {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] [Finite V]

theorem finrank_eq_of_card_pow (hK : Nat.card K=2) (d : ℕ)
    (hV : Nat.card V=2^d) : Module.finrank K V=d := by
  letI : FiniteDimensional K V := Module.Finite.of_finite
  have hc := Module.natCard_eq_pow_finrank (K := K) (V := V)
  rw [hK,hV] at hc
  exact Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ)) hc.symm

theorem fixed_card_le (hK : Nat.card K=2) (e : V ≃ₗ[K] V) (he : e ≠ 1) :
    Nat.card {v : V // e v=v} ≤ 2^(Module.finrank K V-1) := by
  letI : FiniteDimensional K V := Module.Finite.of_finite
  let W : Submodule K V := (e.toLinearMap-LinearMap.id).ker
  have hproper : W ≠ ⊤ := by
    intro htop
    apply he
    ext v
    have hv : v ∈ W := by rw [htop]; trivial
    exact sub_eq_zero.mp (show e v-v=0 from hv)
  have hd := Submodule.finrank_lt hproper
  let a : {v : V // e v=v} ≃ W := {
    toFun := fun v => ⟨v.val,by change e v.val-v.val=0; rw [v.property,sub_self]⟩
    invFun := fun v => ⟨v.val,sub_eq_zero.mp v.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  calc
    Nat.card {v : V // e v=v} = Nat.card W := Nat.card_congr a
    _ = 2^Module.finrank K W := by
      rw [Module.natCard_eq_pow_finrank (K := K) (V := W),hK]
    _ ≤ 2^(Module.finrank K V-1) := Nat.pow_le_pow_right (by decide) (by omega)

omit [Finite V] in
private theorem difference_square_zero (hK : Nat.card K=2)
    (e : V ≃ₗ[K] V) (he : ∀v : V, e (e v)=v) (v : V) :
    (e.toLinearMap-LinearMap.id : V →ₗ[K] V)
      ((e.toLinearMap-LinearMap.id : V →ₗ[K] V) v)=0 := by
  change e (e v-v)-(e v-v)=0
  rw [map_sub,he v]
  have hd (x : V) : x+x=0 := by
    calc
      x+x = -x+x := congrArg (fun z : V => z+x) (neg_eq_self hK x).symm
      _ = 0 := neg_add_cancel x
  calc
    v-e v-(e v-v) = (v+v)-(e v+e v) := by abel
    _ = 0 := by simp only [hd,sub_self]

omit [Finite V] in
private theorem difference_range_pos [FiniteDimensional K V]
    (e : V ≃ₗ[K] V) (he : e ≠ 1) :
    0 < Module.finrank K (e.toLinearMap-LinearMap.id).range := by
  apply Nat.pos_of_ne_zero
  intro hr
  have hz := LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hr)
  apply he
  ext v
  have hh := DFunLike.congr_fun hz v
  exact sub_eq_zero.mp (show e v-v=0 from hh)

theorem centralizer_card_le_eight (hK : Nat.card K=2) (hV : Nat.card V=8)
    (e : V ≃ₗ[K] V) (he : e ≠ 1) :
    Nat.card {a : V ≃ₗ[K] V // Commute e a} ≤ 8 := by
  letI : FiniteDimensional K V := Module.Finite.of_finite
  have hd : Module.finrank K V=3 := finrank_eq_of_card_pow hK 3 (by simpa using hV)
  rcases independent_triple_or_quadratic hK e with ⟨v,hv⟩ | hinv | hquad
  · have hb := LinearCentralizerTripleEvaluation.card_le_of_independent_triple e v hv
    rw [hV,hd] at hb
    exact hb.trans (by decide)
  · let N := e.toLinearMap-LinearMap.id
    have hN : ∀v : V, N (N v)=0 := difference_square_zero hK e hinv
    have heN (v : V) : e v=v+N v := by change e v=v+(e v-v); abel
    have hrpos : 0 < Module.finrank K N.range := difference_range_pos e he
    have hrle := SquareZeroLinearBasisPairs.twice_range_finrank_le N hN
    have hr : Module.finrank K N.range=1 := by rw [hd] at hrle; omega
    have hkdim : Module.finrank K N.ker=2 := by
      have hh := N.finrank_range_add_finrank_ker
      rw [hr,hd] at hh
      omega
    have hk : Nat.card N.ker=4 := by
      rw [Module.natCard_eq_pow_finrank (K := K) (V := N.ker),hK,hkdim]
      decide
    have hb := RankOneSquareZeroCentralizer.card_le hK N hN hr e heN
    simpa only [hk,hkdim] using hb
  · exact False.elim (BinaryIrreducibleQuadraticBases.not_finrank_three hK e hquad hd)

theorem centralizer_card_le_twoEightyEight (hK : Nat.card K=2) (hV : Nat.card V=16)
    (e : V ≃ₗ[K] V) (he : e ≠ 1) :
    Nat.card {a : V ≃ₗ[K] V // Commute e a} ≤ 288 := by
  letI : FiniteDimensional K V := Module.Finite.of_finite
  have hd : Module.finrank K V=4 := finrank_eq_of_card_pow hK 4 (by simpa using hV)
  rcases independent_triple_or_quadratic hK e with ⟨v,hv⟩ | hinv | hquad
  · have hb := LinearCentralizerTripleEvaluation.card_le_of_independent_triple e v hv
    rw [hV,hd] at hb
    exact hb.trans (by decide)
  · let N := e.toLinearMap-LinearMap.id
    have hN : ∀v : V, N (N v)=0 := difference_square_zero hK e hinv
    have heN (v : V) : e v=v+N v := by change e v=v+(e v-v); abel
    have hrpos : 0 < Module.finrank K N.range := difference_range_pos e he
    have hrle := SquareZeroLinearBasisPairs.twice_range_finrank_le N hN
    have hr : Module.finrank K N.range=1 ∨ Module.finrank K N.range=2 := by
      rw [hd] at hrle
      omega
    rcases hr with hr | hr
    · have hkdim : Module.finrank K N.ker=3 := by
        have hh := N.finrank_range_add_finrank_ker
        rw [hr,hd] at hh
        omega
      have hk : Nat.card N.ker=8 := by
        rw [Module.natCard_eq_pow_finrank (K := K) (V := N.ker),hK,hkdim]
        decide
      have hb := RankOneSquareZeroCentralizer.card_le hK N hN hr e heN
      simpa only [hk,hkdim] using hb
    · obtain ⟨b,hb0,hb2⟩ := SquareZeroLinearBasisPairs.exists_basis_difference_pairs N hN hr hd e heN
      have hb := LinearCentralizerTwoPairEvaluation.card_le_of_basis_difference_pairs b e hb0 hb2
      rw [hV] at hb
      exact hb.trans (by decide)
  · obtain ⟨b,hb0,hb2⟩ := BinaryIrreducibleQuadraticBases.exists_basis_pairs hK e hquad hd
    have hb := LinearCentralizerTwoPairEvaluation.card_le_of_basis_pairs b e hb0 hb2
    rw [hV] at hb
    exact hb.trans (by decide)

end SymmetricSubgroupAsymptotics.FiniteBinarySmallCentralizerBounds
