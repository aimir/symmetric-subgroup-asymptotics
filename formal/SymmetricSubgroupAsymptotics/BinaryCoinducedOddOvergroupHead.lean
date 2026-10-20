import SymmetricSubgroupAsymptotics.CoinducedNormalizerOrbitHead
import SymmetricSubgroupAsymptotics.BinaryPairTernaryOrbitHead

/-! An odd subgroup containing an actual ambient Sylow-three subgroup can
replace that Sylow in the moving-orbit estimate. Every fixed orbit still
has zero twisted local fibre. In particular an actual fifteen-point orbit
on sixteen points gives a two-dimensional coinduced head. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace BinaryCoinducedOddOvergroupHead

private theorem moving_le_one_of_fifteen_orbit
    {A X : Type} [Group A] [MulAction A X] [Finite X]
    (hX : Nat.card X = 16) (x : X)
    (hx : 15 ≤ Nat.card (MulAction.orbit A x)) :
    Nat.card (TernaryMovingOrbitCount.movingOrbits A X) ≤ 1 := by
  letI : Fintype (TernaryMovingOrbitCount.movingOrbits A X) := Fintype.ofFinite _
  let q : TernaryMovingOrbitCount.movingOrbits A X := ⟨Quotient.mk'' x, by
    change 1 < Nat.card (MulAction.orbit A x)
    omega⟩
  have hsum : 2 * Nat.card (TernaryMovingOrbitCount.movingOrbits A X) + 13 ≤
      Nat.card (TernaryMovingOrbitCount.movingPoints A X) := by
    rw [Nat.card_sigma]
    calc
      _ = ∑ o : TernaryMovingOrbitCount.movingOrbits A X,
          (2 + if o = q then 13 else 0) := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul,
          Finset.sum_ite_eq', Finset.mem_univ, if_true, Nat.card_eq_fintype_card]
        omega
      _ ≤ _ := Finset.sum_le_sum (by
        intro o _
        by_cases ho : o = q
        · subst o
          simpa only [if_true, Nat.reduceAdd] using hx
        · simpa only [if_neg ho, Nat.add_zero] using o.2)
  have hbound := hsum.trans (Nat.card_le_card_of_injective
    (TernaryMovingOrbitCount.movingPoint A X)
    (TernaryMovingOrbitCount.movingPoint_injective A X))
  omega

variable {G L V : Type} [Group G] [Finite G] [Group L] [Finite L]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (H : Subgroup G) (P : Sylow 3 G) (A : Subgroup G)
    (hPA : (P : Subgroup G) ≤ A) (hodd : ¬ 2 ∣ Nat.card A)
    (f : H →* L) (hf : Function.Surjective f)
    (rho : Representation (ZMod 2) L V)
    (hL : Nat.card L = 3 ∨ Nat.card L = 6)
    (hdim : Module.finrank (ZMod 2) V = 2) (hrho : Function.Injective rho)

include hPA hodd hf hL hdim hrho in
theorem head_le_twice_moving
    (B : Subrepresentation (Representation.coind H.subtype (rho.comp f))) :
    Module.finrank (ZMod 2)
      (B.toRepresentation.IntertwiningMap (Representation.trivial (ZMod 2) G (ZMod 2))) ≤
      2 * Nat.card (TernaryMovingOrbitCount.movingOrbits A (G ⧸ H)) := by
  letI : Finite (DoubleCoset.Quotient (H : Set G) (A : Set G)) :=
    Finite.of_injective (inducedDoubleCosetToOrbit H A)
      (inducedDoubleCosetToOrbit_injective H A)
  letI : Fintype (DoubleCoset.Quotient (H : Set G) (A : Set G)) := Fintype.ofFinite _
  let moving : Finset (DoubleCoset.Quotient (H : Set G) (A : Set G)) :=
    Finset.univ.filter (fun q => 1 < (inducedOrbitStabilizer H A q.out).index)
  have hinactive : ∀ q, q ∉ moving →
      CoinducedOrbitFixedHead.fibreFixedSpace H A (rho.comp f) q = ⊥ := by
    intro q hq
    have hnot : ¬ 1 < (inducedOrbitStabilizer H A q.out).index := by
      simpa only [moving, Finset.mem_filter, Finset.mem_univ, true_and] using hq
    have hpos : 0 < (inducedOrbitStabilizer H A q.out).index :=
      Nat.pos_of_ne_zero (inducedOrbitStabilizer H A q.out).index_ne_zero_of_finite
    have hfull : inducedOrbitStabilizer H A q.out = ⊤ :=
      Subgroup.index_eq_one.mp (by omega)
    have hPfull : inducedOrbitStabilizer H (P : Subgroup G) q.out = ⊤ := by
      apply top_unique
      intro p _
      have ha : (⟨p.1, hPA p.2⟩ : A) ∈ inducedOrbitStabilizer H A q.out := by
        rw [hfull]
        trivial
      exact ha
    exact BinaryCoinducedSylowOrbitHead.fibre_invariants_eq_bot_of_sylow_full_stabilizer
      H P A hPA f hf rho hL hdim hrho q.out hPfull
  have hunit : IsUnit (Nat.card A : ZMod 2) :=
    isUnit_iff_ne_zero.mpr ((ZMod.natCast_eq_zero_iff (Nat.card A) 2).not.mpr hodd)
  have hb := CoinducedOrbitFixedHead.subrepresentation_head_le_active
    H A (rho.comp f) hunit moving hinactive B
  let e : {q : DoubleCoset.Quotient (H : Set G) (A : Set G) //
      1 < (inducedOrbitStabilizer H A q.out).index} ≃
      TernaryMovingOrbitCount.movingOrbits A (G ⧸ H) :=
    (inducedDoubleCosetOrbitEquiv H A).subtypeEquiv (by
      intro q
      rw [inducedDoubleCosetOrbitEquiv_orbit, Nat.card_coe_set_eq,
        inducedOrbitStabilizer_index])
  have hc : moving.card = Nat.card (TernaryMovingOrbitCount.movingOrbits A (G ⧸ H)) := by
    calc
      _ = Nat.card {q : DoubleCoset.Quotient (H : Set G) (A : Set G) //
          1 < (inducedOrbitStabilizer H A q.out).index} := by
        simp only [moving, Nat.card_eq_fintype_card, Fintype.card_subtype]
      _ = _ := Nat.card_congr e
  simpa only [hdim, hc, Nat.mul_comm] using hb

include hPA hodd hf hL hdim hrho in
theorem head_le_two_of_fifteen_orbit (hX : Nat.card (G ⧸ H) = 16)
    (x : G ⧸ H) (hx : 15 ≤ Nat.card (MulAction.orbit A x))
    (B : Subrepresentation (Representation.coind H.subtype (rho.comp f))) :
    Module.finrank (ZMod 2)
      (B.toRepresentation.IntertwiningMap (Representation.trivial (ZMod 2) G (ZMod 2))) ≤ 2 := by
  have hb := head_le_twice_moving H P A hPA hodd f hf rho hL hdim hrho B
  have hc := moving_le_one_of_fifteen_orbit hX x hx
  omega

end BinaryCoinducedOddOvergroupHead
end SymmetricSubgroupAsymptotics

end
