import SymmetricSubgroupAsymptotics.SylowBinaryTopNormalizer
import SymmetricSubgroupAsymptotics.CoinducedNormalizerOrbitHead
import SymmetricSubgroupAsymptotics.TernaryNormalizerBlockOrbits
import SymmetricSubgroupAsymptotics.BinaryCoinducedLargeOrbitOriginalHead

/-! A nontrivial transitive binary block top gives a four-dimensional
head bound for every actual binary plane frame on sixteen points. The
Sylow, its normalizer, both block actions and the external local quotient
are kept on their original groups. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryTopNormalizerOrbitHead

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

variable {G T I L V : Type} [Group G] [Finite G] [Group T]
    [MulAction G I] [MulAction T I] [MulAction.IsPretransitive T I]
    [FaithfulSMul T I] [Finite I] [Nontrivial I]
    [Group L] [Finite L] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]

theorem head_le_four (H : Subgroup G) (hindex : H.index = 16)
    (beta : G →* T) (hbeta : Function.Surjective beta) (hT : IsPGroup 2 T)
    (hact : ∀ (g : G) (i : I), g • i = beta g • i)
    (b : G ⧸ H → I)
    (hb : ∀ (g : G) (x : G ⧸ H), b (g • x) = g • b x)
    (f : H →* L) (hf : Function.Surjective f)
    (rho : Representation (ZMod 2) L V)
    (hL : Nat.card L = 3 ∨ Nat.card L = 6)
    (hdim : Module.finrank (ZMod 2) V = 2) (hrho : Function.Injective rho)
    (B : Subrepresentation (Representation.coind H.subtype (rho.comp f))) :
    Module.finrank (ZMod 2)
      (B.toRepresentation.IntertwiningMap (Representation.trivial (ZMod 2) G (ZMod 2)))
        ≤ 4 := by
  let P : Sylow 3 G := Classical.choice inferInstance
  obtain ⟨g, hg, hgm⟩ :=
    SylowBinaryTopNormalizer.exists_moving_normalizer (I := I) beta hbeta hT P
  let A : Subgroup G := (P : Subgroup G) ⊔ Subgroup.zpowers g
  have hPA : (P : Subgroup G) ≤ A := le_sup_left
  have hgA : g ∈ A :=
    (show Subgroup.zpowers g ≤ A from le_sup_right) (Subgroup.mem_zpowers g)
  letI : Finite (DoubleCoset.Quotient (H : Set G) (A : Set G)) :=
    Finite.of_injective (inducedDoubleCosetToOrbit H A)
      (inducedDoubleCosetToOrbit_injective H A)
  letI : Fintype (DoubleCoset.Quotient (H : Set G) (A : Set G)) := Fintype.ofFinite _
  let active := TernaryNormalizerBlockOrbits.active H (P : Subgroup G) A
  have hfix (p : P) (i : I) : (p : G) • i = i := by
    have hp : beta p.1 = 1 := SylowBinaryTopNormalizer.sylow_le_kernel beta hT P p.2
    rw [hact, hp, one_smul]
  have hmove (i : I) : g • i ≠ i := by rw [hact]; exact hgm i
  have hcount : active.card ≤ 2 := by
    have hn := TernaryNormalizerBlockOrbits.six_mul_active_le_index H
      (P : Subgroup G) A b hb P.isPGroup' hPA hfix ⟨g, hgA⟩ hmove
    change 6 * active.card ≤ H.index at hn
    omega
  have hodd : ¬ 2 ∣ Nat.card P := by
    obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
    rw [hn]
    intro h
    exact (by decide : ¬ 2 ∣ 3) (Nat.prime_two.dvd_of_dvd_pow h)
  have hunit : IsUnit (Nat.card P : ZMod 2) :=
    isUnit_iff_ne_zero.mpr ((ZMod.natCast_eq_zero_iff (Nat.card P) 2).not.mpr hodd)
  have hinactive : ∀ q, q ∉ active →
      CoinducedOrbitFixedHead.fibreFixedSpace H A (rho.comp f) q = ⊥ := by
    intro q hq
    have hfull : inducedOrbitStabilizer H (P : Subgroup G) q.out = ⊤ := by
      simpa only [active, TernaryNormalizerBlockOrbits.active, Finset.mem_filter,
        Finset.mem_univ, true_and, not_not] using hq
    exact BinaryCoinducedSylowOrbitHead.fibre_invariants_eq_bot_of_sylow_full_stabilizer
      H P A hPA f hf rho hL hdim hrho q.out hfull
  have hhead := CoinducedNormalizerOrbitHead.subrepresentation_head_le_active
    H (P : Subgroup G) (rho.comp f) g hunit hg active hinactive B
  rw [hdim] at hhead
  omega

variable {X : Type} [MulAction G X] [MulAction.IsPretransitive G X] [Finite X]

omit [Finite X] in
/-- Original-point version, with the original stabilizer and local
epimorphism unchanged. The coset equivalence is only a coordinate change. -/
theorem head_le_four_on_points (x : X) (hX : Nat.card X = 16)
    (beta : G →* T) (hbeta : Function.Surjective beta) (hT : IsPGroup 2 T)
    (hact : ∀ (g : G) (i : I), g • i = beta g • i)
    (b : X → I) (hb : ∀ (g : G) (y : X), b (g • y) = g • b y)
    (f : MulAction.stabilizer G x →* L) (hf : Function.Surjective f)
    (rho : Representation (ZMod 2) L V)
    (hL : Nat.card L = 3 ∨ Nat.card L = 6)
    (hdim : Module.finrank (ZMod 2) V = 2) (hrho : Function.Injective rho)
    (B : Subrepresentation
      (Representation.coind (MulAction.stabilizer G x).subtype (rho.comp f))) :
    Module.finrank (ZMod 2)
      (B.toRepresentation.IntertwiningMap (Representation.trivial (ZMod 2) G (ZMod 2)))
        ≤ 4 := by
  let H := MulAction.stabilizer G x
  let e : G ⧸ H ≃ X := BinaryPairTernaryOrbitHead.pointCosetEquiv x
  apply head_le_four H ((Nat.card_congr e).trans hX) beta hbeta hT hact
    (b ∘ e) _ f hf rho hL hdim hrho B
  intro g y
  change b (e (g • y)) = g • b (e y)
  rw [BinaryPairTernaryOrbitHead.pointCosetEquiv_smul, hb]

end SymmetricSubgroupAsymptotics.BinaryTopNormalizerOrbitHead

end
