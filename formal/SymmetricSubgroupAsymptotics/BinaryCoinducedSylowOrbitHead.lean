import SymmetricSubgroupAsymptotics.CoinducedOrbitFixedHead
import SymmetricSubgroupAsymptotics.BinaryPlaneTernaryInvariants

/-!
At an actual Sylow-three fixed coset, conjugation places the original
Sylow subgroup inside the original point stabilizer. It is then Sylow in
that stabilizer, and its image in the original local quotient has order
three. This proves the vanishing of the original twisted fixed fibre.

Consequently every original subrepresentation head is at most twice the
number of moving Sylow-three orbits on the original coset action. There
are no local fixed-space or representation-capacity premises in this bound.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Classical Pointwise

namespace SymmetricSubgroupAsymptotics.BinaryCoinducedSylowOrbitHead

variable {G L V : Type} [Group G] [Finite G] [Group L] [Finite L]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (H : Subgroup G) (P : Sylow 3 G)
  (f : H →* L) (hf : Function.Surjective f)
  (rho : Representation (ZMod 2) L V)
  (hL : Nat.card L = 3 ∨ Nat.card L = 6)
  (hdim : Module.finrank (ZMod 2) V = 2)
  (hrho : Function.Injective rho)

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

include hf hL hdim hrho in
/-- Conjugate the actual ambient Sylow into the stabilizer; the resulting
local Sylow is obtained by subgroup restriction, not selected afresh. -/
theorem fibre_invariants_eq_bot_of_full_stabilizer
    (x : G) (hfull : inducedOrbitStabilizer H (P : Subgroup G) x = ⊤) :
    Representation.invariants
      (inducedOrbitFibre H (P : Subgroup G) (rho.comp f) x) = ⊥ := by
  have hfix (p : P) : x * (p : G) * x⁻¹ ∈ H := by
    have hp : p ∈ inducedOrbitStabilizer H (P : Subgroup G) x := by
      rw [hfull]
      exact Subgroup.mem_top p
    exact hp
  have hle : ((x • P : Sylow 3 G) : Subgroup G) ≤ H := by
    intro y hy
    change y ∈ (P : Subgroup G).map (MulAut.conj x).toMonoidHom at hy
    obtain ⟨p, hp, rfl⟩ := hy
    exact hfix ⟨p, hp⟩
  let Q : Sylow 3 H := (x • P).subtype hle
  have hzero := BinaryPlaneTernaryInvariants.local_sylow_invariants_eq_bot
    f hf Q rho hL hdim hrho
  apply le_antisymm _ bot_le
  intro v hv
  have hvQ : v ∈ Representation.invariants
      ((rho.comp f).comp (Q : Subgroup H).subtype) := by
    intro q
    have hq : (q.1 : G) ∈ (P : Subgroup G).map (MulAut.conj x).toMonoidHom := q.2
    obtain ⟨p, hp, he⟩ := hq
    let l : inducedOrbitStabilizer H (P : Subgroup G) x :=
      ⟨⟨p, hp⟩, hfix ⟨p, hp⟩⟩
    have htwist : inducedOrbitTwist H (P : Subgroup G) x l = q.1 :=
      Subtype.ext he
    change rho (f q.1) v = v
    rw [← htwist]
    exact hv l
  rw [hzero] at hvQ
  exact hvQ

variable [Fintype (DoubleCoset.Quotient (H : Set G) ((P : Subgroup G) : Set G))]

def movingOrbits : Finset
    (DoubleCoset.Quotient (H : Set G) ((P : Subgroup G) : Set G)) :=
  Finset.univ.filter (fun q =>
    1 < (inducedOrbitStabilizer H (P : Subgroup G) q.out).index)

include hf hL hdim hrho in
/-- The actual frame head is paid only by moving Sylow-three orbits.
Fixed orbits have zero fibre by the original local epimorphism. -/
theorem subrepresentation_head_le_twice_moving
    (B : Subrepresentation (Representation.coind H.subtype (rho.comp f))) :
    Module.finrank (ZMod 2)
      (B.toRepresentation.IntertwiningMap
        (Representation.trivial (ZMod 2) G (ZMod 2))) ≤
      2 * (movingOrbits H P).card := by
  have hodd : ¬ 2 ∣ Nat.card P := by
    obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
    rw [hn]
    intro h
    exact (by decide : ¬ 2 ∣ 3) (Nat.prime_two.dvd_of_dvd_pow h)
  have hunit : IsUnit (Nat.card P : ZMod 2) :=
    isUnit_iff_ne_zero.mpr ((ZMod.natCast_eq_zero_iff (Nat.card P) 2).not.mpr hodd)
  have hinactive : ∀ q, q ∉ movingOrbits H P →
      CoinducedOrbitFixedHead.fibreFixedSpace H (P : Subgroup G) (rho.comp f) q = ⊥ := by
    intro q hq
    have hnot : ¬ 1 < (inducedOrbitStabilizer H (P : Subgroup G) q.out).index := by
      simpa only [movingOrbits, Finset.mem_filter, Finset.mem_univ, true_and] using hq
    have hpos : 0 < (inducedOrbitStabilizer H (P : Subgroup G) q.out).index :=
      Nat.pos_of_ne_zero
        (inducedOrbitStabilizer H (P : Subgroup G) q.out).index_ne_zero_of_finite
    have hindex : (inducedOrbitStabilizer H (P : Subgroup G) q.out).index = 1 := by omega
    exact fibre_invariants_eq_bot_of_full_stabilizer H P f hf rho hL hdim hrho q.out
      (Subgroup.index_eq_one.mp hindex)
  have h := CoinducedOrbitFixedHead.subrepresentation_head_le_active
    H (P : Subgroup G) (rho.comp f) hunit (movingOrbits H P) hinactive B
  simpa only [hdim, Nat.mul_comm] using h

end SymmetricSubgroupAsymptotics.BinaryCoinducedSylowOrbitHead

end
