import SymmetricSubgroupAsymptotics.CFSGHeisenbergSymplecticQuotient
import SymmetricSubgroupAsymptotics.CFSGHeisenbergCentralIsotropy
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.Tactic.Linarith

/-! A centre-proper subgroup of the actual Heisenberg group over a
finite field has at most q^m vector parameters. Its central intersection
has index at least the characteristic prime. The vector subgroup need
not be linear over the full coefficient field: the proof restricts the
actual pairing to the prime field and uses a nonzero functional killing
the actual central intersection. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGHeisenbergFiniteFieldIsotropy

open CFSGHeisenbergCoordinateGroup CFSGHeisenbergSymplecticQuotient
variable {K : Type*} [Field K] {m : ℕ}

def vectorImage (H : Subgroup (Element K m)) :
    AddSubgroup ((Fin m → K) × (Fin m → K)) := (H.map projection).toAddSubgroup'

def centralPreimage (H : Subgroup (Element K m)) : AddSubgroup K :=
  (H.comap central).toAddSubgroup'

theorem centralPreimage_ne_top (H : Subgroup (Element K m))
    (hH : ¬(central (K := K) (m := m)).range ≤ H) : centralPreimage H ≠ ⊤ := by
  intro he
  apply hH
  rintro g ⟨z, rfl⟩
  change z.toAdd ∈ centralPreimage H
  rw [he]
  trivial

theorem vectorImage_pairing_mem (H : Subgroup (Element K m))
    (v : (Fin m → K) × (Fin m → K)) (hv : v ∈ vectorImage H)
    (w : (Fin m → K) × (Fin m → K)) (hw : w ∈ vectorImage H) :
    pairing v w ∈ centralPreimage H := by
  change Multiplicative.ofAdd v ∈ H.map projection at hv
  change Multiplicative.ofAdd w ∈ H.map projection at hw
  obtain ⟨g, hg, hgv⟩ := hv
  obtain ⟨h, hh, hhw⟩ := hw
  have hgv' : (g.a, g.b) = v := congrArg Multiplicative.toAdd hgv
  have hhw' : (h.a, h.b) = w := congrArg Multiplicative.toAdd hhw
  change central (Multiplicative.ofAdd (pairing v w)) ∈ H
  rw [← hgv', ← hhw', ← commutator_eq_pairing]
  exact H.mul_mem (H.mul_mem (H.mul_mem hg hh) (H.inv_mem hg)) (H.inv_mem hh)

theorem vectorImage_card_le (p : ℕ) [Fact p.Prime] [CharP K p] [Finite K]
    (H : Subgroup (Element K m)) (hH : ¬(central (K := K) (m := m)).range ≤ H) :
    Nat.card (vectorImage H) ≤ Nat.card K ^ m := by
  letI : Algebra (ZMod p) K := ZMod.algebra K p
  let V := (Fin m → K) × (Fin m → K)
  letI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  let B : V →ₗ[ZMod p] V →ₗ[ZMod p] K :=
    (pairing (K := K) (m := m)).restrictScalars₁₂ (ZMod p) (ZMod p)
  let W := vectorImage H
  let C := centralPreimage H
  let L := AddSubgroup.toZModSubmodule p W
  have hd : 2 * Module.finrank (ZMod p) L ≤ Module.finrank (ZMod p) V :=
    CFSGHeisenbergCentralIsotropy.additive_twice_finrank_le p B
      (fun v => pairing_alt v) (fun v hv => pairing_full v hv)
      C (centralPreimage_ne_top H hH) W (fun v hv w hw => vectorImage_pairing_mem H v hv w hw)
  have hW : Nat.card W = p ^ Module.finrank (ZMod p) L := by
    change Nat.card L = _
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
  have hV : Nat.card V = p ^ Module.finrank (ZMod p) V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
  have hs : Nat.card W ^ 2 ≤ Nat.card V := by
    rw [hW, hV, ← pow_mul]
    exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos
      (by simpa only [Nat.mul_comm] using hd)
  have hv : Nat.card V = (Nat.card K ^ m)^2 := by
    simp only [V, Nat.card_prod, Nat.card_fun, Nat.card_fin, pow_two]
  rw [hv] at hs
  change Nat.card W ≤ Nat.card K ^ m
  exact (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp hs

theorem proper_additive_card_mul_prime_le (p : ℕ) [Fact p.Prime] [CharP K p] [Finite K]
    (C : AddSubgroup K) (hC : C ≠ ⊤) : p * Nat.card C ≤ Nat.card K := by
  letI : Algebra (ZMod p) K := ZMod.algebra K p
  letI : Module.Finite (ZMod p) K := Module.Finite.of_finite
  let L := AddSubgroup.toZModSubmodule p C
  have hL : L ≠ ⊤ := by
    intro he
    apply hC
    apply top_unique
    intro x _
    have hx : x ∈ L := by rw [he]; trivial
    exact hx
  have hd : Module.finrank (ZMod p) L < Module.finrank (ZMod p) K :=
    Submodule.finrank_lt hL
  have hc : Nat.card C = p ^ Module.finrank (ZMod p) L := by
    change Nat.card L = _
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
  have hk : Nat.card K = p ^ Module.finrank (ZMod p) K := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
  calc
    p * Nat.card C = p ^ (Module.finrank (ZMod p) L + 1) := by
      rw [hc, pow_succ]
      exact Nat.mul_comm _ _
    _ ≤ p ^ Module.finrank (ZMod p) K :=
      Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by omega)
    _ = Nat.card K := hk.symm

end SymmetricSubgroupAsymptotics.CFSGHeisenbergFiniteFieldIsotropy
