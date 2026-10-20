import SymmetricSubgroupAsymptotics.FaithfulThreeOnThree
import Mathlib.RepresentationTheory.Invariants
import Mathlib.FieldTheory.Finiteness
import Mathlib.Algebra.Field.ZMod
import Mathlib.GroupTheory.Sylow

/-!
A faithful binary plane has no fixed vector under an order-three group.
Consequently a Sylow-three subgroup of an actual local source, mapped
onto a local group of order three or six, has no fixed vectors either.
This discharges the local vanishing calculation in the odd-orbit frame
bound. It does not assume that an original point is Sylow-fixed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryPlaneTernaryInvariants

variable {L V : Type} [Group L] [Finite L]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- The three nonzero vectors of the actual faithful plane form one orbit;
an invariant nonzero vector would make that three-point set a singleton. -/
theorem invariants_eq_bot_of_card_three
    (rho : Representation (ZMod 2) L V)
    (hL : Nat.card L = 3) (hdim : Module.finrank (ZMod 2) V = 2)
    (hrho : Function.Injective rho) : Representation.invariants rho = ⊥ := by
  letI : Finite V := Module.finite_of_finite (ZMod 2)
  let X := {v : V // v ≠ 0}
  letI : MulAction L X := {
    smul := fun g x => ⟨rho g x.1, by
      intro hzero
      apply x.2
      have hz := congrArg (rho g⁻¹) hzero
      simpa only [rho.inv_self_apply, map_zero] using hz⟩
    one_smul := by
      intro x
      apply Subtype.ext
      exact congrArg (fun a : Module.End (ZMod 2) V => a x.1) rho.map_one
    mul_smul := by
      intro g h x
      apply Subtype.ext
      exact congrArg (fun a : Module.End (ZMod 2) V => a x.1) (rho.map_mul g h) }
  letI : FaithfulSMul L X := {
    eq_of_smul_eq_smul := by
      intro g h hgh
      apply hrho
      apply LinearMap.ext
      intro v
      by_cases hv : v = 0
      · simp only [hv, map_zero]
      · exact congrArg (fun x : X => (x : V)) (hgh ⟨v, hv⟩) }
  have hX : Nat.card X = 3 := by
    letI : Fintype V := Fintype.ofFinite V
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
      ← Nat.card_eq_fintype_card,
      Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hdim]
    norm_num
  letI : MulAction.IsPretransitive L X :=
    faithful_three_on_three_isPretransitive L X hL hX
  apply le_antisymm _ bot_le
  intro v hv
  change v = 0
  by_contra hvzero
  let x : X := ⟨v, hvzero⟩
  have hx (y : X) : x = y := by
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq L x y
    apply Subtype.ext
    have hg' := congrArg (fun z : X => (z : V)) hg
    change rho g v = y.1 at hg'
    exact (hv g).symm.trans hg'
  letI : Subsingleton X := ⟨fun a b => (hx a).symm.trans (hx b)⟩
  have hsmall : Nat.card X = 1 := Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨x⟩⟩
  omega

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

theorem sylow_card_three (P : Sylow 3 L)
    (hL : Nat.card L = 3 ∨ Nat.card L = 6) : Nat.card P = 3 := by
  rw [Sylow.card_eq_multiplicity]
  rcases hL with h | h
  · rw [h, show Nat.factorization 3 3 = 1 by decide +kernel, pow_one]
  · rw [h, show Nat.factorization 6 3 = 1 by decide +kernel, pow_one]

/-- The actual Sylow image is used, with the same local epimorphism and
the original faithful plane. No identification of the local group is needed. -/
theorem local_sylow_invariants_eq_bot
    {H : Type} [Group H] [Finite H]
    (f : H →* L) (hf : Function.Surjective f) (P : Sylow 3 H)
    (rho : Representation (ZMod 2) L V)
    (hL : Nat.card L = 3 ∨ Nat.card L = 6)
    (hdim : Module.finrank (ZMod 2) V = 2)
    (hrho : Function.Injective rho) :
    Representation.invariants
      ((rho.comp f).comp (P : Subgroup H).subtype) = ⊥ := by
  let Q : Sylow 3 L := P.mapSurjective hf
  have hQ : Nat.card Q = 3 := sylow_card_three Q hL
  have hfixed := invariants_eq_bot_of_card_three
    (rho.comp (Q : Subgroup L).subtype) hQ hdim
    (hrho.comp Subtype.coe_injective)
  apply le_antisymm _ bot_le
  intro v hv
  have hvQ : v ∈ Representation.invariants
      (rho.comp (Q : Subgroup L).subtype) := by
    intro q
    have hq : q.1 ∈ (P : Subgroup H).map f := q.2
    obtain ⟨h, hh, he⟩ := hq
    have hhfixed := hv (⟨h, hh⟩ : (P : Subgroup H))
    change rho (f h) v = v at hhfixed
    change rho q.1 v = v
    rw [← he]
    exact hhfixed
  rw [hfixed] at hvQ
  exact hvQ

end SymmetricSubgroupAsymptotics.BinaryPlaneTernaryInvariants

end
