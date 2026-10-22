import SymmetricSubgroupAsymptotics.CFSGPrimeBinaryAbelianNormal
import Mathlib.GroupTheory.Index
import Mathlib.Data.Nat.Totient

/-! A nontrivial abelian normal subgroup forces an actual order divisor,
not merely solubility. Both it and the conjugation kernel inject into the
original irreducible linear centralizer. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical IsMulCommutative

namespace SymmetricSubgroupAsymptotics.CFSGPrimeBinaryAbelianNormalOrder
open CFSGPrimeBinaryAbelianNormal CFSGIrreducibleLinearCentralizer

variable {G V : Type} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] [Finite V]
  (rho : Representation (ZMod 2) G V)

theorem card_dvd_prime_mul_pred_of_abelian_normal
    (hrho : Representation.IsIrreducible rho) (hf : Function.Injective rho)
    (hd : (Module.finrank (ZMod 2) V).Prime)
    {p : ℕ} [Fact p.Prime] (hcard : Nat.card V - 1 = p)
    (N : Subgroup G) [N.Normal] (hN : N ≠ ⊥) [IsMulCommutative N] :
    Nat.card G ∣ p * (p - 1) := by
  letI : Representation.IsIrreducible (rho.comp N.subtype) :=
    CFSGCliffordBinaryPrimeDimension.normal_restriction_irreducible rho hrho hf hd N hN
  have hcentral : Nat.card (linearCentralizer (rho.comp N.subtype)) ∣ p := by
    simpa only [hcard] using centralizer_card_dvd_nonzero_card (rho.comp N.subtype)
  have hncomm (x y : N) : (x : G) * y = y * x :=
    congrArg Subtype.val (mul_comm x y)
  have hNdiv : Nat.card N ∣ p :=
    (Subgroup.card_dvd_of_injective (commutingSubgroupHom rho N N hncomm)
      (commutingSubgroupHom_injective rho hf N N hncomm)).trans hcentral
  have hNcard : Nat.card N = p := by
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hNdiv with h | h
    · exact False.elim (hN (N.card_eq_one.mp h))
    · exact h
  letI : IsCyclic N := isCyclic_of_prime_card hNcard
  let theta : G →* MulAut N := MulAut.conjNormal
  have hkcomm (d : theta.ker) (n : N) : (d : G) * n = n * d := by
    have he : theta (d : G) = 1 := MonoidHom.mem_ker.mp d.property
    have hn := congrArg (fun f : MulAut N => (f n : G)) he
    change (d : G) * n * (d : G)⁻¹ = n at hn
    have hh := congrArg (fun z : G => z * (d : G)) hn
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hh
  have hker : Nat.card theta.ker ∣ p :=
    (Subgroup.card_dvd_of_injective (commutingSubgroupHom rho N theta.ker hkcomm)
      (commutingSubgroupHom_injective rho hf N theta.ker hkcomm)).trans hcentral
  have hrange : Nat.card theta.range ∣ p - 1 := by
    have hh := Subgroup.card_subgroup_dvd_card theta.range
    rwa [IsCyclic.card_mulAut N, hNcard, Nat.totient_prime (Fact.out : p.Prime)] at hh
  have he : Nat.card G = Nat.card theta.ker * Nat.card theta.range := by
    rw [← Subgroup.index_ker theta]
    exact theta.ker.card_mul_index.symm
  rw [he]
  exact Nat.mul_dvd_mul hker hrange

theorem card_dvd_nineHundredThirty_of_abelian_normal
    (hrho : Representation.IsIrreducible rho) (hf : Function.Injective rho)
    (hd : Module.finrank (ZMod 2) V = 5)
    (N : Subgroup G) [N.Normal] (hN : N ≠ ⊥) [IsMulCommutative N] :
    Nat.card G ∣ 930 := by
  letI : Fact (Nat.Prime 31) := ⟨by decide⟩
  have hp : (Module.finrank (ZMod 2) V).Prime := by rw [hd]; decide
  have hcard : Nat.card V - 1 = 31 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hd]
    decide
  simpa using card_dvd_prime_mul_pred_of_abelian_normal rho hrho hf hp hcard N hN

end SymmetricSubgroupAsymptotics.CFSGPrimeBinaryAbelianNormalOrder
