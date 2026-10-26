import SymmetricSubgroupAsymptotics.PrimeFrattiniAutomorphismKernelPGroup
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

/-! Divisibility of the actual automorphism group of a finite p-group.
The genuine prime-Frattini action has p-group kernel. A common divisor
for the possible linear image orders therefore bounds the automorphism
order, with that same prime-power kernel factor retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.PrimeFrattiniSmallRankAutomorphismDivisor

theorem automorphism_card_dvd (p r C : ℕ) [Fact p.Prime] {N : Type*} [Group N] [Finite N]
    (hN : IsPGroup p N)
    (hr : Module.finrank (ZMod p) (PrimeCharacters p N) ≤ r)
    (hGL : ∀ d : ℕ, d ≤ r → Nat.card (Matrix.GeneralLinearGroup (Fin d) (ZMod p)) ∣ C) :
    ∃ a : ℕ, Nat.card (MulAut N) ∣ p ^ a * C := by
  letI : Finite (MulAut N) := Finite.of_injective
    (fun a : MulAut N => (a : N → N)) DFunLike.coe_injective
  let W := PrimeAbelianization p N
  let d := Module.finrank (ZMod p) W
  let b := Module.finBasis (ZMod p) W
  let e := (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod p) W).symm.trans
    (Matrix.GeneralLinearGroup.toLin' b).symm
  let f : MulAut N →* Matrix.GeneralLinearGroup (Fin d) (ZMod p) :=
    e.toMonoidHom.comp (PrimeFrattiniAutomorphismAction.linearAction p N)
  have hk : IsPGroup p f.ker := by
    apply PrimeFrattiniAutomorphismKernelPGroup.isPGroup_of_trivial_primeFrattini_action p hN
    intro a n
    have ha : PrimeFrattiniAutomorphismAction.linearAction p N a.val = 1 := by
      apply e.injective
      exact a.property.trans e.map_one.symm
    change primeAbelianizationMap p N (Additive.ofMul (a.val n)) =
      primeAbelianizationMap p N (Additive.ofMul n)
    rw [← PrimeFrattiniAutomorphismAction.linearAut_apply p N a.val n]
    exact DFunLike.congr_fun ha (primeAbelianizationMap p N (Additive.ofMul n))
  obtain ⟨a,ha⟩ := IsPGroup.iff_card.mp hk
  have hd : d ≤ r := by
    simpa only [d,W,Subspace.dual_finrank_eq] using hr
  have himage : Nat.card f.range ∣ C :=
    f.range.card_subgroup_dvd_card.trans (hGL d hd)
  have hprod : Nat.card f.ker * Nat.card f.range = Nat.card (MulAut N) := by
    rw [← Subgroup.index_ker,f.ker.card_mul_index]
  refine ⟨a,?_⟩
  rw [← hprod,ha]
  exact Nat.mul_dvd_mul_left _ himage

private instance ternaryPrime : Fact (Nat.Prime 3) := ⟨by decide⟩

theorem ternary_GL_card_dvd (d : ℕ) (hd : d ≤ 3) :
    Nat.card (Matrix.GeneralLinearGroup (Fin d) (ZMod 3)) ∣ 11232 := by
  have he : Nat.card (Matrix.GeneralLinearGroup (Fin d) (ZMod 3)) =
      ∏ i : Fin d, (3 ^ d - 3 ^ i.val) := by
    rw [Matrix.card_GL_field]
    simp only [ZMod.card]
  rw [he]
  interval_cases d <;> norm_num [Fin.prod_univ_succ]

theorem ternary_automorphism_card_dvd {N : Type*} [Group N] [Finite N]
    (hN : IsPGroup 3 N)
    (hr : Module.finrank (ZMod 3) (PrimeCharacters 3 N) ≤ 3) :
    ∃ a : ℕ, Nat.card (MulAut N) ∣ 3 ^ a * 11232 := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact automorphism_card_dvd 3 3 11232 hN hr ternary_GL_card_dvd

end SymmetricSubgroupAsymptotics.PrimeFrattiniSmallRankAutomorphismDivisor
