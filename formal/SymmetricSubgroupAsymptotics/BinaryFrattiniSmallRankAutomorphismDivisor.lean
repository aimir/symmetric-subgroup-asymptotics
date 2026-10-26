import SymmetricSubgroupAsymptotics.PrimeFrattiniAutomorphismKernelPGroup
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

/-! For an actual finite two-group of prime-Frattini rank at most three,
its actual automorphism order divides a power of two times168. The
prime-Frattini action kernel is a two-group and the same action image
embeds in the genuine binary GL of the original quotient dimension. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.BinaryFrattiniSmallRankAutomorphismDivisor

theorem binary_GL_card_dvd (d : ℕ) (hd : d ≤ 3) :
    Nat.card (Matrix.GeneralLinearGroup (Fin d) (ZMod 2)) ∣ 168 := by
  have he : Nat.card (Matrix.GeneralLinearGroup (Fin d) (ZMod 2)) =
      ∏ i : Fin d, (2 ^ d - 2 ^ i.val) := by
    rw [Matrix.card_GL_field]
    simp only [ZMod.card]
  rw [he]
  interval_cases d <;> norm_num [Fin.prod_univ_succ]

theorem automorphism_card_dvd {N : Type*} [Group N] [Finite N]
    (hN : IsPGroup 2 N)
    (hr : Module.finrank (ZMod 2) (PrimeCharacters 2 N) ≤ 3) :
    ∃ a : ℕ, Nat.card (MulAut N) ∣ 2 ^ a * 168 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Finite (MulAut N) := Finite.of_injective
    (fun a : MulAut N => (a : N → N)) DFunLike.coe_injective
  let W := PrimeAbelianization 2 N
  let d := Module.finrank (ZMod 2) W
  let b := Module.finBasis (ZMod 2) W
  let e := (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W).symm.trans
    (Matrix.GeneralLinearGroup.toLin' b).symm
  let f : MulAut N →* Matrix.GeneralLinearGroup (Fin d) (ZMod 2) :=
    e.toMonoidHom.comp (PrimeFrattiniAutomorphismAction.linearAction 2 N)
  have hk : IsPGroup 2 f.ker := by
    apply PrimeFrattiniAutomorphismKernelPGroup.isPGroup_of_trivial_primeFrattini_action 2 hN
    intro a n
    have ha : PrimeFrattiniAutomorphismAction.linearAction 2 N a.val = 1 := by
      apply e.injective
      exact a.property.trans e.map_one.symm
    change primeAbelianizationMap 2 N (Additive.ofMul (a.val n)) =
      primeAbelianizationMap 2 N (Additive.ofMul n)
    rw [← PrimeFrattiniAutomorphismAction.linearAut_apply 2 N a.val n]
    exact DFunLike.congr_fun ha (primeAbelianizationMap 2 N (Additive.ofMul n))
  obtain ⟨a,ha⟩ := IsPGroup.iff_card.mp hk
  have hd : d ≤ 3 := by
    simpa only [d,W,Subspace.dual_finrank_eq] using hr
  have himage : Nat.card f.range ∣ 168 :=
    f.range.card_subgroup_dvd_card.trans (binary_GL_card_dvd d hd)
  have hprod : Nat.card f.ker * Nat.card f.range = Nat.card (MulAut N) := by
    rw [← Subgroup.index_ker,f.ker.card_mul_index]
  refine ⟨a,?_⟩
  rw [← hprod,ha]
  exact Nat.mul_dvd_mul_left _ himage

end SymmetricSubgroupAsymptotics.BinaryFrattiniSmallRankAutomorphismDivisor
