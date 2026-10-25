import SymmetricSubgroupAsymptotics.CyclicConjugateOrbitSolvable
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Group.Commute.Hom
import Mathlib.Tactic.NormNum

/-! Two inverse-offset commutations suffice for the entire conjugate
orbit of an involution under a five-torsion element. The offsets ±1,±2
cover all differences modulo five. This is group structure on the SAME
actual elements, not a permutation action enumeration. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FiveCycleInvolutionOrbitCommutation
open CyclicConjugateOrbitSolvable

variable {G : Type} [Group G]

theorem commute_of_involutions {x z : G} (hx : x^2 = 1) (hz : z^2 = 1)
    (hprod : (x*z)^2 = 1) : Commute x z := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hx)
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hz)
  have hi : (x*z)⁻¹ = x*z := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hprod)
  show x*z = z*x
  calc x*z = (x*z)⁻¹ := hi.symm
       _ = z*x := by rw [mul_inv_rev,hzi,hxi]

theorem commuting_orbit_of_five_and_two_offsets (x y : G)
    (hx : x^2 = 1) (hy : y^5 = 1)
    (hfirst : (x*orbit x y (-1))^2 = 1)
    (hsecond : (x*orbit x y (-2))^2 = 1) :
    ∀ a b : ℤ, Commute (orbit x y a) (orbit x y b) := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hsq (n : ℤ) : (orbit x y n)^2 = 1 := by
    change ((MulAut.conj (y^n)) x)^2 = 1
    rw [←map_pow,hx,map_one]
  have hm1 := commute_of_involutions hx (hsq (-1)) hfirst
  have hm2 := commute_of_involutions hx (hsq (-2)) hsecond
  by_cases hyone : y = 1
  · intro a b
    simp only [orbit,hyone,one_zpow,MulAut.conj_apply,one_mul,inv_one,mul_one]
    exact Commute.refl x
  have ho : orderOf y = 5 := orderOf_eq_prime hy hyone
  have hreduce (n : ℤ) : orbit x y n = orbit x y (n%5) := by
    have hpow : y^n = y^(n%5) := by
      simpa only [ho,Nat.cast_ofNat] using (zpow_mod_orderOf y n).symm
    exact congrArg (fun z : G => (MulAut.conj z) x) hpow
  have hneg1 : orbit x y (-1) = orbit x y 4 := by
    simpa using hreduce (-1)
  have hneg2 : orbit x y (-2) = orbit x y 3 := by
    simpa using hreduce (-2)
  have hp1 : Commute x (orbit x y 1) := by
    have h := hm1.map (MulAut.conj (y^(1 : ℤ))).toMonoidHom
    change Commute (orbit x y 1) ((MulAut.conj (y^(1 : ℤ))) (orbit x y (-1))) at h
    rw [conjugate_orbit] at h
    have h0 : orbit x y (1+ -1) = x := by
      simp only [add_neg_cancel,orbit,zpow_zero,MulAut.conj_apply,one_mul,inv_one,mul_one]
    rw [h0] at h
    exact h.symm
  have hp2 : Commute x (orbit x y 2) := by
    have h := hm2.map (MulAut.conj (y^(2 : ℤ))).toMonoidHom
    change Commute (orbit x y 2) ((MulAut.conj (y^(2 : ℤ))) (orbit x y (-2))) at h
    rw [conjugate_orbit] at h
    have h0 : orbit x y (2+ -2) = x := by
      simp only [add_neg_cancel,orbit,zpow_zero,MulAut.conj_apply,one_mul,inv_one,mul_one]
    rw [h0] at h
    exact h.symm
  have hbase (n : ℤ) : Commute x (orbit x y n) := by
    have hlo : 0 ≤ n%5 := Int.emod_nonneg _ (by decide)
    have hhi : n%5 < 5 := Int.emod_lt_of_pos _ (by decide)
    have hc : n%5 = 0 ∨ n%5 = 1 ∨ n%5 = 2 ∨ n%5 = 3 ∨ n%5 = 4 := by omega
    rw [hreduce]
    rcases hc with h | h | h | h | h
    · rw [h]
      simpa only [orbit,zpow_zero,MulAut.conj_apply,one_mul,inv_one,mul_one] using Commute.refl x
    · simpa only [h] using hp1
    · simpa only [h] using hp2
    · simpa only [h,hneg2] using hm2
    · simpa only [h,hneg1] using hm1
  intro a b
  have h := (hbase (b-a)).map (MulAut.conj (y^a)).toMonoidHom
  change Commute (orbit x y a) ((MulAut.conj (y^a)) (orbit x y (b-a))) at h
  rw [conjugate_orbit,show a+(b-a)=b by omega] at h
  exact h

theorem isSolvable_of_five_and_two_offsets (g : Fin 2 → G)
    (hgen : Subgroup.closure (Set.range g) = ⊤)
    (hx : (g 0)^2 = 1) (hy : (g 1)^5 = 1)
    (hfirst : (g 0*orbit (g 0) (g 1) (-1))^2 = 1)
    (hsecond : (g 0*orbit (g 0) (g 1) (-2))^2 = 1) : IsSolvable G :=
  isSolvable_of_commuting_orbit g hgen
    (commuting_orbit_of_five_and_two_offsets (g 0) (g 1) hx hy hfirst hsecond)

end SymmetricSubgroupAsymptotics.FiveCycleInvolutionOrbitCommutation
