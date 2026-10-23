import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Algebra.Module.Prod
import Mathlib.Tactic.Module

/-! Distinct vectors of nonzero quadratic norm whose difference is
singular are independent, including in characteristic two. Therefore a
linear image preserving their projected rays and their difference ray
has the SAME scalar on both representatives, and the same tail value. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGQuadraticNonsingularPairCoupling
variable {K H T : Type*} [Field K] [AddCommGroup H] [Module K H]

theorem independent_of_singular_difference (Q : QuadraticForm K H) (h k : H)
    (hQ : Q h ≠ 0) (hne : h ≠ k) (hdiff : Q (h - k) = 0) :
    LinearIndependent K ![h, k] := by
  have hh : h ≠ 0 := by
    intro he
    apply hQ
    rw [he, QuadraticMap.map_zero]
  apply (LinearIndependent.pair_iff' hh).mpr
  intro a ha
  have hd : h - k = (1 - a) • h := by rw [← ha]; module
  rw [hd, Q.map_smul] at hdiff
  change ((1 - a) * (1 - a)) * Q h = 0 at hdiff
  have hs := (mul_eq_zero.mp hdiff).resolve_right hQ
  have hz : 1 - a = 0 := (mul_eq_zero.mp hs).elim id id
  have ha1 : a = 1 := (sub_eq_zero.mp hz).symm
  exact hne (by simpa only [ha1, one_smul] using ha)

theorem tail_eq_of_coupled_difference [AddCommGroup T] [Module K T]
    (h k : H) (hind : LinearIndependent K ![h, k])
    (x y : T) (a b c : K) (ha : a ≠ 0)
    (he : a • (h, x) - b • (k, y) = c • (h - k, (0 : T))) : x = y := by
  have hp := congrArg Prod.fst he
  change a • h - b • k = c • (h - k) at hp
  have hs : (a - c) • h + (c - b) • k = 0 := by
    calc
      (a - c) • h + (c - b) • k = (a • h - b • k) - c • (h - k) := by module
      _ = 0 := sub_eq_zero.mpr hp
  have hc := (LinearIndependent.pair_iff.mp hind) (a - c) (c - b) hs
  have hac : a = c := sub_eq_zero.mp hc.1
  have hcb : c = b := sub_eq_zero.mp hc.2
  have ht := congrArg Prod.snd he
  change a • x - b • y = c • (0 : T) at ht
  rw [← hcb, ← hac, smul_zero] at ht
  have heq : a • x = a • y := sub_eq_zero.mp ht
  exact (smul_right_injective T ha) heq

end SymmetricSubgroupAsymptotics.CFSGQuadraticNonsingularPairCoupling
