import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.Field.Defs

/-! Rank-one root commutation over every characteristic. The only
duality input is reciprocity of the two zero-pairing conditions. -/
set_option autoImplicit false

namespace SymmetricSubgroupAsymptotics.CFSGRankOneRootCommutation
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem commute_rankOne_iff (u v : V) (f g : V →ₗ[K] K) (hf : f ≠ 0)
    (hfu : f u = 0) (hreciprocal : f v = 0 ↔ g u = 0) :
    Commute (f.smulRight u) (g.smulRight v) ↔ f v = 0 := by
  constructor
  · intro h
    by_contra hv
    have hgu : g u ≠ 0 := fun hh => hv (hreciprocal.mpr hh)
    have hex : ∃ x : V, f x ≠ 0 := by
      by_contra hn
      apply hf
      apply LinearMap.ext
      intro x
      change f x = 0
      by_contra hx
      exact hn ⟨x, hx⟩
    obtain ⟨x, hx⟩ := hex
    have hh := congrArg (fun A : Module.End K V => f (A x)) h.eq
    have hz : (f x * g u) * f v = 0 := by
      simpa only [Module.End.mul_apply, LinearMap.smulRight_apply, map_smul,
        smul_eq_mul, hfu, mul_zero, mul_assoc] using hh.symm
    exact (mul_ne_zero (mul_ne_zero hx hgu) hv) hz
  · intro hv
    have hgu : g u = 0 := hreciprocal.mp hv
    change (f.smulRight u) * (g.smulRight v) = (g.smulRight v) * (f.smulRight u)
    apply LinearMap.ext
    intro x
    simp only [Module.End.mul_apply, LinearMap.smulRight_apply, map_smul,
      hv, hgu, zero_smul, smul_zero]

theorem commute_one_add_rankOne_iff (u v : V) (f g : V →ₗ[K] K) (hf : f ≠ 0)
    (hfu : f u = 0) (hreciprocal : f v = 0 ↔ g u = 0) :
    Commute (1 + f.smulRight u : Module.End K V) (1 + g.smulRight v) ↔ f v = 0 := by
  constructor
  · intro h
    have hh := (h.sub_left (Commute.one_left _)).sub_right (Commute.one_right _)
    have hc : Commute (f.smulRight u) (g.smulRight v) := by
      simpa only [add_sub_cancel_left] using hh
    exact (commute_rankOne_iff u v f g hf hfu hreciprocal).mp hc
  · intro h
    have hc := (commute_rankOne_iff u v f g hf hfu hreciprocal).mpr h
    exact (Commute.one_left (1 + g.smulRight v)).add_left ((Commute.one_right _).add_right hc)

end SymmetricSubgroupAsymptotics.CFSGRankOneRootCommutation
