import SymmetricSubgroupAsymptotics.CFSGGTwoNaturalLieCentralizer
import SymmetricSubgroupAsymptotics.CFSGQuadraticParameterCommutant
import Mathlib.Data.Finite.Card
import Mathlib.GroupTheory.Subgroup.Center
import Lean.Elab.Tactic.Omega

/-! The natural group's actual centre is trivial for every field with
at least three elements. Two parameters separate the quadratic root
words, without an odd-characteristic assumption. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGGTwoNaturalCenter
open CFSGGTwoSerreMatrices CFSGGTwoNaturalLieCentralizer
variable (K : Type) [Field K]

theorem center_eq_bot_of_parameter (c : K) (hc0 : c ≠ 0) (hc1 : c ≠ 1) :
    Subgroup.center (naturalGroup K) = ⊥ := by
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro g hg
  have hcomm (isNegative : Bool) (i : Fin 2) (t : K) :
      (g.val : Mat K) * (rootTransvection K isNegative i t : Mat K) =
        (rootTransvection K isNegative i t : Mat K) * (g.val : Mat K) := by
    have h := congrArg (fun u : naturalGroup K => (u.val : Mat K))
      ((Subgroup.mem_center_iff.mp hg) (naturalRoot K isNegative i t))
    change (rootTransvection K isNegative i t : Mat K) * (g.val : Mat K) =
      (g.val : Mat K) * (rootTransvection K isNegative i t : Mat K) at h
    exact h.symm
  have hLie (isNegative : Bool) (i : Fin 2) :
      (g.val : Mat K) * rootMatrix K isNegative i =
        rootMatrix K isNegative i * (g.val : Mat K) := by
    exact (CFSGQuadraticParameterCommutant.commute_of_all_parameters
      (g.val : Mat K) (rootMatrix K isNegative i) (rootSecond K isNegative i) c hc0 hc1
      (fun t => by simpa only [rootTransvection_val] using hcomm isNegative i t)).1
  apply natural_eq_one_of_lie_commutation K g
  · exact hLie false
  · exact hLie true

theorem center_eq_bot [Finite K] (hcard : 3 ≤ Nat.card K) :
    Subgroup.center (naturalGroup K) = ⊥ := by
  classical
  have hex : ∃ c : K, c ≠ 0 ∧ c ≠ 1 := by
    by_contra h
    have hcover (x : K) : x = 0 ∨ x = 1 := by
      by_cases hx : x = 0
      · exact Or.inl hx
      · right
        by_contra hx1
        exact h ⟨x, hx, hx1⟩
    let encode : K → Bool := fun x => if x = 0 then false else true
    have hinj : Function.Injective encode := by
      intro x y he
      rcases hcover x with hx | hx <;> rcases hcover y with hy | hy <;>
        simp_all [encode]
    have hle := Nat.card_le_card_of_injective encode hinj
    have htwo : Nat.card Bool = 2 := by simp
    rw [htwo] at hle
    omega
  obtain ⟨c, hc0, hc1⟩ := hex
  exact center_eq_bot_of_parameter K c hc0 hc1

end SymmetricSubgroupAsymptotics.CFSGGTwoNaturalCenter
