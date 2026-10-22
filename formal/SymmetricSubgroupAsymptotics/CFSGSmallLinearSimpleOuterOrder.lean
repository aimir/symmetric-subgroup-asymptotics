import SymmetricSubgroupAsymptotics.CFSGSufficientSimpleIndexBounds
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawChart
import SymmetricSubgroupAsymptotics.CFSGQuotientActionIndexUpper
import Mathlib.RepresentationTheory.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic

/-! A moved original vector bounds the least proper index of a faithful
linear simple group. The sufficient outer budget then bounds its actual
outer automorphism group when the original module has at most32 elements. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGSmallLinearSimpleOuterOrder
open PrimitiveSocleRawStructure

variable {k S V : Type} [Field k] [Group S] [Finite S]
  [AddCommGroup V] [Module k V] [Finite V]

omit [Finite S] in
theorem leastProperIndex_le_module_card
    (rho : Representation k S V) (hf : Function.Injective rho)
    [Nontrivial S] (ell : ℕ) (hell : LeastProperIndex S ell) :
    ell ≤ Nat.card V := by
  letI : MulAction S V := {
    smul g x := rho g x
    one_smul x := by change rho 1 x = x; rw [map_one]; rfl
    mul_smul g h x := by
      change rho (g * h) x = rho g (rho h x)
      simp only [map_mul, Module.End.mul_apply] }
  obtain ⟨g, hg⟩ := exists_ne (1 : S)
  have hnot : ¬ ∀ x : V, rho g x = x := by
    intro hfix
    apply hg
    apply hf
    apply LinearMap.ext
    intro x
    simpa only [map_one, Module.End.one_apply] using hfix x
  obtain ⟨x, hx⟩ := not_forall.mp hnot
  obtain ⟨H, hH, hcard⟩ := CFSGQuotientActionIndexUpper.exists_proper_subgroup_of_moved_point
    (MonoidHom.id S) Function.surjective_id x
    (by intro a ha; have he : a = 1 := MonoidHom.mem_ker.mp ha
        rw [he]; exact one_smul S x) g hx
  exact (hell.2 H hH).trans hcard

theorem outer_card_le_thirty_of_module_card_le_thirtyTwo
    (hindex : SufficientSimpleIndexBounds)
    (rho : Representation k S V) (hf : Function.Injective rho)
    [IsSimpleGroup S] (hnc : ¬ IsMulCommutative S)
    (hV : Nat.card V ≤ 32) : Nat.card (Outer S) ≤ 30 := by
  obtain ⟨ell, hell⟩ := exists_leastProperIndex S
  have he := (leastProperIndex_le_module_card rho hf ell hell).trans hV
  obtain ⟨_, hb⟩ := hindex S hnc ell hell
  have hellpos : 0 < ell := by
    have hfive := nonabelianSimple_leastProperIndex_five_le
      (fun h => hnc (isMulCommutative_iff.mpr h)) hell.1
    omega
  have hout := hb.log_six_of_le hellpos he
  have hl : Real.logb 2 (32 : ℝ) = 5 := by
    rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    norm_num
  norm_num only [Nat.cast_ofNat] at hout
  rw [hl] at hout
  norm_num at hout
  exact_mod_cast hout

/-- A fixed, explicitly bounded arithmetic check, independent of any group
enumeration or model identification. -/
theorem cardFactors_le_four_of_le_thirtyOne (n : ℕ) (hn : n ≤ 31) :
    ArithmeticFunction.cardFactors n ≤ 4 := by
  interval_cases n <;> decide +kernel

end SymmetricSubgroupAsymptotics.CFSGSmallLinearSimpleOuterOrder
