import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Subgroup.Basic

/-! Independent sign and coordinate exchange make every nonzero ternary
translation subgroup full. The only finite checks are scalar arithmetic
on F3 and two coordinate identities. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TwoTripleTernaryKernelIrreducible
abbrev Vector := ZMod 3 × ZMod 3
def flip (v : Vector) : Vector := (-v.1,v.2)
def swap (v : Vector) : Vector := (v.2,v.1)

private theorem normalize_first : ∀ a b : ZMod 3, a ≠ 0 →
    ((2*a)⁻¹).val • ((a,b) - flip (a,b)) = ((1 : ZMod 3),0) := by
  decide +kernel

private theorem basis_coordinates : ∀ a b : ZMod 3,
    a.val • ((1 : ZMod 3),(0 : ZMod 3)) + b.val • ((0 : ZMod 3),(1 : ZMod 3)) = (a,b) := by
  decide +kernel

theorem eq_top_of_sign_swap (A : AddSubgroup Vector) (hne : A ≠ ⊥)
    (hflip : ∀ v, v ∈ A → flip v ∈ A)
    (hswap : ∀ v, v ∈ A → swap v ∈ A) : A = ⊤ := by
  have hex : ∃ v : Vector, v ∈ A ∧ v ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply hne
    apply le_antisymm ?_ bot_le
    intro v hv
    exact AddSubgroup.mem_bot.mpr (hn v hv)
  obtain ⟨v,hv,hvne⟩ := hex
  have hw : ∃ w : Vector, w ∈ A ∧ w.1 ≠ 0 := by
    by_cases h : v.1 = 0
    · refine ⟨swap v,hswap v hv,?_⟩
      intro h2
      apply hvne
      exact Prod.ext h h2
    · exact ⟨v,hv,h⟩
  obtain ⟨w,hw,hwne⟩ := hw
  have hfirst : ((1 : ZMod 3),0) ∈ A := by
    have hh := A.nsmul_mem (A.sub_mem hw (hflip w hw)) ((2*w.1)⁻¹).val
    rw [normalize_first w.1 w.2 hwne] at hh
    exact hh
  have hsecond : ((0 : ZMod 3),1) ∈ A := hswap _ hfirst
  apply top_unique
  rintro ⟨a,b⟩ _
  rw [← basis_coordinates a b]
  exact A.add_mem (A.nsmul_mem hfirst a.val) (A.nsmul_mem hsecond b.val)

end SymmetricSubgroupAsymptotics.TwoTripleTernaryKernelIrreducible
