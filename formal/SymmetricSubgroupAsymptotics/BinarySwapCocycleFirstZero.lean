import SymmetricSubgroupAsymptotics.BinarySwapCocycle

/-! Vanishing of either restricted parity coordinate forces both.

Conjugation by the same original outside element swaps the restricted
cocycle values. Its square and the extension splitting are irrelevant.
-/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinarySwapCocycle

variable {G : Type} [Group G] (H : Subgroup G) [H.Normal]
    (σ : Representation (ZMod 2) G (ZMod 2 × ZMod 2))
    (hact : ∀ (g : G) (p : ZMod 2 × ZMod 2),
      σ g p=if g∈H then p else (p.2,p.1))
    (z : groupCohomology.cocycles₁ (Rep.of σ))

include hact

/-- This exact conjugation identity follows from the cocycle equation
and the trivial action of H; it is not a separate extension premise. -/
theorem conjugate_kernel_value (g h : G) (hh : h∈H) :
    z (g*h*g⁻¹)=σ g (z h) := by
  have hmul (a b : G) : z (a*b)=σ a (z b)+z a :=
    (groupCohomology.mem_cocycles₁_iff _).mp z.property a b
  have hc : g*h*g⁻¹∈H := Subgroup.Normal.conj_mem (H := H) inferInstance h hh g
  have he := hmul (g*h*g⁻¹) g
  have hp : (g*h*g⁻¹)*g=g*h := by group
  rw [hp,hact,if_pos hc] at he
  have he' : z (g*h*g⁻¹)+z g=σ g (z h)+z g := by
    calc
      z (g*h*g⁻¹)+z g=z g+z (g*h*g⁻¹) := add_comm _ _
      _ = z (g*h) := he.symm
      _ = σ g (z h)+z g := hmul g h
  exact add_right_cancel he'

/-- A zero first restricted coordinate forces the entire original
restricted cocycle to vanish. -/
theorem zero_on_kernel_of_first_zero (g : G) (hg : g∉H)
    (hz : ∀ h∈H,(z h).1=0) : ∀ h∈H,z h=0 := by
  intro h hh
  have hc : g*h*g⁻¹∈H := Subgroup.Normal.conj_mem (H := H) inferInstance h hh g
  have he := conjugate_kernel_value H σ hact z g h hh
  rw [hact,if_neg hg] at he
  have hs : (z h).2=0 :=
    (congrArg Prod.fst he).symm.trans (hz _ hc)
  exact Prod.ext (hz h hh) hs

/-- The statement is symmetric, so it also applies when the additive
chart's first orbit is the second orbit in an existing parity chart. -/
theorem zero_on_kernel_of_second_zero (g : G) (hg : g∉H)
    (hz : ∀ h∈H,(z h).2=0) : ∀ h∈H,z h=0 := by
  intro h hh
  have hc : g*h*g⁻¹∈H := Subgroup.Normal.conj_mem (H := H) inferInstance h hh g
  have he := conjugate_kernel_value H σ hact z g h hh
  rw [hact,if_neg hg] at he
  have hs : (z h).1=0 :=
    (congrArg Prod.snd he).symm.trans (hz _ hc)
  exact Prod.ext hs (hz h hh)

end SymmetricSubgroupAsymptotics.BinarySwapCocycle
