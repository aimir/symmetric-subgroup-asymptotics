import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic.Group

/-! An abstract rank-one Bruhat closure engine. It converts the literal
torus-normalization and `wUw` calculation into a two-cell cover of the
generated group. No finite-group classification or group-order input is
used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGRankOneBruhat
variable {G : Type*} [Group G]

def Cell (B U : Subgroup G) (w g : G) : Prop :=
  g ∈ B ∨ ∃ b ∈ B, ∃ u ∈ U, g = b * w * u

theorem cell_left_mul (B U : Subgroup G) (w b g : G) (hb : b ∈ B)
    (hg : Cell B U w g) : Cell B U w (b * g) := by
  rcases hg with hg | ⟨c,hc,u,hu,rfl⟩
  · exact Or.inl (B.mul_mem hb hg)
  · exact Or.inr ⟨b*c,B.mul_mem hb hc,u,hu,by group⟩

theorem cell_right_unipotent (B U : Subgroup G) (w : G) (hUB : U ≤ B)
    (u g : G) (hu : u ∈ U) (hg : Cell B U w g) : Cell B U w (g * u) := by
  rcases hg with hg | ⟨b,hb,v,hv,rfl⟩
  · exact Or.inl (B.mul_mem hg (hUB hu))
  · exact Or.inr ⟨b,hb,v*u,U.mul_mem hv hu,by group⟩

theorem cell_right_torus (B U T : Subgroup G) (w : G) (hTB : T ≤ B)
    (hTN : T ≤ Subgroup.normalizer (U : Set G))
    (hWT : ∀ t ∈ T, w * t * w⁻¹ ∈ T)
    (t g : G) (ht : t ∈ T) (hg : Cell B U w g) : Cell B U w (g * t) := by
  rcases hg with hg | ⟨b,hb,u,hu,rfl⟩
  · exact Or.inl (B.mul_mem hg (hTB ht))
  · have hv : t⁻¹ * u * t ∈ U := by
      have hN := hTN (T.inv_mem ht)
      simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp hN u).mp hu
    exact Or.inr ⟨b*(w*t*w⁻¹),B.mul_mem hb (hTB (hWT t ht)),
      t⁻¹*u*t,hv,by group⟩

theorem cell_right_weyl (B U : Subgroup G) (w : G)
    (hWU : ∀ u ∈ U, Cell B U w (w * u * w))
    (g : G) (hg : Cell B U w g) : Cell B U w (g * w) := by
  rcases hg with hg | ⟨b,hb,u,hu,rfl⟩
  · exact Or.inr ⟨g,hg,1,U.one_mem,by simp⟩
  · simpa only [mul_assoc] using cell_left_mul B U w b (w*u*w) hb (hWU u hu)

private def rightStabilizer (C : Set G) : Subgroup G where
  carrier := {x | (∀ g ∈ C, g*x ∈ C) ∧ (∀ g ∈ C, g*x⁻¹ ∈ C)}
  one_mem' := by constructor <;> intro g hg <;> simpa using hg
  mul_mem' := by
    intro x y hx hy
    constructor
    · intro g hg
      simpa only [mul_assoc] using hy.1 (g*x) (hx.1 g hg)
    · intro g hg
      simpa only [mul_inv_rev,mul_assoc] using hx.2 (g*y⁻¹) (hy.2 g hg)
  inv_mem' := by
    intro x hx
    constructor
    · exact hx.2
    · intro g hg
      simpa only [inv_inv] using hx.1 g hg

theorem closure_le_two_cells (B U T : Subgroup G) (w : G)
    (hUB : U ≤ B) (hTB : T ≤ B) (hB : B ≤ U ⊔ T)
    (hTN : T ≤ Subgroup.normalizer (U : Set G))
    (hWT : ∀ t ∈ T, w*t*w⁻¹ ∈ T) (hww : w*w = 1)
    (hWU : ∀ u ∈ U, Cell B U w (w*u*w)) :
    ∀ g ∈ Subgroup.closure ((B : Set G) ∪ {w}), Cell B U w g := by
  let C : Set G := {g | Cell B U w g}
  let D : Subgroup G := rightStabilizer C
  have hUD : U ≤ D := by
    intro u hu
    exact ⟨fun g hg => cell_right_unipotent B U w hUB u g hu hg,
      fun g hg => cell_right_unipotent B U w hUB u⁻¹ g (U.inv_mem hu) hg⟩
  have hTD : T ≤ D := by
    intro t ht
    exact ⟨fun g hg => cell_right_torus B U T w hTB hTN hWT t g ht hg,
      fun g hg => cell_right_torus B U T w hTB hTN hWT t⁻¹ g (T.inv_mem ht) hg⟩
  have hwD : w ∈ D := by
    have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
    constructor
    · exact fun g hg => cell_right_weyl B U w hWU g hg
    · intro g hg
      rw [hwi]
      exact cell_right_weyl B U w hWU g hg
  have hBD : B ≤ D := hB.trans (sup_le hUD hTD)
  have hle : Subgroup.closure ((B : Set G) ∪ {w}) ≤ D := by
    apply (Subgroup.closure_le D).mpr
    intro x hx
    rcases hx with hx | hx
    · exact hBD hx
    · rcases Set.mem_singleton_iff.mp hx with rfl
      exact hwD
  intro g hg
  have h := (hle hg).1 1 (Or.inl B.one_mem)
  simpa only [one_mul] using h

end SymmetricSubgroupAsymptotics.CFSGRankOneBruhat
