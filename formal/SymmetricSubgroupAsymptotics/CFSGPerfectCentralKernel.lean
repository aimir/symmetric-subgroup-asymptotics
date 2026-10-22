import SymmetricSubgroupAsymptotics.CFSGSimpleProjectiveDescent
import Mathlib.GroupTheory.IsPerfect
import Mathlib.Tactic.Group

/-! In a perfect group, a central kernel cannot hide a further layer of
centrality. This transports an actual central-kernel theorem through the
central quotient, without assuming representation faithfulness. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGPerfectCentralKernel
variable {G H : Type*} [Group G] [Group H]

theorem preimage_center_le_center (f : G →* H)
    (hperfect : commutator G = ⊤) (hker : f.ker ≤ Subgroup.center G) :
    (Subgroup.center H).comap f ≤ Subgroup.center G := by
  intro g hg
  let c : G → G := fun x => g * x * g⁻¹ * x⁻¹
  have hc (x : G) : c x ∈ Subgroup.center G := by
    apply hker
    change f (g * x * g⁻¹ * x⁻¹) = 1
    have hh : Commute (f g) (f x) :=
      (Subgroup.mem_center_iff.mp hg (f x)).symm
    simpa only [map_mul, map_inv, commutatorElement_def] using hh.commutator_eq
  let chi : G →* Subgroup.center G := {
    toFun := fun x => ⟨c x, hc x⟩
    map_one' := by apply Subtype.ext; change g * 1 * g⁻¹ * 1⁻¹ = 1; group
    map_mul' := by
      intro x y
      apply Subtype.ext
      change c (x * y) = c x * c y
      have he : x * c y * x⁻¹ = c y := by
        rw [Subgroup.mem_center_iff.mp (hc y) x]
        group
      calc
        c (x * y) = c x * (x * c y * x⁻¹) := by dsimp only [c]; group
        _ = c x * c y := by rw [he] }
  have hbot : ⁅chi.range, chi.range⁆ ≤ (⊥ : Subgroup (Subgroup.center G)) := by
    have hm : ⁅chi.range, chi.range⁆ ≤ commutator (Subgroup.center G) :=
      Subgroup.commutator_mono le_top le_top
    simpa only [commutator_eq_bot] using hm
  apply Subgroup.mem_center_iff.mpr
  intro x
  have hx : chi x ∈ (commutator G).map chi := ⟨x, by rw [hperfect]; trivial, rfl⟩
  rw [map_commutator_eq] at hx
  have he : chi x = 1 := hbot hx
  have hc1 : g * x * g⁻¹ * x⁻¹ = 1 := congrArg Subtype.val he
  exact (commutatorElement_eq_one_iff_mul_comm.mp hc1).symm

theorem projective_kernel_eq_center (f : G →* H) (hf : Function.Surjective f)
    (hperfect : commutator G = ⊤) (hker : f.ker ≤ Subgroup.center G) :
    ((QuotientGroup.mk' (Subgroup.center H)).comp f).ker = Subgroup.center G := by
  apply le_antisymm
  · intro g hg
    apply preimage_center_le_center f hperfect hker
    change f g ∈ Subgroup.center H
    exact (QuotientGroup.eq_one_iff _).mp hg
  · exact CFSGSimpleProjectiveDescent.center_le_projective_kernel f hf

end SymmetricSubgroupAsymptotics.CFSGPerfectCentralKernel
