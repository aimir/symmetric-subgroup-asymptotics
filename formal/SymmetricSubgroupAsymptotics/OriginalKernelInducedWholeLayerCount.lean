import SymmetricSubgroupAsymptotics.OriginalKernelWholeLayerCount
import SymmetricSubgroupAsymptotics.TraceyRefinedInducedModuleProof

/-! The internally proved induced-module theorem pays the invariant-kernel
part of a COMPLETE elementary extension layer. The actual module embedding
and quotient generating tuple are retained; the capacity is constructed,
not an additional published or project-owned assumption. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.OriginalKernelInducedWholeLayerCount

variable {p : ℕ} [Fact p.Prime] {E Q V : Type}
    [Group E] [Finite E] [Group Q] [Finite Q]
    [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]

/-- All five numerical capacity estimates hold for the same actual layer
whose complete lift count is bounded here. No split-extension premise. -/
theorem exists_capacity_fullImage_le
    (π : E →* Q) (hπ : Function.Surjective π)
    (A : Rep.{0} (ZMod p) Q) (chart : OriginalKernelModuleChart π A)
    (H : Subgroup Q) (hindex : 2 ≤ H.index)
    (rho : Representation (ZMod p) H V)
    (embed : A.ρ.IntertwiningMap (Representation.ind H.subtype rho))
    (hembed : Function.Injective embed)
    {d : ℕ} (f : Fin d → Q) (hf : Subgroup.closure (Set.range f) = ⊤) :
    ∃ cap : ℕ,
      TraceyRefinedInducedCapacityBounds p (Module.finrank (ZMod p) V) H.index (cap : ℝ) ∧
      Nat.card (FiniteAbelianExtensionWholeLayerCount.FullImage π) ≤
        (Nat.card A)^(cap+d) := by
  obtain ⟨cap,hbounds,hgen⟩ := traceyRefinedInducedModuleInput_proved p Q H hindex V rho
  refine ⟨cap,hbounds,?_⟩
  exact OriginalKernelWholeLayerCount.card_fullImage_le_of_uniform π hπ A chart
    (UniformSubrepresentationGeneratorBound.of_injective hgen embed hembed) f hf

/-- A direct logarithmic exponent for the complete layer, supplied by the
closed induced-module proof rather than a capacity input. -/
theorem fullImage_le_logarithmic
    (π : E →* Q) (hπ : Function.Surjective π)
    (A : Rep.{0} (ZMod p) Q) (chart : OriginalKernelModuleChart π A)
    (H : Subgroup Q) (hindex : 2 ≤ H.index)
    (rho : Representation (ZMod p) H V)
    (embed : A.ρ.IntertwiningMap (Representation.ind H.subtype rho))
    (hembed : Function.Injective embed)
    {d : ℕ} (f : Fin d → Q) (hf : Subgroup.closure (Set.range f) = ⊤) :
    Nat.card (FiniteAbelianExtensionWholeLayerCount.FullImage π) ≤
      (Nat.card A)^(traceyInducedGeneratorCeiling (Module.finrank (ZMod p) V) H.index+d) := by
  letI : Finite A := Finite.of_equiv π.ker chart.equiv.symm.toEquiv
  obtain ⟨cap,hbounds,hcount⟩ := exists_capacity_fullImage_le π hπ A chart H hindex rho
    embed hembed f hf
  have hcap : cap ≤ traceyInducedGeneratorCeiling (Module.finrank (ZMod p) V) H.index := by
    exact_mod_cast hbounds.logarithmic
  have hpos : 1 ≤ Nat.card A := Nat.card_pos
  exact hcount.trans (Nat.pow_le_pow_right hpos (Nat.add_le_add_right hcap d))

end SymmetricSubgroupAsymptotics.OriginalKernelInducedWholeLayerCount
