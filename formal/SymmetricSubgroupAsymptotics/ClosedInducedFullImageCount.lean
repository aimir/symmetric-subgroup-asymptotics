import SymmetricSubgroupAsymptotics.OriginalKernelWholeLayerCount
import SymmetricSubgroupAsymptotics.InducedMinimumUnitLogarithmic
import SymmetricSubgroupAsymptotics.RepresentationDualSubquotientGenerators
import SymmetricSubgroupAsymptotics.FiniteGroupBinaryOrderGenerators

/-! Complete abelian-layer counts with the closed least induced capacity
and the genuine quotient rank. The representation is the action of the
actual extension quotient; its induced embedding is retained. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.ClosedInducedFullImageCount

variable {p : ℕ} [Fact p.Prime] {E B V : Type}
    [Group E] [Finite E] [Group B] [Finite B]
    [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
    (π : E →* B) (hπ : Function.Surjective π)
    (A : Rep.{0} (ZMod p) B) (chart : OriginalKernelModuleChart π A)
    (H : Subgroup E) (rho : Representation (ZMod p) H V)
    (embed : Representation.IntertwiningMap (A.ρ.comp π) (Representation.ind H.subtype rho))
    (hembed : Function.Injective embed)

include embed hembed in
omit [Finite B] in
theorem uniform : UniformSubrepresentationGeneratorBound A.ρ
    (InducedMinimumUniformCapacity.capacity H rho) := by
  apply UniformSubrepresentationGeneratorBound.of_comp A.ρ π
  exact (InducedMinimumUniformCapacity.uniform H rho).of_injective embed hembed

include hπ chart embed hembed in
/-- Every invariant intersection and every lift is counted, without a
split-extension or separate ordinary-generation premise. -/
theorem card_fullImage_le_capacity_add_rank :
    Nat.card (FiniteAbelianExtensionWholeLayerCount.FullImage π) ≤
      (Nat.card A)^(InducedMinimumUniformCapacity.capacity H rho+MarkedC4.genRank B) := by
  obtain ⟨S,hcard,hgen⟩ := MarkedC4.genRank_spec (G := B)
  let eS := Fintype.equivFin S
  let f : Fin (Fintype.card S) → B := fun i => (eS.symm i : B)
  have hrange : Set.range f=(S : Set B) := by
    ext b
    constructor
    · rintro ⟨i,rfl⟩
      exact (eS.symm i).property
    · intro hb
      refine ⟨eS ⟨b,hb⟩,?_⟩
      exact congrArg (fun z : S => (z : B)) (eS.symm_apply_apply ⟨b,hb⟩)
  have hf : Subgroup.closure (Set.range f)=⊤ := by rw [hrange]; exact hgen
  have hU : UniformSubrepresentationGeneratorBound A.ρ
      (InducedMinimumUniformCapacity.capacity H rho) := by
    apply UniformSubrepresentationGeneratorBound.of_comp A.ρ π
    exact (InducedMinimumUniformCapacity.uniform H rho).of_injective embed hembed
  have h : Nat.card (FiniteAbelianExtensionWholeLayerCount.FullImage π) ≤
      (Nat.card A)^(InducedMinimumUniformCapacity.capacity H rho+Fintype.card S) :=
    OriginalKernelWholeLayerCount.card_fullImage_le_of_uniform
      (π := π) (hπ := hπ) (A := A) (chart := chart)
      (H := InducedMinimumUniformCapacity.capacity H rho) hU f hf
  simpa only [Fintype.card_coe,hcard] using h

theorem capacity_le_root_log (ht : 2≤H.index) :
    (InducedMinimumUniformCapacity.capacity H rho : ℝ)≤
      (Module.finrank (ZMod p) V : ℝ)*H.index /
        Real.sqrt (Real.logb 2 (H.index : ℝ)) :=
  InducedMinimumUnitLogarithmic.logarithmic_real H rho ht

end SymmetricSubgroupAsymptotics.ClosedInducedFullImageCount
