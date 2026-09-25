import SymmetricSubgroupAsymptotics.BinaryExceptionalCarriers
import SymmetricSubgroupAsymptotics.BinaryPairFrames
import SymmetricSubgroupAsymptotics.GeneratedNormal8.Registry8T16
import SymmetricSubgroupAsymptotics.GeneratedNormal8.Registry8T20
import SymmetricSubgroupAsymptotics.GeneratedNormal8.Registry8T21

/-! The three width-eight exceptional charts are bound to the original
normal-registry rows. Reconstruction retains the full arbitrary exterior. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace SymmetricSubgroupAsymptotics

namespace BinaryNormalTransport8T16
local instance : Group BinaryNormal8T16.Source := BinaryMenuCayley8T16.group
abbrev Original := Subgroup.closure (Set.range BinaryMenuCayley8T16.generators)
abbrev chart := BinaryChart8T16.chart

theorem source_eq : chart.source=Original := by
  change Subgroup.closure (Set.range BinaryChart8T16.alphaGenerators)=_
  have he : BinaryChart8T16.alphaGenerators=BinaryMenuCayley8T16.generators := by
    funext j
    revert j; decide +kernel
  rw [he]

def originalNormal : Subgroup Original :=
  BinaryNormal8T16.N1.kernel.map BinaryMenuCayley8T16.originalEquiv.toMonoidHom

theorem axis_eq : chart.axis=originalNormal.map Original.subtype := by
  have he : ∀ j : Fin 1, BinaryChart8T16.axisGenerators j=
      (BinaryMenuCayley8T16.originalEquiv (BinaryNormal8T16.N1.normalGenerators j) :
        Equiv.Perm (Fin 8)) := by
    intro j
    apply Equiv.ext
    intro x
    change BinaryChart8T16.axisGenerators j x=
      BinaryMenuCayley8T16.certificate.toCayley.elements
        (BinaryNormal8T16.N1.normalGenerators j).index x
    rw [binaryPair_source_row_apply]
    revert x j
    decide +kernel
  change Subgroup.closure (Set.range BinaryChart8T16.axisGenerators)=_
  unfold originalNormal BinaryNormal8T16.N1.kernel
  rw [MonoidHom.map_closure,MonoidHom.map_closure]
  congr 1
  ext x
  simp only [Set.mem_range,Set.mem_image]
  constructor
  · rintro ⟨j,rfl⟩
    exact ⟨BinaryMenuCayley8T16.originalEquiv (BinaryNormal8T16.N1.normalGenerators j),
      ⟨BinaryNormal8T16.N1.normalGenerators j,⟨j,rfl⟩,rfl⟩,(he j).symm⟩
  · rintro ⟨u,⟨y,⟨j,rfl⟩,rfl⟩,rfl⟩
    exact ⟨j,he j⟩

theorem alpha_kernel_original :
    chart.alpha.ker.map chart.source.subtype=originalNormal.map Original.subtype :=
  chart.alpha_kernel.trans axis_eq

/-- The specified original normal is the actual source axis. -/
theorem reconstruct_original_normal {E : Type*} [Group E]
    (H : Subgroup (chart.source×E))
    (haxis : ∀ x : chart.source,
      (x : Equiv.Perm (Fin 8))∈originalNormal.map Original.subtype → (x,1)∈H) :
    ((chart.transport H).map chart.carrierMap).comap chart.sourceMap=H :=
  chart.transport_reconstruct H (fun x hx => haxis x (axis_eq ▸ hx))

end BinaryNormalTransport8T16

namespace BinaryNormalTransport8T20
local instance : Group BinaryNormal8T20.Source := BinaryMenuCayley8T20.group
abbrev Original := Subgroup.closure (Set.range BinaryMenuCayley8T20.generators)
abbrev chart := BinaryChart8T20.chart

theorem source_eq : chart.source=Original := by
  change Subgroup.closure (Set.range BinaryChart8T20.alphaGenerators)=_
  have he : BinaryChart8T20.alphaGenerators=BinaryMenuCayley8T20.generators := by
    funext j
    revert j; decide +kernel
  rw [he]

def originalNormal : Subgroup Original :=
  BinaryNormal8T20.N1.kernel.map BinaryMenuCayley8T20.originalEquiv.toMonoidHom

theorem axis_eq : chart.axis=originalNormal.map Original.subtype := by
  have he : ∀ j : Fin 1, BinaryChart8T20.axisGenerators j=
      (BinaryMenuCayley8T20.originalEquiv (BinaryNormal8T20.N1.normalGenerators j) :
        Equiv.Perm (Fin 8)) := by
    intro j
    apply Equiv.ext
    intro x
    change BinaryChart8T20.axisGenerators j x=
      BinaryMenuCayley8T20.certificate.toCayley.elements
        (BinaryNormal8T20.N1.normalGenerators j).index x
    rw [binaryPair_source_row_apply]
    revert x j
    decide +kernel
  change Subgroup.closure (Set.range BinaryChart8T20.axisGenerators)=_
  unfold originalNormal BinaryNormal8T20.N1.kernel
  rw [MonoidHom.map_closure,MonoidHom.map_closure]
  congr 1
  ext x
  simp only [Set.mem_range,Set.mem_image]
  constructor
  · rintro ⟨j,rfl⟩
    exact ⟨BinaryMenuCayley8T20.originalEquiv (BinaryNormal8T20.N1.normalGenerators j),
      ⟨BinaryNormal8T20.N1.normalGenerators j,⟨j,rfl⟩,rfl⟩,(he j).symm⟩
  · rintro ⟨u,⟨y,⟨j,rfl⟩,rfl⟩,rfl⟩
    exact ⟨j,he j⟩

theorem alpha_kernel_original :
    chart.alpha.ker.map chart.source.subtype=originalNormal.map Original.subtype :=
  chart.alpha_kernel.trans axis_eq

/-- The specified original normal is the actual source axis. -/
theorem reconstruct_original_normal {E : Type*} [Group E]
    (H : Subgroup (chart.source×E))
    (haxis : ∀ x : chart.source,
      (x : Equiv.Perm (Fin 8))∈originalNormal.map Original.subtype → (x,1)∈H) :
    ((chart.transport H).map chart.carrierMap).comap chart.sourceMap=H :=
  chart.transport_reconstruct H (fun x hx => haxis x (axis_eq ▸ hx))

end BinaryNormalTransport8T20

namespace BinaryNormalTransport8T21
local instance : Group BinaryNormal8T21.Source := BinaryMenuCayley8T21.group
abbrev Original := Subgroup.closure (Set.range BinaryMenuCayley8T21.generators)
abbrev chart := BinaryChart8T21.chart

theorem source_eq : chart.source=Original := by
  change Subgroup.closure (Set.range BinaryChart8T21.alphaGenerators)=_
  have he : BinaryChart8T21.alphaGenerators=BinaryMenuCayley8T21.generators := by
    funext j
    revert j; decide +kernel
  rw [he]

def originalNormal : Subgroup Original :=
  BinaryNormal8T21.N1.kernel.map BinaryMenuCayley8T21.originalEquiv.toMonoidHom

theorem axis_eq : chart.axis=originalNormal.map Original.subtype := by
  have he : ∀ j : Fin 1, BinaryChart8T21.axisGenerators j=
      (BinaryMenuCayley8T21.originalEquiv (BinaryNormal8T21.N1.normalGenerators j) :
        Equiv.Perm (Fin 8)) := by
    intro j
    apply Equiv.ext
    intro x
    change BinaryChart8T21.axisGenerators j x=
      BinaryMenuCayley8T21.certificate.toCayley.elements
        (BinaryNormal8T21.N1.normalGenerators j).index x
    rw [binaryPair_source_row_apply]
    revert x j
    decide +kernel
  change Subgroup.closure (Set.range BinaryChart8T21.axisGenerators)=_
  unfold originalNormal BinaryNormal8T21.N1.kernel
  rw [MonoidHom.map_closure,MonoidHom.map_closure]
  congr 1
  ext x
  simp only [Set.mem_range,Set.mem_image]
  constructor
  · rintro ⟨j,rfl⟩
    exact ⟨BinaryMenuCayley8T21.originalEquiv (BinaryNormal8T21.N1.normalGenerators j),
      ⟨BinaryNormal8T21.N1.normalGenerators j,⟨j,rfl⟩,rfl⟩,(he j).symm⟩
  · rintro ⟨u,⟨y,⟨j,rfl⟩,rfl⟩,rfl⟩
    exact ⟨j,he j⟩

theorem alpha_kernel_original :
    chart.alpha.ker.map chart.source.subtype=originalNormal.map Original.subtype :=
  chart.alpha_kernel.trans axis_eq

/-- The specified original normal is the actual source axis. -/
theorem reconstruct_original_normal {E : Type*} [Group E]
    (H : Subgroup (chart.source×E))
    (haxis : ∀ x : chart.source,
      (x : Equiv.Perm (Fin 8))∈originalNormal.map Original.subtype → (x,1)∈H) :
    ((chart.transport H).map chart.carrierMap).comap chart.sourceMap=H :=
  chart.transport_reconstruct H (fun x hx => haxis x (axis_eq ▸ hx))

end BinaryNormalTransport8T21
end SymmetricSubgroupAsymptotics
