import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoZeroSixteenFourByFourCharts
import SymmetricSubgroupAsymptotics.ProductBlockFrameOriginalBlocks
import SymmetricSubgroupAsymptotics.NonbinaryFourPointPrimitivity

/-! Sixteen selected point words per original action; no enumeration of
group elements, normal subgroups, or binary modules. -/
set_option autoImplicit false
set_option maxRecDepth 10000
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoZeroSixteenPhysical
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open PrimitiveAffineDegreeTwoZeroSixteenFourByFourCharts

namespace Row28
abbrev Original := DegreeTwoZeroSixteenInterfaces.Row28Top
abbrev generators := DegreeTwoZeroSixteenInterfaces.row28Generators
abbrev chart := row28Frame
local instance : MulAction Original (Fin 4) := chart.topMulAction

def ambient (j : Fin 4) : Original :=
  ⟨generators j,Subgroup.subset_closure (Set.mem_range_self j)⟩

private def pointWords (x : Fin 16) : List (Fin 4) :=
  (#[[],[3,0,3,2],[3,2,3,2],[3,0,2,3],[2],[3,3,2],[1,0,3],[1,2,3],[0,3,2],[2,3,2],[3],[0,2,3],[3,2],[0,3],[1,3],[2,3]] : Array (List (Fin 4)))[x.val]!
private theorem pointWords_checked : ∀ x : Fin 16,
    ((pointWords x).map generators).prod (0 : Fin 16) = x := by decide +kernel

theorem transitive : MulAction.IsPretransitive Original (Fin 16) := by
  apply (MulAction.isPretransitive_iff_base (G := Original) (0 : Fin 16)).mpr
  intro x
  refine ⟨((pointWords x).map ambient).prod,?_⟩
  change (((pointWords x).map ambient).prod : Equiv.Perm (Fin 16)) 0 = x
  simpa [Subgroup.val_list_prod,ambient] using pointWords_checked x

local instance : MulAction.IsPretransitive Original (Fin 16) := transitive
abbrev fibre := originalBlockFibre chart.blockMap (0 : Fin 4)
abbrev component := originalBlockComponent chart.blockMap chart.blockMap_equivariant (0 : Fin 4)

theorem fibre_card : Nat.card fibre = 4 := by
  simpa using chart.originalFibre_card (0 : Fin 4)

theorem component_transitive : MulAction.IsPretransitive component fibre := by
  let H := MulAction.stabilizer Original (0 : Fin 4)
  letI := originalBlockStabilizerMulAction chart.blockMap chart.blockMap_equivariant (0 : Fin 4)
  letI : MulAction.IsPretransitive H fibre :=
    originalBlockStabilizer_pretransitive chart.blockMap chart.blockMap_equivariant (0 : Fin 4)
  let f : MulActionHom
      (fun h : H => (originalBlockFibreAction chart.blockMap chart.blockMap_equivariant
        (0 : Fin 4)).rangeRestrict h) fibre fibre := {
    toFun := id
    map_smul' := fun _ _ => rfl }
  exact MulAction.IsPretransitive.of_surjective_map (f := f) Function.surjective_id inferInstance


private theorem top_generator (j : Fin 4) :
    chart.top (ambient j) = row28Tops j :=
  ProductBlockFrame.ofGenerators_top_generator coordinates generators row28Tops
    row28_preserves j

def localCubic : component :=
  (originalBlockFibreAction chart.blockMap chart.blockMap_equivariant
    (0 : Fin 4)).rangeRestrict
      ⟨ambient 1, by
        change chart.top (ambient 1) 0 = 0
        rw [top_generator]
        decide +kernel⟩

theorem localCubic_cube : localCubic ^ 3 = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  apply Subtype.ext
  change generators 1 (generators 1 (generators 1 x.1)) = x.1
  have h : ∀ x : Fin 16, chart.blockMap x = 0 →
      generators 1 (generators 1 (generators 1 x)) = x := by decide +kernel
  exact h x.1 x.2

theorem localCubic_ne_one : localCubic ≠ 1 := by
  intro he
  let x : fibre := ⟨1, by decide +kernel⟩
  have hx := congrArg (fun g : component => ((g : Equiv.Perm fibre) x).1) he
  have hn : generators 1 (1 : Fin 16) ≠ 1 := by decide +kernel
  exact hn hx

theorem component_nonbinary : ¬ IsPGroup 2 component := by
  intro h
  apply localCubic_ne_one
  apply (h.powEquiv (by decide : Nat.Coprime 2 3)).injective
  simpa only [IsPGroup.powEquiv_apply,one_pow] using localCubic_cube

theorem component_primitive : MulAction.IsPreprimitive component fibre := by
  letI := component_transitive
  exact nonbinary_card_four_preprimitive component fibre_card component_nonbinary

theorem blockStabilizer_proper : MulAction.stabilizer Original (0 : Fin 4) < ⊤ := by
  apply lt_of_le_of_ne le_top
  intro he
  have hmem : ambient 2 ∈ MulAction.stabilizer Original (0 : Fin 4) := by
    rw [he]
    exact Subgroup.mem_top _
  have hz : chart.top (ambient 2) 0 = 0 := hmem
  rw [top_generator] at hz
  have hn : row28Tops 2 (0 : Fin 4) ≠ 0 := by decide +kernel
  exact hn hz

end Row28

namespace Row29
abbrev Original := DegreeTwoZeroSixteenInterfaces.Row29Top
abbrev generators := DegreeTwoZeroSixteenInterfaces.row29Generators
abbrev chart := row29Frame
local instance : MulAction Original (Fin 4) := chart.topMulAction

def ambient (j : Fin 4) : Original :=
  ⟨generators j,Subgroup.subset_closure (Set.mem_range_self j)⟩

private def pointWords (x : Fin 16) : List (Fin 4) :=
  (#[[],[3,1,2],[0,3,1,2],[1,3,1,2],[2],[1,1,3],[1,3,2],[1,0,3],[1,2],[0,0,3],[3],[2,0,3],[1,1,2],[3,2],[1,3],[0,3]] : Array (List (Fin 4)))[x.val]!
private theorem pointWords_checked : ∀ x : Fin 16,
    ((pointWords x).map generators).prod (0 : Fin 16) = x := by decide +kernel

theorem transitive : MulAction.IsPretransitive Original (Fin 16) := by
  apply (MulAction.isPretransitive_iff_base (G := Original) (0 : Fin 16)).mpr
  intro x
  refine ⟨((pointWords x).map ambient).prod,?_⟩
  change (((pointWords x).map ambient).prod : Equiv.Perm (Fin 16)) 0 = x
  simpa [Subgroup.val_list_prod,ambient] using pointWords_checked x

local instance : MulAction.IsPretransitive Original (Fin 16) := transitive
abbrev fibre := originalBlockFibre chart.blockMap (0 : Fin 4)
abbrev component := originalBlockComponent chart.blockMap chart.blockMap_equivariant (0 : Fin 4)

theorem fibre_card : Nat.card fibre = 4 := by
  simpa using chart.originalFibre_card (0 : Fin 4)

theorem component_transitive : MulAction.IsPretransitive component fibre := by
  let H := MulAction.stabilizer Original (0 : Fin 4)
  letI := originalBlockStabilizerMulAction chart.blockMap chart.blockMap_equivariant (0 : Fin 4)
  letI : MulAction.IsPretransitive H fibre :=
    originalBlockStabilizer_pretransitive chart.blockMap chart.blockMap_equivariant (0 : Fin 4)
  let f : MulActionHom
      (fun h : H => (originalBlockFibreAction chart.blockMap chart.blockMap_equivariant
        (0 : Fin 4)).rangeRestrict h) fibre fibre := {
    toFun := id
    map_smul' := fun _ _ => rfl }
  exact MulAction.IsPretransitive.of_surjective_map (f := f) Function.surjective_id inferInstance


private theorem top_generator (j : Fin 4) :
    chart.top (ambient j) = row29Tops j :=
  ProductBlockFrame.ofGenerators_top_generator coordinates generators row29Tops
    row29_preserves j

def localCubic : component :=
  (originalBlockFibreAction chart.blockMap chart.blockMap_equivariant
    (0 : Fin 4)).rangeRestrict
      ⟨ambient 1, by
        change chart.top (ambient 1) 0 = 0
        rw [top_generator]
        decide +kernel⟩

theorem localCubic_cube : localCubic ^ 3 = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  apply Subtype.ext
  change generators 1 (generators 1 (generators 1 x.1)) = x.1
  have h : ∀ x : Fin 16, chart.blockMap x = 0 →
      generators 1 (generators 1 (generators 1 x)) = x := by decide +kernel
  exact h x.1 x.2

theorem localCubic_ne_one : localCubic ≠ 1 := by
  intro he
  let x : fibre := ⟨1, by decide +kernel⟩
  have hx := congrArg (fun g : component => ((g : Equiv.Perm fibre) x).1) he
  have hn : generators 1 (1 : Fin 16) ≠ 1 := by decide +kernel
  exact hn hx

theorem component_nonbinary : ¬ IsPGroup 2 component := by
  intro h
  apply localCubic_ne_one
  apply (h.powEquiv (by decide : Nat.Coprime 2 3)).injective
  simpa only [IsPGroup.powEquiv_apply,one_pow] using localCubic_cube

theorem component_primitive : MulAction.IsPreprimitive component fibre := by
  letI := component_transitive
  exact nonbinary_card_four_preprimitive component fibre_card component_nonbinary

theorem blockStabilizer_proper : MulAction.stabilizer Original (0 : Fin 4) < ⊤ := by
  apply lt_of_le_of_ne le_top
  intro he
  have hmem : ambient 2 ∈ MulAction.stabilizer Original (0 : Fin 4) := by
    rw [he]
    exact Subgroup.mem_top _
  have hz : chart.top (ambient 2) 0 = 0 := hmem
  rw [top_generator] at hz
  have hn : row29Tops 2 (0 : Fin 4) ≠ 0 := by decide +kernel
  exact hn hz

end Row29
end PrimitiveAffineDegreeTwoZeroSixteenPhysical
end SymmetricSubgroupAsymptotics
end
