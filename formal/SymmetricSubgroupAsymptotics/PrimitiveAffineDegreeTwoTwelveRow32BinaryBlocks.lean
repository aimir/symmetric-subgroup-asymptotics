import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow32BinaryChart
import SymmetricSubgroupAsymptotics.PermutationBinaryThreeFourAugmentation

/-!
# Original binary block coordinates for row 32

The three coordinate types are literal fibres inside the original twelve
points. The actual binary normal kernel preserves each fibre and acts
transitively on its four points. Coordinate restrictions retain an
arbitrary original top subrepresentation and are jointly injective.

Consequently the extremal binary head identifies the original numerator
with the actual nine-dimensional augmentation sum. No splitting of a
correlated source is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwelveRow32BinaryBlocks


abbrev P := PrimitiveAffineDegreeTwoTwelveRow32BinaryChart.beta.ker

def label (x : Fin 12) : Fin 3 := ⟨x.val % 3, Nat.mod_lt _ (by decide)⟩

abbrev Fiber (i : Fin 3) := {x : Fin 12 // label x = i}

theorem point_label (i : Fin 3) (j : Fin 4) : label (PrimitiveAffineDegreeTwoTwelveRow32AugmentationGenerators.point i j) = i := by
  decide +kernel +revert

def fiberEquiv (i : Fin 3) : Fin 4 ≃ Fiber i :=
  Equiv.ofBijective (fun j ↦ ⟨PrimitiveAffineDegreeTwoTwelveRow32AugmentationGenerators.point i j, point_label i j⟩) (by
    constructor
    · intro j k h
      have hp : (i, j) = (i, k) :=
        PrimitiveAffineDegreeTwoTwelveRow32AugmentationGenerators.point_bijective.1
          (congrArg (fun x : Fiber i ↦ x.val) h)
      exact congrArg Prod.snd hp
    · intro x
      obtain ⟨⟨j, k⟩, h⟩ := PrimitiveAffineDegreeTwoTwelveRow32AugmentationGenerators.point_bijective.2 x.val
      have hj : j = i := (point_label j k).symm.trans
        ((congrArg label h).trans x.property)
      subst j
      exact ⟨k, Subtype.ext h⟩)

theorem fiber_card (i : Fin 3) : Nat.card (Fiber i) = 4 := by
  rw [← Nat.card_congr (fiberEquiv i)]
  exact Nat.card_fin 4

private theorem translation_preserves_label (v : PrimitiveAffineDegreeTwoTwelveRow32BinaryChart.Translation) (x : Fin 12) :
    label (PrimitiveAffineDegreeTwoTwelveRow32BinaryChart.literalAction (SemidirectProduct.inl v) x) = label x := by
  decide +kernel +revert

theorem kernel_preserves_label (g : P) (x : Fin 12) :
    label ((g : PrimitiveAffineDegreeTwoTwelveRow32BinaryChart.Top) • x) = label x := by
  obtain ⟨v, rfl⟩ := PrimitiveAffineDegreeTwoTwelveRow32BinaryChart.binaryKernelEquiv.surjective g
  change label (PrimitiveAffineDegreeTwoTwelveRow32BinaryChart.literalAction (SemidirectProduct.inl v) x) = label x
  exact translation_preserves_label v x

instance fiberMulAction (i : Fin 3) : MulAction P (Fiber i) where
  smul g x := ⟨(g : PrimitiveAffineDegreeTwoTwelveRow32BinaryChart.Top) • x.val, (kernel_preserves_label g x.val).trans x.property⟩
  one_smul x := Subtype.ext (one_smul PrimitiveAffineDegreeTwoTwelveRow32BinaryChart.Top x.val)
  mul_smul g h x := Subtype.ext (mul_smul (g : PrimitiveAffineDegreeTwoTwelveRow32BinaryChart.Top) (h : PrimitiveAffineDegreeTwoTwelveRow32BinaryChart.Top) x.val)

private theorem translation_cover (i : Fin 3) (j k : Fin 4) :
    ∃ v : PrimitiveAffineDegreeTwoTwelveRow32BinaryChart.Translation,
      PrimitiveAffineDegreeTwoTwelveRow32BinaryChart.literalAction (SemidirectProduct.inl v) (PrimitiveAffineDegreeTwoTwelveRow32AugmentationGenerators.point i j) = PrimitiveAffineDegreeTwoTwelveRow32AugmentationGenerators.point i k := by
  decide +kernel +revert

instance fiberPretransitive (i : Fin 3) : MulAction.IsPretransitive P (Fiber i) := by
  constructor
  intro x y
  obtain ⟨j, rfl⟩ := (fiberEquiv i).surjective x
  obtain ⟨k, rfl⟩ := (fiberEquiv i).surjective y
  obtain ⟨v, hv⟩ := translation_cover i j k
  exact ⟨PrimitiveAffineDegreeTwoTwelveRow32BinaryChart.binaryKernelEquiv v, Subtype.ext hv⟩

def basepoint (i : Fin 3) : Fiber i := fiberEquiv i 0

def restricted (B : Subrepresentation PrimitiveAffineDegreeTwoTwelveRow32AugmentationGenerators.representation) :
    Representation (ZMod 2) P B.toSubmodule :=
  B.toRepresentation.comp PrimitiveAffineDegreeTwoTwelveRow32BinaryChart.beta.ker.subtype

/-- Restriction to a literal block intertwines the actual kernel action. -/
def coordinate (B : Subrepresentation PrimitiveAffineDegreeTwoTwelveRow32AugmentationGenerators.representation) (i : Fin 3) :
    (restricted B).IntertwiningMap
      (permutationFunctionRepresentation (ZMod 2) P (Fiber i)) where
  toLinearMap :=
    { toFun := fun v x ↦ v.val x.val
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  isIntertwining' := by
    intro g
    apply LinearMap.ext
    intro v
    funext x
    rfl

theorem coordinates_injective (B : Subrepresentation PrimitiveAffineDegreeTwoTwelveRow32AugmentationGenerators.representation) :
    Function.Injective (fun v i ↦ coordinate B i v) := by
  intro v w h
  apply Subtype.ext
  funext x
  exact congrFun (congrFun h (label x)) ⟨x, rfl⟩

attribute [local instance] Fintype.ofFinite

private theorem coordinateSum_eq_sum (i : Fin 3) (f : Fiber i → ZMod 2) :
    PermutationAugmentation.coordinateSum (ZMod 2) (Fiber i) f = ∑ x : Fiber i, f x := by
  unfold PermutationAugmentation.coordinateSum
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  congr 1 <;> ext x <;> simp

theorem coordinate_sum (B : Subrepresentation PrimitiveAffineDegreeTwoTwelveRow32AugmentationGenerators.representation)
    (v : B.toSubmodule) (i : Fin 3) :
    (∑ x : Fiber i, coordinate B i v x) = ∑ j : Fin 4, v.val (PrimitiveAffineDegreeTwoTwelveRow32AugmentationGenerators.point i j) :=
  (Equiv.sum_comp (fiberEquiv i) (coordinate B i v)).symm

theorem augmentation_mem_iff (v : PrimitiveAffineDegreeTwoTwelveRow32AugmentationGenerators.ModuleSpace) : v ∈ PrimitiveAffineDegreeTwoTwelveRow32AugmentationGenerators.augmentation ↔
    ∀ i : Fin 3, ∑ j : Fin 4, v (PrimitiveAffineDegreeTwoTwelveRow32AugmentationGenerators.point i j) = 0 := by
  change v ∈ PrimitiveAffineDegreeTwoTwelveRow32AugmentationGenerators.chart.space ↔ _
  rw [PrimitiveAffineDegreeTwoTwelveRow32AugmentationGenerators.chart_mem_iff]
  constructor
  · rintro ⟨h0, h1, h2⟩ i
    fin_cases i
    · simpa [PrimitiveAffineDegreeTwoTwelveRow32AugmentationGenerators.point, Fin.sum_univ_succ, add_assoc] using h0
    · simpa [PrimitiveAffineDegreeTwoTwelveRow32AugmentationGenerators.point, Fin.sum_univ_succ, add_assoc] using h1
    · simpa [PrimitiveAffineDegreeTwoTwelveRow32AugmentationGenerators.point, Fin.sum_univ_succ, add_assoc] using h2
  · intro h
    exact ⟨by simpa [PrimitiveAffineDegreeTwoTwelveRow32AugmentationGenerators.point, Fin.sum_univ_succ, add_assoc] using h 0,
      by simpa [PrimitiveAffineDegreeTwoTwelveRow32AugmentationGenerators.point, Fin.sum_univ_succ, add_assoc] using h 1,
      by simpa [PrimitiveAffineDegreeTwoTwelveRow32AugmentationGenerators.point, Fin.sum_univ_succ, add_assoc] using h 2⟩

/-- An extremal binary head forces equality with the literal augmentation
sum, within the original top module. -/
theorem eq_augmentation_of_binary_head_ge_six
    (B : Subrepresentation PrimitiveAffineDegreeTwoTwelveRow32AugmentationGenerators.representation)
    (hhead : 6 ≤ Module.finrank (ZMod 2)
      ((restricted B).IntertwiningMap (Representation.trivial (ZMod 2) P (ZMod 2)))) :
    B = PrimitiveAffineDegreeTwoTwelveRow32AugmentationGenerators.augmentation := by
  obtain ⟨hrange, _hdim⟩ :=
    PermutationBinaryThreeFourAugmentation.range_eq_augmentation_and_finrank_eq_nine
      Fiber (restricted B) (coordinate B) PrimitiveAffineDegreeTwoTwelveRow32BinaryChart.binaryKernel_isPGroup
      basepoint fiber_card (coordinates_injective B) hhead
  apply le_antisymm
  · intro v hv
    apply (augmentation_mem_iff v).mpr
    intro i
    have hcoord : coordinate B i ⟨v, hv⟩ ∈
        PermutationAugmentation.space (ZMod 2) (Fiber i) := by
      rw [← hrange i]
      exact ⟨⟨v, hv⟩, rfl⟩
    have hsum : (∑ x : Fiber i, coordinate B i ⟨v, hv⟩ x) = 0 := by
      rwa [PermutationAugmentation.space, LinearMap.mem_ker, coordinateSum_eq_sum] at hcoord
    rwa [coordinate_sum] at hsum
  · intro w hw
    let tuple : ∀ i, Fiber i → ZMod 2 := fun _ x ↦ w x.val
    have htuple : ∀ i, tuple i ∈ PermutationAugmentation.space (ZMod 2) (Fiber i) := by
      intro i
      have hsum : (∑ x : Fiber i, w x.val) = 0 := by
        rw [← Equiv.sum_comp (fiberEquiv i) (fun x : Fiber i ↦ w x.val)]
        exact (augmentation_mem_iff w).mp hw i
      rw [PermutationAugmentation.space, LinearMap.mem_ker, coordinateSum_eq_sum]
      exact hsum
    obtain ⟨v, hv⟩ :=
      PermutationBinaryThreeFourAugmentation.extremal_head_original_augmentation_cover
        Fiber (restricted B) (coordinate B) PrimitiveAffineDegreeTwoTwelveRow32BinaryChart.binaryKernel_isPGroup
        basepoint fiber_card (coordinates_injective B) hhead tuple htuple
    have hvw : v.val = w := by
      funext x
      exact congrFun (hv (label x)) ⟨x, rfl⟩
    exact hvw ▸ v.property

end PrimitiveAffineDegreeTwoTwelveRow32BinaryBlocks
end SymmetricSubgroupAsymptotics

end
