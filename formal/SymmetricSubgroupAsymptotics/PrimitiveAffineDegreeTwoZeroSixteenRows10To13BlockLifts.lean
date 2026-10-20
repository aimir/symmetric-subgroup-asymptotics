import SymmetricSubgroupAsymptotics.BinaryFourNonsplitBlockModels
import SymmetricSubgroupAsymptotics.BinaryFourFullBlockPermutation

/-! The exact retained generator lifts for zero16 rows10,12,13.
Each identity is on the original sixteen points. The nonsplit lifts
remain elements of their actual constrained subgroups. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoZeroSixteenRows10To13BlockLifts

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open BinaryFourBlockAugmentation BinaryFourFullBlockCoordinates SemidirectProduct

def blockOffset (b : Fin 4) (mask : ℕ) : FullCoordinates :=
  fullEncode (Pi.single b (localOfMask mask))

def commonC : BinaryFourFullBlockCoordinates.Ambient :=
  ⟨Multiplicative.ofAdd (includeAugmentation correction), cElement⟩

def row10U : BinaryFourFullBlockCoordinates.Ambient := ⟨Multiplicative.ofAdd (blockOffset 3 1), uElement⟩
def row10V : BinaryFourFullBlockCoordinates.Ambient := ⟨Multiplicative.ofAdd (blockOffset 3 2), vElement⟩
def row12U : BinaryFourFullBlockCoordinates.Ambient := ⟨Multiplicative.ofAdd (blockOffset 3 3), uElement⟩
def row12V : BinaryFourFullBlockCoordinates.Ambient := ⟨Multiplicative.ofAdd (blockOffset 3 1), vElement⟩

theorem commonC_row10 : row10Condition commonC := by
  unfold row10Condition
  decide +kernel
theorem row10U_condition : row10Condition row10U := by
  unfold row10Condition
  decide +kernel
theorem row10V_condition : row10Condition row10V := by
  unfold row10Condition
  decide +kernel
theorem commonC_row12 : row12Condition commonC := by
  unfold row12Condition
  decide +kernel
theorem row12U_condition : row12Condition row12U := by
  unfold row12Condition
  decide +kernel
theorem row12V_condition : row12Condition row12V := by
  unfold row12Condition
  decide +kernel

def row10Lifts : Fin 3 → Row10Model :=
  ![⟨commonC, commonC_row10⟩, ⟨row10U, row10U_condition⟩, ⟨row10V, row10V_condition⟩]

def row12Lifts : Fin 3 → Row12Model :=
  ![⟨commonC, commonC_row12⟩, ⟨row12U, row12U_condition⟩, ⟨row12V, row12V_condition⟩]

def row13Lifts : Fin 4 → BinaryFourFullBlockCoordinates.Ambient :=
  ![⟨Multiplicative.ofAdd (blockOffset 2 1 + includeAugmentation correction), cElement⟩,
    inr uElement, inr vElement, inl (Multiplicative.ofAdd (blockOffset 0 1))]

def row10OriginalMap : Row10Model →* Equiv.Perm (Fin 16) :=
  fullPermutation.comp row10Subgroup.subtype

def row12OriginalMap : Row12Model →* Equiv.Perm (Fin 16) :=
  fullPermutation.comp row12Subgroup.subtype

theorem row10_lifts_original (i : Fin 3) :
    row10OriginalMap (row10Lifts i) = DegreeTwoZeroSixteenInterfaces.row10Generators i := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

theorem row12_lifts_original (i : Fin 3) :
    row12OriginalMap (row12Lifts i) = DegreeTwoZeroSixteenInterfaces.row12Generators i := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

theorem row13_lifts_original (i : Fin 4) :
    fullPermutation (row13Lifts i) = DegreeTwoZeroSixteenInterfaces.row13Generators i := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

theorem row10_top_le_range : DegreeTwoZeroSixteenInterfaces.row10.top ≤
    row10OriginalMap.range := by
  apply (Subgroup.closure_le _).2
  rintro _ ⟨i, rfl⟩
  exact ⟨row10Lifts i, row10_lifts_original i⟩

theorem row12_top_le_range : DegreeTwoZeroSixteenInterfaces.row12.top ≤
    row12OriginalMap.range := by
  apply (Subgroup.closure_le _).2
  rintro _ ⟨i, rfl⟩
  exact ⟨row12Lifts i, row12_lifts_original i⟩

theorem row13_top_le_range : DegreeTwoZeroSixteenInterfaces.row13.top ≤
    fullPermutation.range := by
  apply (Subgroup.closure_le _).2
  rintro _ ⟨i, rfl⟩
  exact ⟨row13Lifts i, row13_lifts_original i⟩

theorem row10_projection_lifts (i : Fin 3) :
    row10Projection (row10Lifts i) = ![cElement, uElement, vElement] i := by
  fin_cases i <;> rfl

theorem row12_projection_lifts (i : Fin 3) :
    row12Projection (row12Lifts i) = ![cElement, uElement, vElement] i := by
  fin_cases i <;> rfl

theorem complement_word (r : Complement) :
    uElement ^ (r.left.toAdd 0).val * vElement ^ (r.left.toAdd 1).val *
      cElement ^ r.right.toAdd.val = r := by
  obtain ⟨p, z⟩ := r
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    ext i
    revert p z i
    decide +kernel
  · apply Multiplicative.toAdd.injective
    revert p z
    decide +kernel

/-- A range calculation using only the actual kernel and three actual
lifts. Surjectivity of the block projection is not an extra input. -/
theorem range_le_of_kernel_lifts {G : Type} [Group G]
    (pi : G →* Complement) (f : G →* Equiv.Perm (Fin 16))
    (H : Subgroup (Equiv.Perm (Fin 16)))
    (cLift uLift vLift : G)
    (hc : pi cLift = cElement) (hu : pi uLift = uElement) (hv : pi vLift = vElement)
    (hcmem : f cLift ∈ H) (humem : f uLift ∈ H) (hvmem : f vLift ∈ H)
    (hker : ∀ g : G, g ∈ pi.ker → f g ∈ H) : f.range ≤ H := by
  rintro _ ⟨g, rfl⟩
  let w := uLift ^ ((pi g).left.toAdd 0).val *
    vLift ^ ((pi g).left.toAdd 1).val * cLift ^ (pi g).right.toAdd.val
  have hw : pi w = pi g := by
    dsimp [w]
    rw [map_mul, map_mul, map_pow, map_pow, map_pow, hu, hv, hc]
    exact complement_word (pi g)
  have hdiff : g * w⁻¹ ∈ pi.ker := by
    apply MonoidHom.mem_ker.mpr
    rw [map_mul, map_inv, hw, mul_inv_cancel]
  have hwm : f w ∈ H := by
    dsimp [w]
    rw [map_mul, map_mul, map_pow, map_pow, map_pow]
    exact H.mul_mem (H.mul_mem (H.pow_mem humem _) (H.pow_mem hvmem _))
      (H.pow_mem hcmem _)
  have hm := H.mul_mem (hker (g * w⁻¹) hdiff) hwm
  simpa only [← map_mul, inv_mul_cancel_right] using hm

theorem augmentation_zero_include (x : FullCoordinates) (hx : augmentation x = 0) :
    includeAugmentation (head x) = x := by
  have h6 := congrFun hx 0
  have h7 := congrFun hx 1
  change x 6 = 0 at h6
  change x 7 = 0 at h7
  ext i
  fin_cases i <;> simp [includeAugmentation, head, h6, h7]

theorem row10_kernel_original (g : Row10Model) (hg : g ∈ row10Projection.ker) :
    ∃ x : Coordinates, x 5 = 0 ∧
      row10OriginalMap g = translations (Multiplicative.ofAdd x) := by
  have hr : g.val.right = 1 := hg
  have haug : augmentation g.val.left.toAdd = 0 := by
    simpa only [hr] using g.property.1
  have hf : g.val.left.toAdd 5 = 0 := by
    simpa [hr, quadratic] using g.property.2
  refine ⟨head g.val.left.toAdd, hf, ?_⟩
  have hgval : g.val = inl (Multiplicative.ofAdd g.val.left.toAdd) :=
    SemidirectProduct.ext rfl hr
  change fullPermutation g.val = _
  calc
    fullPermutation g.val = fullPermutation
        (inl (Multiplicative.ofAdd g.val.left.toAdd)) := congrArg fullPermutation hgval
    _ = fullTranslations (Multiplicative.ofAdd g.val.left.toAdd) := fullPermutation_inl _
    _ = fullTranslations (Multiplicative.ofAdd
        (includeAugmentation (head g.val.left.toAdd))) :=
      congrArg (fun x => fullTranslations (Multiplicative.ofAdd x))
        (augmentation_zero_include _ haug).symm
    _ = _ := fullTranslations_include _

theorem row12_kernel_original (g : Row12Model) (hg : g ∈ row12Projection.ker) :
    ∃ x : Coordinates,
      row12OriginalMap g = translations (Multiplicative.ofAdd x) := by
  have hr : g.val.right = 1 := hg
  have haug : augmentation g.val.left.toAdd = 0 := by
    have hh : augmentation g.val.left.toAdd = localCycle g.val.right.left.toAdd := g.property
    rw [hr] at hh
    change augmentation g.val.left.toAdd = localCycle (0 : Local) at hh
    simpa only [map_zero] using hh
  refine ⟨head g.val.left.toAdd, ?_⟩
  have hgval : g.val = inl (Multiplicative.ofAdd g.val.left.toAdd) :=
    SemidirectProduct.ext rfl hr
  change fullPermutation g.val = _
  calc
    fullPermutation g.val = fullPermutation
        (inl (Multiplicative.ofAdd g.val.left.toAdd)) := congrArg fullPermutation hgval
    _ = fullTranslations (Multiplicative.ofAdd g.val.left.toAdd) := fullPermutation_inl _
    _ = fullTranslations (Multiplicative.ofAdd
        (includeAugmentation (head g.val.left.toAdd))) :=
      congrArg (fun x => fullTranslations (Multiplicative.ofAdd x))
        (augmentation_zero_include _ haug).symm
    _ = _ := fullTranslations_include _

end PrimitiveAffineDegreeTwoZeroSixteenRows10To13BlockLifts
end SymmetricSubgroupAsymptotics

end
