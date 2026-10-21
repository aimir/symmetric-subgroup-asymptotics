import SymmetricSubgroupAsymptotics.BinaryRegularFullConstantPlaneOne
import SymmetricSubgroupAsymptotics.BinaryCoordinateDisplacementBasis

/-! The checked plane-one capacity determines an actual four-dimensional
fixed space. This identifies the same correlated subspace, rather than
substituting its cardinality or independently projecting its layers. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryRegularFullConstantSecondCenterSpace
local instance fullConstantSecondCenterSpacePrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private def inclusion :=
  (binaryRectangularMatrixOfColumnMasks 16 4 (![135,75,45,30] : Fin 4 → ℕ)).mulVecLin
private def coordinates : (Fin 16 → ZMod 2) →ₗ[ZMod 2] (Fin 4 → ZMod 2) where
  toFun v j := v ⟨7-j.val,by omega⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
private theorem chart_basis : ∀ j : Fin 4,
    coordinates (inclusion (Pi.single j 1))=Pi.single j 1 := by decide +kernel
private theorem chart_left (v : Fin 4 → ZMod 2) : coordinates (inclusion v)=v := by
  have he : coordinates.comp inclusion=LinearMap.id := by
    apply LinearMap.pi_ext
    intro i c
    have hs : Pi.single i c=c • Pi.single i (1 : ZMod 2) := by
      ext j
      simp [Pi.single_apply,mul_ite]
    simp only [LinearMap.comp_apply,hs,map_smul,chart_basis,LinearMap.id_apply]
  exact DFunLike.congr_fun he v
/-- The literal original-coordinate four-space containing the second centre. -/
def room : BinaryCoordinateSpace 16 4 := ⟨inclusion,coordinates,chart_left⟩
private theorem room_basis : ∀ j : Fin 4,
    room.inclusion (Pi.single j 1)∈BinaryRegularFullConstantPlaneOne.K.space ∧
      ∀ i : Fin 6,
      BinaryRegularFullConstantPlaneOne.action i (room.inclusion (Pi.single j 1))-
        room.inclusion (Pi.single j 1)∈BinaryRegularFullConstantPlaneOne.plane.space := by
  decide +kernel

theorem room_mem_fixed (v : room.space) :
    v.val∈BinaryRegularFullConstantPlaneOne.K.space ∧
      ∀ i : Fin 6,BinaryRegularFullConstantPlaneOne.action i v.val-v.val∈
        BinaryRegularFullConstantPlaneOne.plane.space := by
  constructor
  · exact room.le_of_basis_mem BinaryRegularFullConstantPlaneOne.K.space
      (fun j => (room_basis j).1) v.property
  · intro i
    exact binaryCoordinate_displacement_mem_of_basis room
      (BinaryRegularFullConstantPlaneOne.action i) BinaryRegularFullConstantPlaneOne.plane.space
      (fun j => (room_basis j).2 i) v.val v.property

/-- No further finite search: sixteen displayed fixed vectors exhaust
an independently checked fixed set of cardinality at most sixteen. -/
theorem fixed_mem_room
    (v : binaryCoordinateFixedDisplacements BinaryRegularFullConstantPlaneOne.K
      BinaryRegularFullConstantPlaneOne.action BinaryRegularFullConstantPlaneOne.plane.space) :
    v.val∈room.space := by
  let f : room.space → binaryCoordinateFixedDisplacements BinaryRegularFullConstantPlaneOne.K
      BinaryRegularFullConstantPlaneOne.action BinaryRegularFullConstantPlaneOne.plane.space :=
    fun x => ⟨x.val,room_mem_fixed x⟩
  have hf : Function.Injective f := by
    intro a b he
    exact Subtype.ext (congrArg
      (fun x : binaryCoordinateFixedDisplacements BinaryRegularFullConstantPlaneOne.K
        BinaryRegularFullConstantPlaneOne.action BinaryRegularFullConstantPlaneOne.plane.space => x.val) he)
  have hcard : Nat.card (binaryCoordinateFixedDisplacements BinaryRegularFullConstantPlaneOne.K
      BinaryRegularFullConstantPlaneOne.action BinaryRegularFullConstantPlaneOne.plane.space)≤Nat.card room.space := by
    simpa only [room.card] using BinaryRegularFullConstantPlaneOne.fixed_card_le
  obtain ⟨x,hx⟩ := (hf.bijective_of_nat_card_le hcard).surjective v
  exact (congrArg (fun x : binaryCoordinateFixedDisplacements BinaryRegularFullConstantPlaneOne.K
    BinaryRegularFullConstantPlaneOne.action BinaryRegularFullConstantPlaneOne.plane.space => x.val) hx) ▸ x.property

end SymmetricSubgroupAsymptotics.BinaryRegularFullConstantSecondCenterSpace
