import SymmetricSubgroupAsymptotics.BinaryRegularFullConstantSecondCenterSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! All two-dimensional subspaces of the same literal four-space which
contain its constant line belong to seven planes. Only the sixteen
coordinate vectors of that four-space are used in the finite cover. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryRegularFullConstantSevenPlanes
local instance fullConstantSevenPlanesPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
abbrev room := BinaryRegularFullConstantSecondCenterSpace.room
private def lineInclusion : (Fin 1 → ZMod 2) →ₗ[ZMod 2] (Fin 16 → ZMod 2) :=
  (binaryRectangularMatrixOfColumnMasks 16 1 (![255] : Fin 1 → ℕ)).mulVecLin
private def lineCoordinates : (Fin 16 → ZMod 2) →ₗ[ZMod 2] (Fin 1 → ZMod 2) where
  toFun v _ := v 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
private theorem lineBasis : ∀ j : Fin 1,
    lineCoordinates (lineInclusion (Pi.single j 1))=Pi.single j 1 := by decide +kernel
private theorem lineLeft (v : Fin 1 → ZMod 2) : lineCoordinates (lineInclusion v)=v := by
  have he : lineCoordinates.comp lineInclusion=LinearMap.id := by
    apply LinearMap.pi_ext
    intro j c
    have hs : Pi.single j c=c • Pi.single j (1 : ZMod 2) := by
      ext k
      simp [Pi.single_apply,mul_ite]
    simp only [LinearMap.comp_apply,hs,map_smul,lineBasis,LinearMap.id_apply]
  exact DFunLike.congr_fun he v
def line : BinaryCoordinateSpace 16 1 := ⟨lineInclusion,lineCoordinates,lineLeft⟩
private def pivot (i : Fin 7) : Fin 3 :=
  ⟨Nat.log2 (i.val+1),by
    have hbound : ∀ j : Fin 7,Nat.log2 (j.val+1)<3 := by decide
    exact hbound i⟩
private def mask (i : Fin 7) : ℕ :=
  (if (i.val+1).testBit 0 then 135 else 0) ^^^
  (if (i.val+1).testBit 1 then 75 else 0) ^^^
  (if (i.val+1).testBit 2 then 45 else 0)
private def planeInclusion (i : Fin 7) :=
  (binaryRectangularMatrixOfColumnMasks 16 2 (![255,mask i] : Fin 2 → ℕ)).mulVecLin
private def planeCoordinates (i : Fin 7) :
    (Fin 16 → ZMod 2) →ₗ[ZMod 2] (Fin 2 → ZMod 2) where
  toFun v := ![room.coordinates v 3,
    room.coordinates v ⟨(pivot i).val,by omega⟩+room.coordinates v 3]
  map_add' a b := by ext j;fin_cases j <;> simp [map_add,add_add_add_comm]
  map_smul' c v := by ext j;fin_cases j <;> simp [map_smul,mul_add]
private theorem planeBasis : ∀ i : Fin 7,∀ j : Fin 2,
    planeCoordinates i (planeInclusion i (Pi.single j 1))=Pi.single j 1 := by decide +kernel
private theorem planeLeft (i : Fin 7) (v : Fin 2 → ZMod 2) :
    planeCoordinates i (planeInclusion i v)=v := by
  have he : (planeCoordinates i).comp (planeInclusion i)=LinearMap.id := by
    apply LinearMap.pi_ext
    intro j c
    have hs : Pi.single j c=c • Pi.single j (1 : ZMod 2) := by
      ext k
      simp [Pi.single_apply,mul_ite]
    simp only [LinearMap.comp_apply,hs,map_smul,planeBasis,LinearMap.id_apply]
  exact DFunLike.congr_fun he v
def plane (i : Fin 7) : BinaryCoordinateSpace 16 2 :=
  ⟨planeInclusion i,planeCoordinates i,planeLeft i⟩
private theorem lineBasisMem : ∀ i : Fin 7,∀ j : Fin 1,
    line.inclusion (Pi.single j 1)∈(plane i).space := by
  simp only [BinaryCoordinateSpace.mem_iff]
  decide +kernel
theorem line_le_plane (i : Fin 7) : line.space≤(plane i).space :=
  line.le_of_basis_mem _ (lineBasisMem i)
private theorem vectorCover : ∀ v : Fin 4 → ZMod 2,
    room.inclusion v∉line.space → ∃ i : Fin 7,room.inclusion v∈(plane i).space := by
  simp only [BinaryCoordinateSpace.mem_iff]
  decide +kernel

theorem cover (A : Submodule (ZMod 2) (Fin 16 → ZMod 2))
    (hA : A≤room.space) (hline : line.space≤A) (hcard : Nat.card A=4) :
    ∃ i : Fin 7,A≤(plane i).space := by
  have hdim : Module.finrank (ZMod 2) A=2 := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := A)
    rw [Nat.card_zmod,hcard] at hc
    have he : 2^Module.finrank (ZMod 2) A=2^2 := hc.symm
    exact Nat.pow_right_injective (by decide : 2≤(2 : ℕ)) he
  have hn : ¬A≤line.space := by
    intro h
    have he := le_antisymm h hline
    have hc := line.card
    rw [←he,hcard] at hc
    norm_num at hc
  obtain ⟨v,hv,hvline⟩ := SetLike.not_le_iff_exists.mp hn
  obtain ⟨c,hc⟩ := hA hv
  obtain ⟨i,hi⟩ := vectorCover c (hc.symm ▸ hvline)
  refine ⟨i,?_⟩
  have hvin : v∈(plane i).space := hc ▸ hi
  have hstrict : line.space<A⊓(plane i).space := by
    refine lt_of_le_of_ne (le_inf hline (line_le_plane i)) ?_
    intro he
    apply hvline
    rw [he]
    exact ⟨hv,hvin⟩
  have hlow := Submodule.finrank_lt_finrank_of_lt hstrict
  rw [line.finrank] at hlow
  have hupper := Submodule.finrank_mono (show A⊓(plane i).space≤A from inf_le_left)
  have he : A⊓(plane i).space=A :=
    Submodule.eq_of_le_of_finrank_eq inf_le_left (by omega)
  rw [←he]
  exact inf_le_right
end SymmetricSubgroupAsymptotics.BinaryRegularFullConstantSevenPlanes
