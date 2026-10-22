import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateBase
import Mathlib.LinearAlgebra.RootSystem.CartanMatrix

/-! Exact original Cartan entries for the actual coordinate base. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoRootPairing
open CFSGIntegerMatrixPairing
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hd : ∀ i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀ i j,i≠j→A i j≤0)

def coordinateIndexEquiv : n≃(coordinateBase A hd hs hp ho).support := by
  classical
  refine Equiv.ofBijective (fun i=>⟨coordinateRoot A hd i,by
    simp [coordinateBase,coordinateSupport]⟩) ?_
  constructor
  · intro i j h
    exact coordinateRoot_injective A hd (congrArg Subtype.val h)
  · intro x
    have hx : x.val∈coordinateSupport A hd := x.property
    change x.val∈Finset.univ.image (coordinateRoot A hd) at hx
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hx
    exact ⟨i,Subtype.ext hi⟩

theorem coordinate_cartan (i j : n) :
    (coordinateBase A hd hs hp ho).cartanMatrix
      (coordinateIndexEquiv A hd hs hp ho i) (coordinateIndexEquiv A hd hs hp ho j)=A i j := by
  apply (Int.cast_injective (α:=ℚ))
  change algebraMap ℤ ℚ ((coordinateBase A hd hs hp ho).cartanMatrixIn ℤ _ _)=(A i j:ℚ)
  rw [RootPairing.Base.algebraMap_cartanMatrixIn_apply]
  change (rootPairing A hs hp).pairing (coordinateRoot A hd i) (coordinateRoot A hd j)=(A i j:ℚ)
  rw [pairing_cast]
  simp only [coordinateRoot,integerPairing,Matrix.toBilin'_single]

theorem coordinate_cartan_transpose (i j : n) :
    (coordinateBase A hd hs hp ho).cartanMatrix
      (coordinateIndexEquiv A hd hs hp ho j) (coordinateIndexEquiv A hd hs hp ho i)=A i j := by
  rw [coordinate_cartan]
  exact congrFun (congrFun hs i) j

end SymmetricSubgroupAsymptotics.CFSGNormTwoRootPairing
