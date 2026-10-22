import SymmetricSubgroupAsymptotics.CFSGSignedCartanReflections
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylLatticeLinear
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateCartan

/-! The literal lattice reflection matrices compute exactly the already
constructed integral linear action of the original coordinate Weyl words. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateLatticeWord
open CFSGSignedCartanReflections CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckLatticeDegree CFSGNormTwoGeckWeylLatticeLinear
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀j,A j j=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]

local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

theorem latticeStep_linear (i : Fin r) :
    (latticeStep A i).mulVecLin=
      (reflectionEquiv A (coordinateRoot A hd i)).toIntLinearEquiv.toLinearMap := by
  apply (Pi.basisFun ℤ (Fin r)).ext
  intro j
  simp only [Pi.basisFun_apply,Matrix.mulVecLin_apply]
  change latticeStep A i*ᵥ(Pi.single j 1 : Fin r→ℤ)=
    Pi.single j 1-integerPairing A (Pi.single j 1) (Pi.single i 1) • Pi.single i 1
  rw [show integerPairing A (Pi.single j 1) (Pi.single i 1)=A j i from
    Matrix.toBilin'_single A j i]
  funext k
  simp only [Matrix.mulVec_single_one,Matrix.col_apply,latticeStep,Matrix.sub_apply,
    Matrix.of_apply,Matrix.one_apply,Pi.sub_apply,Pi.smul_apply,zsmul_eq_mul]
  by_cases hkj : k=j <;> by_cases hki : k=i <;>
    simp [Pi.single_apply,hkj,hki]

theorem latticeWord_linear (w : List (Fin r)) :
    (latticeWord A w).mulVecLin=(wordLinear A hs hp b₀ s₀ w).toLinearMap := by
  induction w with
  | nil=>simp only [latticeWord,wordLinear,Matrix.mulVecLin_one];rfl
  | cons i w ih=>
    rw [latticeWord,Matrix.mulVecLin_mul,latticeStep_linear A hd i,ih]
    rfl

theorem latticeWord_eq_one_of_wordLinear_eq_one (w : List (Fin r))
    (hw : wordLinear A hs hp b₀ s₀ w=1) : latticeWord A w=1 := by
  apply Matrix.ext_of_mulVec_single
  intro j
  have hh := LinearMap.congr_fun (latticeWord_linear A hd hs hp ho w)
    (Pi.single j (1:ℤ))
  rw [hw] at hh
  change latticeWord A w*ᵥ(Pi.single j (1:ℤ))=Pi.single j (1:ℤ) at hh
  simpa only [Matrix.one_mulVec] using hh

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateLatticeWord
