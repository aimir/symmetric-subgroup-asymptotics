import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateBase
import SymmetricSubgroupAsymptotics.CFSGIntegerHeightSign

/-! The original coordinate base has an actual integral height functional
that is one on every simple root. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateHeight
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGIntegerHeightSign
variable {n : Type*} [Fintype n] [DecidableEq n]

def coordinateHeight : (n→ℤ)→ₗ[ℤ]ℤ where
  toFun := height
  map_add' := height_add
  map_smul' := by
    intro c x
    simp only [height,Pi.smul_apply,smul_eq_mul,Finset.mul_sum,RingHom.id_apply]

variable (A : Matrix n n ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)

theorem simple_height (i : (coordinateBase A hd hs hp ho).support) :
    coordinateHeight (i:Roots A).val=1 := by
  have hi : (i:Roots A)∈(coordinateSupport A hd : Set (Roots A)) := i.property
  rw [coordinateSupport_coe] at hi
  obtain ⟨j,hj⟩ := hi
  rw [←hj]
  change height (Pi.single j (1:ℤ))=1
  simp only [height,Pi.single_apply,
    Finset.sum_ite_eq',Finset.sum_ite_eq,Finset.mem_univ,if_true]

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateHeight
