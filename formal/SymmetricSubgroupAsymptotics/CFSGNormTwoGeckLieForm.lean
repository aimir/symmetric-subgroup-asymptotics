import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckCoordinateForm

/-! The full actual coordinate-base Geck Lie algebra preserves the height
form. This follows from its literal H/E/F Lie-span, not from a recognition
of a named orthogonal algebra. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckLieForm
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoGeckGram
open CFSGNormTwoGeckCoordinateForm
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    (hd : ∀ i,A i i=2) (ho : ∀ i j,i≠j→A i j≤0)
local notation "b" => coordinateBase A hd hs hp ho

theorem lieAlgebra_le_form : RootPairing.GeckConstruction.lieAlgebra b≤
    skewAdjointMatricesLieSubalgebra (gram A hs hp b) := by
  unfold RootPairing.GeckConstruction.lieAlgebra
  apply LieSubalgebra.lieSpan_le.mpr
  intro X hX
  rcases hX with (hX|hX)|hX
  · obtain ⟨i,rfl⟩ := hX
    exact H_mem_form A hs hp hd ho i
  · obtain ⟨i,rfl⟩ := hX
    exact E_mem_form A hs hp hd ho i
  · obtain ⟨i,rfl⟩ := hX
    exact F_mem_form A hs hp hd ho i

theorem mem_form {X : Matrix ((b).support⊕Roots A) ((b).support⊕Roots A) ℚ}
    (hX : X∈RootPairing.GeckConstruction.lieAlgebra b) :
    X∈skewAdjointMatricesLieSubalgebra (gram A hs hp b) :=
  lieAlgebra_le_form A hs hp hd ho hX

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckLieForm
