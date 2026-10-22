import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateBase
import Mathlib.LinearAlgebra.RootSystem.GeckConstruction.Basis

/-! A genuine LieAlgebra.Basis for the SAME generated rational Geck
matrix Lie algebra. Coordinate norm-two roots span both original spaces;
no Lie representation injectivity or named-model recognition is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckGeneratedBasis
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)

include hd in
theorem coordinate_isRootSystem : (rootPairing A hs hp).IsRootSystem := by
  have hspan : Submodule.span ℚ (Set.range (rootPairing A hs hp).root)=⊤ := by
    apply top_unique
    rw [←(Pi.basisFun ℚ n).span_eq]
    apply Submodule.span_mono
    rintro x ⟨i,rfl⟩
    exact ⟨coordinateRoot A hd i,by
      simpa only [Pi.basisFun_apply] using coordinateRoot_root A hd hs hp i⟩
  exact ⟨hspan,hspan⟩

variable [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base)

def generatedLieBasis : LieAlgebra.Basis b.support ℚ
    (RootPairing.GeckConstruction.lieAlgebra b) := by
  letI : (rootPairing A hs hp).IsRootSystem := coordinate_isRootSystem A hd hs hp
  exact RootPairing.GeckConstruction.basis b

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckGeneratedBasis
