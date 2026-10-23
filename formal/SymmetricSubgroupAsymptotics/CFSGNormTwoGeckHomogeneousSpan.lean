import SymmetricSubgroupAsymptotics.CFSGGradedMatrixHomogeneousLieSpan
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckNegativeLatticeDegree
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckRationalAdjointStrings
import Mathlib.LinearAlgebra.Matrix.IsDiag

/-! The original rational Geck Lie algebra is linearly spanned by its
own homogeneous matrices for the literal integer root-lattice grading.
All three original generator families discharge the grading premise.
There is no additional root-space, faithfulness, or finite-type input. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckHomogeneousSpan
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckLatticeDegree CFSGNormTwoGeckNegativeLatticeDegree
open CFSGNormTwoGeckRationalAdjointStrings CFSGGradedMatrixSupport
open CFSGGradedMatrixHomogeneousLieSpan
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base)

theorem rational_H_homogeneous (i : b.support) :
    Supported (latticeWeight A hs hp b) (fun v=>v+0)
      (RootPairing.GeckConstruction.h i) := by
  have hdiag : (RootPairing.GeckConstruction.h i).IsDiag := by
    rw [RootPairing.GeckConstruction.h_eq_diagonal]
    exact Matrix.isDiag_diagonal _
  intro x y hxy
  apply hdiag
  intro he
  subst y
  exact hxy (by simp)

theorem rational_E_homogeneous (i : b.support) :
    Supported (latticeWeight A hs hp b) (fun v=>v+(i:Roots A).val)
      (RootPairing.GeckConstruction.e i) := by
  let s : Fin (Fintype.card b.support)≃b.support := (Fintype.equivFin b.support).symm
  have hh := field_E_lattice_support A hs hp b s ℚ (s.symm i)
  rw [rational_E_eq] at hh
  simpa only [CFSGGeckSerreRepresentation.E,Equiv.apply_symm_apply] using hh

theorem rational_F_homogeneous (i : b.support) :
    Supported (latticeWeight A hs hp b) (fun v=>v+ -(i:Roots A).val)
      (RootPairing.GeckConstruction.f i) := by
  simpa only [sub_eq_add_neg] using rational_F_lattice_support A hs hp b i

theorem lieAlgebra_eq_homogeneousHull :
    (RootPairing.GeckConstruction.lieAlgebra b).toSubmodule=
      homogeneousHull (latticeWeight A hs hp b)
        (RootPairing.GeckConstruction.lieAlgebra b) := by
  unfold RootPairing.GeckConstruction.lieAlgebra
  apply lieSpan_eq_homogeneousHull
  intro M hM
  rcases hM with (hM|hM)|hM
  · obtain ⟨i,rfl⟩ := hM
    exact ⟨0,rational_H_homogeneous A hs hp b i⟩
  · obtain ⟨i,rfl⟩ := hM
    exact ⟨(i:Roots A).val,rational_E_homogeneous A hs hp b i⟩
  · obtain ⟨i,rfl⟩ := hM
    exact ⟨-(i:Roots A).val,rational_F_homogeneous A hs hp b i⟩

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckHomogeneousSpan
