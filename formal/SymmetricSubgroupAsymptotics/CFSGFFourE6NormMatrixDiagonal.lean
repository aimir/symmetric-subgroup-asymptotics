import SymmetricSubgroupAsymptotics.CFSGFFourE6NormMatrixAction

/-! A genuine diagonal ambient matrix is diagonal on the proved
orbit-sum basis. This only compares literal matrix entries; it does not
identify any normalizer or diagonal subgroup with a torus. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6NormMatrixDiagonal
open CFSGFFourSerreMatrices CFSGSerreQuadraticMatrix
open CFSGFFourE6CharacteristicTwoNormImage CFSGFFourE6CharacteristicTwoNormBasis
open CFSGFFourE6NormMatrixAction CFSGFFourE6NormPairRepresentatives
open CFSGTwistedE6GeckDiagramCovariance
variable (K : Type) [Field K] [CharP K 2]

private theorem diagramVector_single (i : Index) :
    diagramVector K (Pi.single i (1:K))=(Pi.single (diagramIndex i) (1:K) : Index→K) := by
  funext j
  change (Pi.single i (1:K) : Index→K) (diagramIndex.symm j)=
    (Pi.single (diagramIndex i) (1:K) : Index→K) j
  simp only [Pi.single_apply,Equiv.symm_apply_eq] <;> split_ifs <;> rfl

theorem normMatrixAction_raw_entry (g : canonicalElementaryGroup realizationData K)
    (j k : PairIndex) :
    normMatrixAction K g j k=
      (g.val : Matrix Index Index K) (selectedRepresentative j) (selectedRepresentative k)+
        (g.val : Matrix Index Index K) (selectedRepresentative j) (diagramIndex (selectedRepresentative k)) := by
  rw [normMatrixAction_entry,normCoordinateEquiv_apply,normAction_val,normBasis_val,
    diagramVector_single,Matrix.mulVec_add,Matrix.mulVec_single_one,Matrix.mulVec_single_one]
  rfl

theorem normMatrixAction_off_diagonal_eq_zero (g : canonicalElementaryGroup realizationData K)
    (hdiag : ∀i j : Index,i≠j→(g.val : Matrix Index Index K) i j=0)
    (j k : PairIndex) (hjk : j≠k) : normMatrixAction K g j k=0 := by
  rw [normMatrixAction_raw_entry,
    hdiag _ _ (fun he=>hjk (selectedRepresentative_injective he)),
    hdiag _ _ (selectedRepresentative_disjoint j k),add_zero]

end SymmetricSubgroupAsymptotics.CFSGFFourE6NormMatrixDiagonal
