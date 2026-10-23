import SymmetricSubgroupAsymptotics.CFSGFFourE6NormDiagonalStepEntries
import SymmetricSubgroupAsymptotics.CFSGFFourE6CharacteristicTwoNormBasis

/-! A diagonal matrix fixing the actual norm26 space and commuting with
the six positive E6 simple units is one. The 52 norm coordinates are seeds;
the checked 26-edge forest supplies all remaining fixed coordinates. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6NormDiagonalResidual
open CFSGFFourSerreMatrices CFSGTwistedE6GeckDiagramCovariance
open CFSGFFourE6CharacteristicTwoNormImage CFSGFFourE6CharacteristicTwoNormBasis
open CFSGFFourE6NormPairRepresentatives CFSGFFourE6FixedIndexRepresentatives
open CFSGFFourE6NormQuotientRootMatching CFSGFFourE6NormQuotientStepEntries
open CFSGFFourE6NormQuotientCoefficientPilot CFSGFFourE6NormDiagonalPropagationPilot
open CFSGFFourE6NormDiagonalStepEntries CFSGSerreQuadraticMatrix
variable (K:Type) [Field K] [CharP K 2]

private theorem normBasis_rep (k:PairIndex) :
    (normBasis K k).val (selectedRepresentative k)=1 := by
  change normCoordinateEquiv K (normBasis K k) k=1
  simp only [normBasis,Module.Basis.map_apply,Pi.basisFun_apply,
    LinearEquiv.apply_symm_apply,Pi.single_eq_same]

private theorem normBasis_partner (k:PairIndex) :
    (normBasis K k).val (diagramIndex (selectedRepresentative k))=1 := by
  have h:=congrFun (normImage_fixed K (normBasis K k)) (diagramIndex (selectedRepresentative k))
  change (normBasis K k).val (diagramIndex.symm (diagramIndex (selectedRepresentative k)))=
    (normBasis K k).val (diagramIndex (selectedRepresentative k)) at h
  rw [Equiv.symm_apply_apply] at h
  exact h.symm.trans (normBasis_rep K k)

private theorem diagonal_value_of_fixed_vector (M:Matrix Index Index K) (hdiag:M.IsDiag)
    (v:Index→K) (hv:M*ᵥv=v) (r:Index) (hr:v r=1) : M r r=1 := by
  have h:=congrFun hv r
  rw [←hdiag.diagonal_diag,Matrix.mulVec_diagonal] at h
  change M r r*v r=v r at h
  simpa only [hr,mul_one] using h

theorem norm_seed_values (M:Matrix Index Index K) (hdiag:M.IsDiag)
    (hnorm:∀k:PairIndex,M*ᵥ(normBasis K k).val=(normBasis K k).val) :
    ∀k:PairIndex,rawDiag K M (normIndex k)=1 ∧ rawDiag K M (partnerIndex (normIndex k))=1 := by
  intro k
  constructor
  · rw [←eraseGeck_selectedRepresentative k,rawDiag_erase]
    exact diagonal_value_of_fixed_vector K M hdiag _ (hnorm k) _ (normBasis_rep K k)
  · rw [←eraseGeck_partnerRepresentative k,rawDiag_erase]
    exact diagonal_value_of_fixed_vector K M hdiag _ (hnorm k) _ (normBasis_partner K k)

theorem diagonal_eq_one (M:Matrix Index Index K) (hdiag:M.IsDiag)
    (hnorm:∀k:PairIndex,M*ᵥ(normBasis K k).val=(normBasis K k).val)
    (hcomm:∀i:Fin 6,M*(canonicalRoot rawData K false i 1:Matrix Index Index K)=
      (canonicalRoot rawData K false i 1:Matrix Index Index K)*M) : M=1 := by
  have hseeds:=norm_seed_values K M hdiag hnorm
  have hfixed:∀j:PairIndex,rawDiag K M (fixedIndex j)=1 :=
    fixed_values_of_steps (rawDiag K M) hseeds (rawDiag_step_eq K M hdiag hcomm)
  have hall (i:Index) : M i i=1 := by
    have hraw:rawDiag K M (eraseGeck i)=1 := by
      rcases selectedRepresentative_cover i with hfix|⟨k,hrep|hrep⟩
      · obtain ⟨j,hj⟩:=fixedIndexMap_bijective.2 ⟨i,hfix⟩
        have hrep0:=congrArg (fun z:{x:GeckIndex // diagramIndex x=x}=>z.val) hj
        change fixedRepresentative j=i at hrep0
        obtain ⟨k,hk⟩:=basisIndexDual.surjective j
        have hrep:fixedRepresentative (basisIndexDual k)=i := by
          rw [hk]
          exact hrep0
        have h:=hfixed k
        rw [←eraseGeck_fixedRepresentative k] at h
        simpa only [hrep] using h
      · rw [hrep,eraseGeck_selectedRepresentative]
        exact (hseeds k).1
      · rw [hrep,eraseGeck_partnerRepresentative]
        exact (hseeds k).2
    simpa only [rawDiag_erase] using hraw
  ext i j
  by_cases hij:i=j
  · subst j
    simpa only [Matrix.one_apply_eq] using hall i
  · rw [hdiag hij,Matrix.one_apply,if_neg hij]

end SymmetricSubgroupAsymptotics.CFSGFFourE6NormDiagonalResidual
