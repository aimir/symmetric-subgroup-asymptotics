import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedRootLineCell
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckLongRootOrbitCardinality
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateBorelRootNormalization

/-! Every fixed-matrix conjugate of the highest ambient long root line
lies in one of six orbits of the literal fixed positive matrix group. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckLongRootFamilyCover
open CFSGNormTwoRootPairing CFSGIntegerMatrixPairing
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityD4PositiveRootOrbits CFSGTrialityD4InvariantRoots
open CFSGTrialityRelativeWordLanguage CFSGTrialityD4WordDiscriminant
open CFSGTrialityGeckSectionHeightMembership CFSGTrialityGeckRootLineDiagonal
open CFSGTrialityGeckFixedRootLineCell CFSGTrialityGeckBruhatCellFactors
open CFSGTrialityGeckShortCentralizerCardinality CFSGTrialityGeckFixedPositiveGeneration
open CFSGTrialityGeckPositiveTwist CFSGTrialityGeckMatrixTwist
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckIntegralWord
open CFSGNormTwoCoordinateRootWeylAction CFSGNormTwoCoordinateBorelRootNormalization
open CFSGSubgroupConjugateOrbitCardinality CFSGSerreOrdinaryTwists
local notation "A" => CartanMatrix.D 4
local notation "hd" => CartanMatrix.D_diag 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite
local notation "ho" => CartanMatrix.D_off_diag_nonpos 4

local instance : DecidableEq (Roots A) := Classical.decEq _

theorem highest_long_dominant (i : Fin 4) :
    0 ≤ integerPairing A (longRoot 2).val (Pi.single i (1 : ℤ) : Fin 4 → ℤ) := by
  fin_cases i <;>
    norm_num [longRoot,longCoordinates,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,
      integerPairing,Matrix.toBilin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,
      CFSGTrialityD4PositiveRootOrbits.cartan_eq,Pi.single_apply]

theorem conjugate_eq_fixed_positive_conjugate (q : CFSG.PrimePower)
    (g : (Matrix GeckIndex GeckIndex (q.Extension 3))ˣ)
    (hg : g ∈ CFSGTrialityGeckSourceWordAction.MatrixGroup (q.Extension 3))
    (hfixed : unitTwist (q.Extension 3) (definingFieldAutomorphism q 3) g = g) :
    ∃ (neg : Bool) (s : Fin 3)
      (u : fixedPositive (q.Extension 3) (definingFieldAutomorphism q 3)),
      (RootLine (q.Extension 3) (longRoot 2)).map (MulAut.conj g).toMonoidHom =
        (RootLine (q.Extension 3) (signedLongRoot neg s)).map
          (MulAut.conj (fixedPositiveInclusion (q.Extension 3)
            (definingFieldAutomorphism q 3) u)).toMonoidHom := by
  let K := q.Extension 3
  let sigma := definingFieldAutomorphism q 3
  obtain ⟨r,u,d,hu,huf,hdiag,hdf,v,hvf,he⟩ :=
    exists_fixed_rootLine_cell K sigma g hg hfixed
  let k := rootAction (expandRelative r) (longRoot 2)
  have hk : diagramRoot k = k := by
    change diagramRoot (rootAction (expandRelative r) (longRoot 2)) =
      rootAction (expandRelative r) (longRoot 2)
    rw [relative_root_action_commutes]
    exact congrArg (rootAction (expandRelative r)) (signed_long_fixed false 2)
  obtain ⟨neg,s,hks⟩ := fixed_root_signed_long k hk
  have hw : (RootLine K (longRoot 2)).map
      (MulAut.conj (wordUnit A hs hp Base Index K (expandRelative r))).toMonoidHom =
        RootLine K k := by
    rw [word_eq_canonicalWord]
    exact rootSubgroup_map_word A hd hs hp ho K (expandRelative r) (longRoot 2)
  have hvU : inversionEmbedding K (expandRelative r) v ∈ Positive K := v.val.property
  have hv := conjugate_eq_of_mem_normalizer (RootLine K (longRoot 2)) _
    (Subgroup.centralizer_le_normalizer _
      (positive_le_centralizer_root A hd hs hp ho K (longRoot 2)
        (long_positive 2) highest_long_dominant hvU))
  have hd' := conjugate_eq_of_mem_normalizer (RootLine K k) d
    (rootLineDiagonal_le_root_normalizer K k hdiag)
  have huf' : (⟨u,hu⟩ : Positive K) ∈ fixedPositive K sigma := by
    apply Subtype.ext
    change (positiveTwist K sigma (⟨u,hu⟩ : Positive K)).val = u
    exact (positiveTwist_val K sigma (⟨u,hu⟩ : Positive K)).trans huf
  refine ⟨neg,s,⟨⟨u,hu⟩,huf'⟩,?_⟩
  change (RootLine K (longRoot 2)).map (MulAut.conj g).toMonoidHom =
    (RootLine K (signedLongRoot neg s)).map (MulAut.conj u).toMonoidHom
  rw [he]
  calc
    _ = ((RootLine K (longRoot 2)).map
        (MulAut.conj (inversionEmbedding K (expandRelative r) v)).toMonoidHom).map
          (MulAut.conj (u*d*wordUnit A hs hp Base Index K (expandRelative r))).toMonoidHom :=
      conjugate_mul _ _ _
    _ = (RootLine K (longRoot 2)).map
        (MulAut.conj (u*d*wordUnit A hs hp Base Index K (expandRelative r))).toMonoidHom :=
      congrArg (fun S : Subgroup ((Matrix GeckIndex GeckIndex K)ˣ) =>
        S.map (MulAut.conj (u*d*wordUnit A hs hp Base Index K (expandRelative r))).toMonoidHom) hv
    _ = ((RootLine K (longRoot 2)).map
        (MulAut.conj (wordUnit A hs hp Base Index K (expandRelative r))).toMonoidHom).map
          (MulAut.conj (u*d)).toMonoidHom := conjugate_mul _ _ _
    _ = (RootLine K k).map (MulAut.conj (u*d)).toMonoidHom :=
      congrArg (fun S : Subgroup ((Matrix GeckIndex GeckIndex K)ˣ) =>
        S.map (MulAut.conj (u*d)).toMonoidHom) hw
    _ = ((RootLine K k).map (MulAut.conj d).toMonoidHom).map
        (MulAut.conj u).toMonoidHom := conjugate_mul _ _ _
    _ = (RootLine K k).map (MulAut.conj u).toMonoidHom :=
      congrArg (fun S : Subgroup ((Matrix GeckIndex GeckIndex K)ˣ) =>
        S.map (MulAut.conj u).toMonoidHom) hd'
    _ = _ := congrArg (fun j : Roots A =>
      (RootLine K j).map (MulAut.conj u).toMonoidHom) hks

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckLongRootFamilyCover
