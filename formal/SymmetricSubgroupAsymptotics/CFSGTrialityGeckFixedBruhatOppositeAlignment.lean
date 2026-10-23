import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedWordOpposition
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedRootLineCell
import SymmetricSubgroupAsymptotics.CFSGFixedSubgroupConjugation
import SymmetricSubgroupAsymptotics.CFSGSubgroupConjugateDisjoint

/-! The genuine fixed positive group acts transitively on its disjoint
conjugates inside the fixed matrix group. Actual fixed Bruhat factors
and the two fixed root tests prove this without an assumed BN-pair. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedBruhatOppositeAlignment
open CFSGTrialityGeckFixedWordOpposition CFSGTrialityGeckFixedPositiveRaw
open CFSGTrialityGeckFixedRootLineCell CFSGTrialityGeckBruhatCellFactors
open CFSGTrialityGeckRootLineDiagonal CFSGTrialityGeckNormalizerEnvelope
open CFSGTrialityGeckRelativeRootGenerated CFSGTrialityGeckPositiveTwist
open CFSGTrialityGeckDiagramCovariance CFSGTrialityD4NormTwo CFSGTrialityRelativeWordLanguage
open CFSGTrialityGeckMatrixTwist CFSGTrialityGeckSourceWordAction
open CFSGNormTwoGeckWeylWordDegree CFSGSubgroupConjugateOrbitCardinality
open CFSGFixedSubgroupConjugation CFSGSubgroupConjugateDisjoint
open CFSGCentralTwistedCommutatorLift CFSGSerreOrdinaryTwists
local notation "A" => CartanMatrix.D 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots A) := Classical.decEq _

private theorem conjugate_cell {G : Type*} [Group G] (R : Subgroup G)
    (g u d W v : G) (he : g=(u*d)*W*v)
    (hv : v∈Subgroup.normalizer (R : Set G)) :
    R.map (MulAut.conj g).toMonoidHom=
      ((R.map (MulAut.conj W).toMonoidHom).map (MulAut.conj d).toMonoidHom).map
        (MulAut.conj u).toMonoidHom := by
  rw [he,conjugate_mul,conjugate_eq_of_mem_normalizer R v hv,conjugate_mul,conjugate_mul]

theorem fixed_opposite_conjugate_by_positive (q : CFSG.PrimePower)
    (g : (Matrix GeckIndex GeckIndex (q.Extension 3))ˣ)
    (hg : g∈MatrixGroup (q.Extension 3))
    (hfixed : unitTwist (q.Extension 3) (definingFieldAutomorphism q 3) g=g)
    (hdisj : fixedPositiveRaw q⊓(fixedPositiveRaw q).map (MulAut.conj g).toMonoidHom=⊥) :
    ∃u∈fixedPositiveRaw q,(fixedPositiveRaw q).map (MulAut.conj g).toMonoidHom=
      (signedFixed (q.Extension 3) (definingFieldAutomorphism q 3) true).map
        (MulAut.conj u).toMonoidHom := by
  let R := fixedPositiveRaw q
  let N := signedFixed (q.Extension 3) (definingFieldAutomorphism q 3) true
  let tau := unitTwist (q.Extension 3) (definingFieldAutomorphism q 3)
  obtain ⟨r,u,d,hu,huf,hdiag,hdf,v,hvf,he⟩ :=
    exists_fixed_rootLine_cell (q.Extension 3) (definingFieldAutomorphism q 3) g hg hfixed
  let W := wordUnit A hs hp Base Index (q.Extension 3) (expandRelative r)
  have huR : u∈R := (mem_fixedPositiveRaw_iff q u).mpr ⟨hu,huf⟩
  have hvR : inversionEmbedding (q.Extension 3) (expandRelative r) v∈R :=
    (mem_fixedPositiveRaw_iff q _).mpr ⟨v.val.property,hvf⟩
  have hdD := rootLineDiagonal_le_diagonal (q.Extension 3) hdiag
  have hdR : d∈Subgroup.normalizer (R : Set ((Matrix GeckIndex GeckIndex (q.Extension 3))ˣ)) := by
    change d∈Subgroup.normalizer (fixedPositiveRaw q : Set ((Matrix GeckIndex GeckIndex (q.Extension 3))ˣ))
    rw [fixedPositiveRaw_eq_signedFixed]
    exact normalizes_inf_fixed tau (Positive (q.Extension 3)) d hdf hdD.1.1
  have hdN : d∈Subgroup.normalizer (N : Set ((Matrix GeckIndex GeckIndex (q.Extension 3))ˣ)) :=
    normalizes_inf_fixed tau (Negative (q.Extension 3)) d hdf hdD.1.2
  have hmap : R.map (MulAut.conj g).toMonoidHom=
      ((R.map (MulAut.conj W).toMonoidHom).map (MulAut.conj d).toMonoidHom).map
        (MulAut.conj u).toMonoidHom :=
    conjugate_cell R g u d W _ he (R.le_normalizer hvR)
  have hstripU : R⊓(R.map (MulAut.conj W).toMonoidHom).map (MulAut.conj d).toMonoidHom=⊥ := by
    apply (inf_conjugate_eq_bot_iff R _ u (R.le_normalizer huR)).mp
    rw [←hmap]
    exact hdisj
  have hstripD : R⊓R.map (MulAut.conj W).toMonoidHom=⊥ :=
    (inf_conjugate_eq_bot_iff R _ d hdR).mp hstripU
  have hW : R.map (MulAut.conj W).toMonoidHom=N :=
    fixed_positive_image_eq_negative_of_disjoint q r hstripD
  refine ⟨u,huR,?_⟩
  rw [hmap,hW,conjugate_eq_of_mem_normalizer N d hdN]

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedBruhatOppositeAlignment
