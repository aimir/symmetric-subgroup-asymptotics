import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckFixedWordOpposition
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedRootLineCell
import SymmetricSubgroupAsymptotics.CFSGSubgroupConjugateDisjoint

/-! The actual identity-twist positive group acts transitively on its
disjoint conjugates inside the fixed matrix group. The proof uses
proved fixed Bruhat factors and the actual fixed root tests. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckFixedBruhatOppositeAlignment
open CFSGGTwoD4GeckFixedWordOpposition CFSGTrialityGeckFixedRootLineCell
open CFSGTrialityGeckBruhatCellFactors CFSGTrialityGeckRootLineDiagonal
open CFSGTrialityGeckNormalizerEnvelope CFSGTrialityGeckRelativeRootGenerated
open CFSGTrialityGeckPositiveTwist CFSGTrialityGeckDiagramCovariance
open CFSGTrialityD4NormTwo CFSGTrialityRelativeWordLanguage
open CFSGTrialityGeckMatrixTwist CFSGTrialityGeckSourceWordAction
open CFSGNormTwoGeckWeylWordDegree CFSGSubgroupConjugateOrbitCardinality
open CFSGFixedSubgroupConjugation CFSGSubgroupConjugateDisjoint
local notation "A" => CartanMatrix.D 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots A) := Classical.decEq _

private theorem conjugate_cell {G : Type*} [Group G] (R : Subgroup G)
    (g u d W v : G) (he : g = (u * d) * W * v)
    (hv : v ∈ Subgroup.normalizer (R : Set G)) :
    R.map (MulAut.conj g).toMonoidHom =
      ((R.map (MulAut.conj W).toMonoidHom).map (MulAut.conj d).toMonoidHom).map
        (MulAut.conj u).toMonoidHom := by
  rw [he, conjugate_mul, conjugate_eq_of_mem_normalizer R v hv, conjugate_mul, conjugate_mul]

theorem fixed_opposite_conjugate_by_positive (K : Type) [Field K] [Finite K]
    (g : (Matrix GeckIndex GeckIndex K)ˣ) (hg : g ∈ MatrixGroup K)
    (hfixed : unitTwist K (RingEquiv.refl K) g = g)
    (hdisj : signedFixed K (RingEquiv.refl K) false ⊓
      (signedFixed K (RingEquiv.refl K) false).map (MulAut.conj g).toMonoidHom = ⊥) :
    ∃ u ∈ signedFixed K (RingEquiv.refl K) false,
      (signedFixed K (RingEquiv.refl K) false).map (MulAut.conj g).toMonoidHom =
        (signedFixed K (RingEquiv.refl K) true).map (MulAut.conj u).toMonoidHom := by
  let R := signedFixed K (RingEquiv.refl K) false
  let N := signedFixed K (RingEquiv.refl K) true
  let tau := unitTwist K (RingEquiv.refl K)
  obtain ⟨r, u, d, hu, huf, hdiag, hdf, v, hvf, he⟩ :=
    exists_fixed_rootLine_cell K (RingEquiv.refl K) g hg hfixed
  let W := wordUnit A hs hp Base Index K (expandRelative r)
  have huR : u ∈ R := ⟨hu, huf⟩
  have hvR : inversionEmbedding K (expandRelative r) v ∈ R := ⟨v.val.property, hvf⟩
  have hdD := rootLineDiagonal_le_diagonal K hdiag
  have hdR : d ∈ Subgroup.normalizer (R : Set ((Matrix GeckIndex GeckIndex K)ˣ)) :=
    normalizes_inf_fixed tau (Positive K) d hdf hdD.1.1
  have hdN : d ∈ Subgroup.normalizer (N : Set ((Matrix GeckIndex GeckIndex K)ˣ)) :=
    normalizes_inf_fixed tau (Negative K) d hdf hdD.1.2
  have hmap : R.map (MulAut.conj g).toMonoidHom =
      ((R.map (MulAut.conj W).toMonoidHom).map (MulAut.conj d).toMonoidHom).map
        (MulAut.conj u).toMonoidHom :=
    conjugate_cell R g u d W _ he (R.le_normalizer hvR)
  have hstripU : R ⊓ (R.map (MulAut.conj W).toMonoidHom).map
      (MulAut.conj d).toMonoidHom = ⊥ := by
    apply (inf_conjugate_eq_bot_iff R _ u (R.le_normalizer huR)).mp
    rw [←hmap]
    exact hdisj
  have hstripD : R ⊓ R.map (MulAut.conj W).toMonoidHom = ⊥ :=
    (inf_conjugate_eq_bot_iff R _ d hdR).mp hstripU
  have hW : R.map (MulAut.conj W).toMonoidHom = N :=
    fixed_positive_image_eq_negative_of_disjoint K r hstripD
  refine ⟨u, huR, ?_⟩
  rw [hmap, hW, conjugate_eq_of_mem_normalizer N d hdN]

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckFixedBruhatOppositeAlignment
