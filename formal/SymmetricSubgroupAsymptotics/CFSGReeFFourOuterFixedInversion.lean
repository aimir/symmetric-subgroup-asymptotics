import SymmetricSubgroupAsymptotics.CFSGReeFFourOuterInversionCoverage
import SymmetricSubgroupAsymptotics.CFSGFFourOriginalMiddleParameterHoms
import SymmetricSubgroupAsymptotics.CFSGReeFFourOuterFixedRoot

/-! The full actual fixed outer inversion block is the constructed
additive outer root group, and has exactly q elements. Ordinary source
coverage, the literal exceptional automorphism, and parameter injectivity
are all retained; no lifting of fixed points is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOuterFixedInversion
open CFSG.Models.Chevalley CFSGSerreModelRootGeneration CFSGFFourOriginalMiddleWords
open CFSGFFourOriginalMiddleParameterHoms CFSGReeFFourOuterInversionCoverage
open CFSGReeFFourFieldParameters CFSGReeFFourOriginalAutomorphism
open CFSGReeFFourOriginalInversionFactors CFSGReeFFourRelativeSimpleWeyl
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourOuterFixedRoot
open CFSGE6GeckOuterTripleChart CFSGE6GeckOuterInversionGroup

private theorem source_outer_words_commute (K : Type) [_root_.Field K] [Finite K] [CharP K 2]
    (a b c d : K) : Commute (sourceOuterWord K a b) (sourceOuterWord K c d) := by
  apply Commute.of_map (rawHom_injective K)
  rw [rawHom_sourceOuterWord,rawHom_sourceOuterWord]
  exact (Commute.all _ _).map (rawTripleHom K)

theorem sourceOuterWord_twist (m : ℕ) (a b : Field m) :
    reeAutomorphism m (sourceOuterWord (Field m) a b)=
      sourceOuterWord (Field m) (beta m b) (alpha m a) := by
  have hc : Commute (modelRoot CartanMatrix.F₄ (Field m) false 0 (beta m b))
      (modelRoot CartanMatrix.F₄ (Field m) false 3 (alpha m a)) := by
    simpa only [sourceOuterWord,source_root_zero,mul_one,one_mul] using
      source_outer_words_commute (Field m) (beta m b) 0 0 (alpha m a)
  simp only [sourceOuterWord,map_mul,reeAutomorphism_root]
  change modelRoot CartanMatrix.F₄ (Field m) false 3 (alpha m a)*
      modelRoot CartanMatrix.F₄ (Field m) false 0 (beta m b)=
    modelRoot CartanMatrix.F₄ (Field m) false 0 (beta m b)*
      modelRoot CartanMatrix.F₄ (Field m) false 3 (alpha m a)
  exact hc.eq.symm

theorem sourceOuterWord_fixed_iff (m : ℕ) (a b : Field m) :
    reeAutomorphism m (sourceOuterWord (Field m) a b)=sourceOuterWord (Field m) a b ↔
      b=alpha m a := by
  rw [sourceOuterWord_twist]
  constructor
  · intro he
    have hp : (beta m b,alpha m a)=(a,b) := sourceOuterWord_injective (Field m) he
    exact (congrArg (fun p : Field m×Field m=>p.2) hp).symm
  · intro he
    rw [he,beta_alpha]

def fixedOuterInversion (m : ℕ) : Subgroup (originalModelFixed m) :=
  (modelInversion m (outerRelativeWeyl m)).comap (originalModelFixed m).subtype

theorem fixedOuterInversion_eq_range (m : ℕ) :
    fixedOuterInversion m=(fixedOuterHom m).range := by
  apply le_antisymm
  · intro g hg
    obtain ⟨a,b,hab⟩ := exists_source_outer_parameters m g.val hg
    have hb : b=alpha m a := (sourceOuterWord_fixed_iff m a b).mp (by
      rw [hab]
      exact g.property)
    refine ⟨Multiplicative.ofAdd a,?_⟩
    apply Subtype.ext
    change sourceOuterWord (Field m) a (alpha m a)=g.val
    rw [←hb]
    exact hab
  · rintro g ⟨a,rfl⟩
    change (fixedOuterHom m a).val∈modelInversion m (outerRelativeWeyl m)
    have hraw : rawHom (Field m) (fixedOuterHom m a).val∈outerInversion (Field m) := by
      rw [outerInversion_eq_triple_range]
      refine ⟨((a,a),Multiplicative.ofAdd (alpha m a.toAdd)),?_⟩
      exact (rawHom_sourceOuterWord (Field m) a.toAdd (alpha m a.toAdd)).symm
    refine ⟨hraw.1,?_⟩
    change rawHom (Field m) (outerRelativeWeyl m*(fixedOuterHom m a).val*
      (outerRelativeWeyl m)⁻¹)∈CFSGTwistedE6GeckPositiveTwist.Negative (Field m)
    rw [map_mul,map_mul,map_inv,CFSGReeFFourRelativeWeylRawWords.rawHom_outerRelativeWeyl]
    simpa only [CFSGReeFFourOuterInversionRoots.blockWord,
      CFSGNormTwoGeckIntegralWord.word_eq_canonicalWord] using hraw.2

theorem fixedOuterInversion_card (m : ℕ) : Nat.card (fixedOuterInversion m)=2^(2*m+1) := by
  rw [fixedOuterInversion_eq_range]
  calc
    Nat.card (fixedOuterHom m).range=Nat.card (Multiplicative (Field m)) :=
      (Nat.card_congr (MonoidHom.ofInjective (fixedOuterHom_injective m)).toEquiv).symm
    _=Nat.card (Field m) := Nat.card_congr Multiplicative.toAdd
    _=2^(2*m+1) := field_card m

end SymmetricSubgroupAsymptotics.CFSGReeFFourOuterFixedInversion
