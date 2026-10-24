import SymmetricSubgroupAsymptotics.CFSGE6GeckOuterInversionGroup
import SymmetricSubgroupAsymptotics.CFSGE6GeckOuterTripleFixed
import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalInversionFactors
import SymmetricSubgroupAsymptotics.CFSGReeFFourRelativeWeylRawWords
import SymmetricSubgroupAsymptotics.CFSGFFourOriginalPositiveDiagramImage

/-! Every element of the same original F4 outer inversion subgroup is
a literal product of its two outer simple roots. Coverage is obtained
from the raw three-root chart and actual diagram fixedness, rather than
from an assumed source root factorization. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOuterInversionCoverage
open CFSG.Models.Chevalley CFSGSerreModelRootGeneration CFSGFFourOriginalMiddleWords
open CFSGReeFFourFieldParameters CFSGReeFFourOriginalInversionFactors
open CFSGReeFFourRelativeSimpleWeyl CFSGReeFFourRelativeWeylRawWords
open CFSGFFourOriginalPositiveDiagramImage CFSGFFourE6FixedGeneratedGroup
open CFSGE6GeckOuterInversionGroup CFSGE6GeckOuterTripleChart CFSGE6GeckOuterTripleFixed
open CFSGReeFFourOuterInversionRoots CFSGTwistedE6GeckMatrixTwist
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckPositiveTwist
open CFSGNormTwoGeckIntegralWord CFSGSerreQuadraticWeylWord

 def sourceOuterWord (K : Type) [_root_.Field K] (a b : K) : Model CartanMatrix.F₄ K :=
  modelRoot CartanMatrix.F₄ K false 0 a*modelRoot CartanMatrix.F₄ K false 3 b

theorem rawHom_sourceOuterWord (K : Type) [_root_.Field K] [Finite K] [CharP K 2]
    (a b : K) : rawHom K (sourceOuterWord K a b)=
      rawTripleHom K ((Multiplicative.ofAdd a,Multiplicative.ofAdd a),Multiplicative.ofAdd b) := by
  simp only [sourceOuterWord,map_mul,rawHom_root,folded_root_eq_orbitParameter]
  rfl

theorem sourceOuterWord_injective (K : Type) [_root_.Field K] [Finite K] [CharP K 2] :
    Function.Injective (fun p : K×K=>sourceOuterWord K p.1 p.2) := by
  intro a b he
  have hr := congrArg (rawHom K) he
  dsimp only at hr
  rw [rawHom_sourceOuterWord,rawHom_sourceOuterWord] at hr
  have hp := rawTripleHom_injective K hr
  apply Prod.ext
  · exact congrArg (fun z : (Multiplicative K×Multiplicative K)×Multiplicative K=>z.1.1.toAdd) hp
  · exact congrArg (fun z : (Multiplicative K×Multiplicative K)×Multiplicative K=>z.2.toAdd) hp

theorem rawHom_mem_outerInversion (m : ℕ)
    (g : Model CartanMatrix.F₄ (Field m))
    (hg : g∈modelInversion m (outerRelativeWeyl m)) : rawHom (Field m) g∈outerInversion (Field m) := by
  refine ⟨hg.1,?_⟩
  have hn := hg.2
  change rawHom (Field m) (outerRelativeWeyl m*g*(outerRelativeWeyl m)⁻¹)∈Negative (Field m) at hn
  rw [map_mul,map_mul,map_inv,rawHom_outerRelativeWeyl] at hn
  simpa only [blockWord,word_eq_canonicalWord] using hn

theorem exists_source_outer_parameters (m : ℕ)
    (g : Model CartanMatrix.F₄ (Field m)) (hg : g∈modelInversion m (outerRelativeWeyl m)) :
    ∃a b : Field m,sourceOuterWord (Field m) a b=g := by
  obtain ⟨p,hp⟩ := exists_triple_of_inversion (Field m) (rawHom (Field m) g)
    (rawHom_mem_outerInversion m g hg)
  rcases p with ⟨⟨a,c⟩,b⟩
  have hfixed : unitTwist (Field m) (RingEquiv.refl (Field m))
      (rawTripleHom (Field m) ((a,c),b))=rawTripleHom (Field m) ((a,c),b) := by
    rw [hp]
    exact rawHom_diagram_fixed (Field m) g
  have hac : a=c := (triple_fixed_iff (Field m) ((a,c),b)).mp hfixed
  subst c
  refine ⟨a.toAdd,b.toAdd,?_⟩
  apply rawHom_injective (Field m)
  rw [rawHom_sourceOuterWord]
  exact hp

end SymmetricSubgroupAsymptotics.CFSGReeFFourOuterInversionCoverage
