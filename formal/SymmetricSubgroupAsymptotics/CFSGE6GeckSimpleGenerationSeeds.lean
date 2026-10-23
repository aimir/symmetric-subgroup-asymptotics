import SymmetricSubgroupAsymptotics.CFSGE6GeckFixedSimpleParameters
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckSectionRootParameters
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRelativeWordTwist

/-! Every literal signed simple fixed seed and every relative section
conjugator lies in a subgroup containing the four displayed signed
simple charts. Reversed paired seeds use sigma squared equals one and
actual orthogonal root commutation, including in characteristic two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckSimpleGenerationSeeds
open CFSGE6GeckFixedSimpleParameters CFSGE6GeckSignedSimpleParameters
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckRelativeRootGenerated
open CFSGTwistedE6GeckSectionRootParameters CFSGTwistedE6GeckOriginalRootSections
open CFSGTwistedE6GeckRelativeWordTwist CFSGTwistedE6RelativeWeylOrbits
open CFSGTwistedE6GeckMatrixTwist
open CFSGTwistedE6FixedWordClassification CFSGTwistedE6FixedA2 CFSGTwistedE6PairedFixedRoots
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite CFSGNormTwoGeckOrthogonalWeyl
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylWordAlgebra CFSGNormTwoGeckIntegralWord
open CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord
variable (K : Type) [Field K] (sigma : RingAut K)
    (S : Subgroup ((Matrix GeckIndex GeckIndex K)ˣ))
    (hsingle : ∀neg j (a : fixedCoefficient K sigma),
      rawSingletonHom K neg j (Multiplicative.ofAdd (a : K))∈S)
    (hpair : ∀neg j (a : K),rawPairedHom K sigma neg j (Multiplicative.ofAdd a)∈S)

include hsingle in
theorem fixed_simple_seed_mem (neg : Bool) (j : Fin 6) (hj : CFSG.Models.e6Twist j=j)
    (a : K) (ha : sigma a=a) : canonicalRoot rawData K neg j a∈S := by
  have hn : j=1 ∨ j=3 := by
    fin_cases j
    · exact False.elim ((by decide : CFSG.Models.e6Twist (0 : Fin 6)≠0) hj)
    · exact Or.inl rfl
    · exact False.elim ((by decide : CFSG.Models.e6Twist (2 : Fin 6)≠2) hj)
    · exact Or.inr rfl
    · exact False.elim ((by decide : CFSG.Models.e6Twist (4 : Fin 6)≠4) hj)
    · exact False.elim ((by decide : CFSG.Models.e6Twist (5 : Fin 6)≠5) hj)
  rcases hn with rfl|rfl
  · exact hsingle neg 0 ⟨a,ha⟩
  · exact hsingle neg 1 ⟨a,ha⟩

include hpair in
theorem nonfixed_simple_pair_mem (hsigma : Function.Involutive sigma)
    (neg : Bool) (j : Fin 6) (hj : CFSG.Models.e6Twist j≠j) (a : K) :
    canonicalRoot rawData K neg j a*canonicalRoot rawData K neg (CFSG.Models.e6Twist j) (sigma a)∈S := by
  fin_cases j
  · exact hpair neg 0 a
  · exact False.elim (hj rfl)
  · exact hpair neg 1 a
  · exact False.elim (hj rfl)
  · have hm := hpair neg 1 (sigma a)
    change canonicalRoot rawData K neg 2 (sigma a)*canonicalRoot rawData K neg 4 (sigma (sigma a))∈S at hm
    rw [hsigma] at hm
    change canonicalRoot rawData K neg 4 a*canonicalRoot rawData K neg 2 (sigma a)∈S
    rw [(orthogonal_signed_roots CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K
      4 2 (by rw [E6_cartan];decide) neg neg a (sigma a)).eq]
    exact hm
  · have hm := hpair neg 0 (sigma a)
    change canonicalRoot rawData K neg 0 (sigma a)*canonicalRoot rawData K neg 5 (sigma (sigma a))∈S at hm
    rw [hsigma] at hm
    change canonicalRoot rawData K neg 5 a*canonicalRoot rawData K neg 0 (sigma a)∈S
    rw [(orthogonal_signed_roots CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K
      5 0 (by rw [E6_cartan];decide) neg neg a (sigma a)).eq]
    exact hm

include hsingle hpair in
theorem orbitParameter_mem (neg : Bool) (j : Fin 4) (a : K) (ha : sigma a=a) :
    orbitParameter K neg j a∈S := by
  fin_cases j
  · have hm := hpair neg 0 a
    change canonicalRoot rawData K neg 0 a*canonicalRoot rawData K neg 5 (sigma a)∈S at hm
    rwa [ha] at hm
  · have hm := hpair neg 1 a
    change canonicalRoot rawData K neg 2 a*canonicalRoot rawData K neg 4 (sigma a)∈S at hm
    rwa [ha] at hm
  · exact hsingle neg 1 ⟨a,ha⟩
  · exact hsingle neg 0 ⟨a,ha⟩

include hsingle hpair in
theorem orbit_word_mem (a : Fin 4) : canonicalWord rawData K (orbitWord a)∈S := by
  rw [orbit_word_parameter]
  exact S.mul_mem (S.mul_mem
    (orbitParameter_mem K sigma S hsingle hpair false a 1 (map_one sigma))
    (orbitParameter_mem K sigma S hsingle hpair true a (-1) (by simp)))
    (orbitParameter_mem K sigma S hsingle hpair false a 1 (map_one sigma))

include hsingle hpair in
theorem relative_word_mem (r : List (Fin 4)) :
    wordUnit CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K (expandRelative r)∈S := by
  induction r with
  | nil=>exact S.one_mem
  | cons a r ih=>
    rw [expandRelative,wordUnit_append]
    apply S.mul_mem _ ih
    rw [word_eq_canonicalWord]
    exact orbit_word_mem K sigma S hsingle hpair a

def sectionConjugator (k : PositiveRoot) : (Matrix GeckIndex GeckIndex K)ˣ :=
  (wordUnit CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K
    (expandRelative (sectionRelative k)))⁻¹

theorem sectionConjugator_eq_word (k : PositiveRoot) :
    sectionConjugator K k=canonicalWord rawData K (sectionWord k) := by
  have hi := wordUnit_inverseWord CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
    E6Base E6Index K (expandRelative (sectionRelative k))
  simpa only [sectionConjugator,sectionWord,word_eq_canonicalWord] using hi.symm

include hsingle hpair in
theorem sectionConjugator_mem (k : PositiveRoot) : sectionConjugator K k∈S :=
  S.inv_mem (relative_word_mem K sigma S hsingle hpair (sectionRelative k))

theorem sectionConjugator_fixed (k : PositiveRoot) :
    unitTwist K sigma (sectionConjugator K k)=sectionConjugator K k := by
  simp only [sectionConjugator,word_eq_canonicalWord,map_inv,relative_word_fixed]

theorem sectionParameter_val_conjugate (k : PositiveRoot) (a : K) :
    (sectionParameter K k a).val=sectionConjugator K k*canonicalRoot rawData K true (sectionNode k) a*
      (sectionConjugator K k)⁻¹ := by
  rw [sectionConjugator_eq_word]
  rfl

end SymmetricSubgroupAsymptotics.CFSGE6GeckSimpleGenerationSeeds
