import SymmetricSubgroupAsymptotics.CFSGE6GeckFixedOrbitRootGroups
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSelfRootConjugation

/-! The actual simple folded Weyl representative exchanges each full
singleton/paired parameter chart with its opposite, with parameter -t.
Both orthogonal factors are retained, so no bad-characteristic division
or original-source faithfulness occurs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckSimpleChartWeyl
open CFSGE6GeckFixedOrbitRootGroups CFSGE6GeckSignedSimpleParameters
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6PairedFixedRoots
open CFSGTwistedE6FixedA2 CFSGTwistedE6RelativeWeylOrbits
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoGeckOrthogonalWeyl CFSGNormTwoGeckSelfRootConjugation
open CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord
local notation "A" => CartanMatrix.E₆
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite

private theorem pair_conjugation (K : Type) [Field K] (i j : Fin 6)
    (hij : CFSGGeckSerreRepresentation.cartan E6Base E6Index i j=0)
    (hji : CFSGGeckSerreRepresentation.cartan E6Base E6Index j i=0) (a b : K) :
    (canonicalWeyl rawData K i*canonicalWeyl rawData K j)*
      (canonicalRoot rawData K false i a*canonicalRoot rawData K false j b)*
      (canonicalWeyl rawData K i*canonicalWeyl rawData K j)⁻¹=
      canonicalRoot rawData K true i (-a)*canonicalRoot rawData K true j (-b) := by
  let W := canonicalWeyl rawData K i*canonicalWeyl rawData K j
  have hi : (MulAut.conj W) (canonicalRoot rawData K false i a)=
      canonicalRoot rawData K true i (-a) := by
    have hc : canonicalWeyl rawData K j*canonicalRoot rawData K false i a*
        (canonicalWeyl rawData K j)⁻¹=canonicalRoot rawData K false i a := by
      rw [(orthogonal_weyl_root A hs hp E6Base E6Index K j i hji false a).eq]
      group
    change W*canonicalRoot rawData K false i a*W⁻¹=_
    calc
      _=canonicalWeyl rawData K i*(canonicalWeyl rawData K j*
        canonicalRoot rawData K false i a*(canonicalWeyl rawData K j)⁻¹)*
          (canonicalWeyl rawData K i)⁻¹ := by dsimp only [W];group
      _=canonicalRoot rawData K true i (-a) := by
        rw [hc]
        exact self_root_word A hs hp E6Base E6Index K i a
  have hj : (MulAut.conj W) (canonicalRoot rawData K false j b)=
      canonicalRoot rawData K true j (-b) := by
    have hc : canonicalWeyl rawData K i*canonicalRoot rawData K true j (-b)*
        (canonicalWeyl rawData K i)⁻¹=canonicalRoot rawData K true j (-b) := by
      rw [(orthogonal_weyl_root A hs hp E6Base E6Index K i j hij true (-b)).eq]
      group
    change W*canonicalRoot rawData K false j b*W⁻¹=_
    calc
      _=canonicalWeyl rawData K i*(canonicalWeyl rawData K j*
        canonicalRoot rawData K false j b*(canonicalWeyl rawData K j)⁻¹)*
          (canonicalWeyl rawData K i)⁻¹ := by dsimp only [W];group
      _=canonicalRoot rawData K true j (-b) := by
        rw [self_root_word A hs hp E6Base E6Index K j b]
        exact hc
  change (MulAut.conj W) (canonicalRoot rawData K false i a*
    canonicalRoot rawData K false j b)=_
  rw [map_mul,hi,hj]

theorem paired_word_conjugates (K : Type) [Field K] (sigma : K≃+*K) (j : Fin 2) (a : K) :
    canonicalWord rawData K (orbitWord (pairedOrbit j))*
      rawPairedHom K sigma false j (Multiplicative.ofAdd a)*
      (canonicalWord rawData K (orbitWord (pairedOrbit j)))⁻¹=
      rawPairedHom K sigma true j (Multiplicative.ofAdd (-a)) := by
  have hw : canonicalWord rawData K (orbitWord (pairedOrbit j))=
      canonicalWeyl rawData K (pairedNode j)*canonicalWeyl rawData K (pairedPartner j) := by
    fin_cases j <;> simp [pairedOrbit,orbitWord,canonicalWord,pairedNode,pairedPartner,CFSG.Models.e6Twist]
  rw [hw]
  change (canonicalWeyl rawData K (pairedNode j)*canonicalWeyl rawData K (pairedPartner j))*
    (canonicalRoot rawData K false (pairedNode j) a*
      canonicalRoot rawData K false (pairedPartner j) (sigma a))*
    (canonicalWeyl rawData K (pairedNode j)*canonicalWeyl rawData K (pairedPartner j))⁻¹=
      canonicalRoot rawData K true (pairedNode j) (-a)*
        canonicalRoot rawData K true (pairedPartner j) (sigma (-a))
  rw [map_neg]
  apply pair_conjugation
  · rw [E6_cartan]
    exact pairedNode_cartan j
  · fin_cases j <;> rw [E6_cartan] <;> decide

theorem singleton_word_conjugates (K : Type) [Field K] (j : Fin 2) (a : K) :
    canonicalWord rawData K (orbitWord (singletonOrbit j))*
      rawSingletonHom K false j (Multiplicative.ofAdd a)*
      (canonicalWord rawData K (orbitWord (singletonOrbit j)))⁻¹=
      rawSingletonHom K true j (Multiplicative.ofAdd (-a)) := by
  have hw : canonicalWord rawData K (orbitWord (singletonOrbit j))=canonicalWeyl rawData K (node j) := by
    fin_cases j <;> simp [singletonOrbit,orbitWord,canonicalWord,node]
  rw [hw]
  exact self_root_word A hs hp E6Base E6Index K (node j) a

end SymmetricSubgroupAsymptotics.CFSGE6GeckSimpleChartWeyl
