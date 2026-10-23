import SymmetricSubgroupAsymptotics.CFSGE6GeckNegativeOrbitRootGroups
import SymmetricSubgroupAsymptotics.CFSGE6GeckSimpleChartWeyl
import SymmetricSubgroupAsymptotics.CFSGE6GeckGeneratedParabolics

/-! The negative counterpart of actual simple-root recovery: the fixed
negative group meets a positive rank-one parabolic in exactly its full
negative singleton/paired chart, including in characteristic two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckNegativeParabolicRootIntersection
open CFSGE6GeckNegativeOrbitRootGroups CFSGE6GeckSimpleChartWeyl
open CFSGE6GeckFixedOrbitRootGroups CFSGE6GeckFixedSimpleParameters
open CFSGE6GeckSignedSimpleParameters CFSGE6GeckGeneratedParabolics
open CFSGE6GeckMinimalOvergroups CFSGE6GeckIntermediateOvergroup
open CFSGTwistedE6GeckNormalizerEnvelope CFSGTwistedE6GeckDiagramCovariance
open CFSGTwistedE6GeckRelativeRootGenerated CFSGTwistedE6GeckRootGeneratedPGroup
open CFSGTwistedE6RelativeWeylOrbits CFSGSerreQuadraticWeylWord

private theorem fixed_positive_le_upperIn (K : Type) [Field K] (sigma : K≃+*K) :
    signedFixed K sigma false≤upperIn K (fixedRootGenerated K sigma) :=
  le_inf (inf_le_left.trans (positive_le_envelope K)) (signedFixed_le_generated K sigma false)

private theorem paired_chart_mem (K : Type) [Field K] (sigma : K≃+*K)
    (hsigma : Function.Involutive sigma) (j : Fin 2) (a : Multiplicative K) :
    rawPairedHom K sigma true j a∈simpleParabolic K (fixedRootGenerated K sigma) (pairedOrbit j) := by
  let P := simpleParabolic K (fixedRootGenerated K sigma) (pairedOrbit j)
  have hw : canonicalWord rawData K (orbitWord (pairedOrbit j))∈P :=
    (show Subgroup.closure {canonicalWord rawData K (orbitWord (pairedOrbit j))}≤P from
      le_sup_right) (Subgroup.subset_closure (Set.mem_singleton _))
  have hx : rawPairedHom K sigma false j (Multiplicative.ofAdd (-a.toAdd))∈P :=
    (show upperIn K (fixedRootGenerated K sigma)≤P from le_sup_left)
      (fixed_positive_le_upperIn K sigma
        (pairedFixedHom K sigma hsigma false j (Multiplicative.ofAdd (-a.toAdd))).property)
  have hh := P.mul_mem (P.mul_mem hw hx) (P.inv_mem hw)
  have he := paired_word_conjugates K sigma j (-a.toAdd)
  rw [neg_neg] at he
  change canonicalWord rawData K (orbitWord (pairedOrbit j))*
    rawPairedHom K sigma false j (Multiplicative.ofAdd (-a.toAdd))*
    (canonicalWord rawData K (orbitWord (pairedOrbit j)))⁻¹=rawPairedHom K sigma true j a at he
  exact he ▸ hh

private theorem singleton_chart_mem (K : Type) [Field K] (sigma : K≃+*K)
    (j : Fin 2) (a : Multiplicative (fixedCoefficient K sigma)) :
    rawSingletonHom K true j (Multiplicative.ofAdd (a.toAdd : K))∈
      simpleParabolic K (fixedRootGenerated K sigma) (singletonOrbit j) := by
  let P := simpleParabolic K (fixedRootGenerated K sigma) (singletonOrbit j)
  have hw : canonicalWord rawData K (orbitWord (singletonOrbit j))∈P :=
    (show Subgroup.closure {canonicalWord rawData K (orbitWord (singletonOrbit j))}≤P from
      le_sup_right) (Subgroup.subset_closure (Set.mem_singleton _))
  have hx : rawSingletonHom K false j (Multiplicative.ofAdd (-(a.toAdd : K)))∈P :=
    (show upperIn K (fixedRootGenerated K sigma)≤P from le_sup_left)
      (fixed_positive_le_upperIn K sigma
        (singletonFixedHom K sigma false j (Multiplicative.ofAdd (-a.toAdd))).property)
  have hh := P.mul_mem (P.mul_mem hw hx) (P.inv_mem hw)
  have he := singleton_word_conjugates K j (-(a.toAdd : K))
  rw [neg_neg] at he
  exact he ▸ hh

theorem fixed_negative_inf_simpleParabolic (K : Type) [Field K] (sigma : K≃+*K)
    (hsigma : Function.Involutive sigma) (a : Fin 4) :
    (simpleParabolic K (fixedRootGenerated K sigma) a).subgroupOf (signedFixed K sigma true)=
      fixedOrbitNegative K sigma a := by
  apply le_antisymm
  · intro g hg
    change g.val∈orbitNegativeGroup K a
    rw [←negative_inf_orbitFlag K a]
    exact ⟨g.property.1,simpleParabolic_le_orbitFlag K (fixedRootGenerated K sigma) a hg⟩
  · have hp (j : Fin 2) : fixedOrbitNegative K sigma (pairedOrbit j)≤
        (simpleParabolic K (fixedRootGenerated K sigma) (pairedOrbit j)).subgroupOf
          (signedFixed K sigma true) := by
      rw [fixedOrbitNegative_paired K sigma hsigma j]
      rintro _ ⟨t,rfl⟩
      exact paired_chart_mem K sigma hsigma j t
    have hs (j : Fin 2) : fixedOrbitNegative K sigma (singletonOrbit j)≤
        (simpleParabolic K (fixedRootGenerated K sigma) (singletonOrbit j)).subgroupOf
          (signedFixed K sigma true) := by
      rw [fixedOrbitNegative_singleton K sigma j]
      rintro _ ⟨t,rfl⟩
      exact singleton_chart_mem K sigma j t
    fin_cases a
    · exact hp 0
    · exact hp 1
    · exact hs 1
    · exact hs 0

def negativeOrbitRootGenerated (K : Type) [Field K] (sigma : K≃+*K) (a : Fin 4) :
    Subgroup (fixedRootGenerated K sigma) :=
  (fixedOrbitNegative K sigma a).map (Subgroup.inclusion (signedFixed_le_generated K sigma true))

theorem negative_rootPart_inf_parabolicGenerated (K : Type) [Field K] [Finite K]
    (sigma : K≃+*K) (hsigma : Function.Involutive sigma) (a : Fin 4) :
    rootPart K sigma true⊓parabolicGenerated K sigma a=negativeOrbitRootGenerated K sigma a := by
  apply Subgroup.ext
  intro x
  constructor
  · rintro ⟨hxV,hxP⟩
    let v : signedFixed K sigma true := ⟨x.val,hxV⟩
    have hv : v∈fixedOrbitNegative K sigma a := by
      rw [←fixed_negative_inf_simpleParabolic K sigma hsigma a]
      exact hxP
    exact ⟨v,hv,Subtype.ext rfl⟩
  · rintro ⟨v,hv,rfl⟩
    refine ⟨v.property,?_⟩
    have hvP : v∈(simpleParabolic K (fixedRootGenerated K sigma) a).subgroupOf
        (signedFixed K sigma true) := by
      rw [fixed_negative_inf_simpleParabolic K sigma hsigma a]
      exact hv
    exact hvP

end SymmetricSubgroupAsymptotics.CFSGE6GeckNegativeParabolicRootIntersection
