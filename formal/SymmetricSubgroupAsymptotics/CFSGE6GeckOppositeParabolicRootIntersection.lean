import SymmetricSubgroupAsymptotics.CFSGE6GeckOppositeOrbitParabolic
import SymmetricSubgroupAsymptotics.CFSGE6GeckSimpleChartWeyl

/-! The actual fixed positive group intersects each opposite rank-one
parabolic in exactly its singleton/orthogonal-pair parameter chart.
This is a literal subgroup equality, uniform in all characteristics.
No folded abelianization or centre recognition is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckOppositeParabolicRootIntersection
open CFSGE6GeckOppositeOrbitParabolic CFSGE6GeckSimpleChartWeyl
open CFSGE6GeckFixedOrbitRootGroups CFSGE6GeckFixedSimpleParameters
open CFSGE6GeckOrbitRootIntersection CFSGE6GeckSignedSimpleParameters
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckRelativeRootGenerated
open CFSGTwistedE6RelativeWeylOrbits CFSGSerreQuadraticWeylWord

private theorem mem_of_conjugate {G : Type*} [Group G] (H : Subgroup G)
    (w x : G) (hw : w∈H) (hx : w*x*w⁻¹∈H) : x∈H := by
  have hh := H.mul_mem (H.mul_mem (H.inv_mem hw) hx) hw
  have he : w⁻¹*(w*x*w⁻¹)*w=x := by group
  exact he ▸ hh

private theorem paired_chart_mem (K : Type) [Field K] (sigma : K≃+*K)
    (hsigma : Function.Involutive sigma) (j : Fin 2) (a : Multiplicative K) :
    rawPairedHom K sigma false j a∈oppositeOrbitParabolic K sigma (pairedOrbit j) := by
  let H := oppositeOrbitParabolic K sigma (pairedOrbit j)
  have hw : canonicalWord rawData K (orbitWord (pairedOrbit j))∈H :=
    (show Subgroup.closure {canonicalWord rawData K (orbitWord (pairedOrbit j))}≤H from
      le_sup_right) (Subgroup.subset_closure (Set.mem_singleton _))
  apply mem_of_conjugate H _ _ hw
  have he := paired_word_conjugates K sigma j a.toAdd
  change canonicalWord rawData K (orbitWord (pairedOrbit j))*
    rawPairedHom K sigma false j a*
    (canonicalWord rawData K (orbitWord (pairedOrbit j)))⁻¹=
    rawPairedHom K sigma true j (Multiplicative.ofAdd (-a.toAdd)) at he
  rw [he]
  exact (show negativeGeneratedNormalizer K sigma≤H from le_sup_left)
    (fixed_negative_le_normalizer K sigma
      (pairedFixedHom K sigma hsigma true j (Multiplicative.ofAdd (-a.toAdd))).property)

private theorem singleton_chart_mem (K : Type) [Field K] (sigma : K≃+*K)
    (j : Fin 2) (a : Multiplicative (fixedCoefficient K sigma)) :
    rawSingletonHom K false j (Multiplicative.ofAdd (a.toAdd : K))∈
      oppositeOrbitParabolic K sigma (singletonOrbit j) := by
  let H := oppositeOrbitParabolic K sigma (singletonOrbit j)
  have hw : canonicalWord rawData K (orbitWord (singletonOrbit j))∈H :=
    (show Subgroup.closure {canonicalWord rawData K (orbitWord (singletonOrbit j))}≤H from
      le_sup_right) (Subgroup.subset_closure (Set.mem_singleton _))
  apply mem_of_conjugate H _ _ hw
  rw [singleton_word_conjugates K j (a.toAdd : K)]
  exact (show negativeGeneratedNormalizer K sigma≤H from le_sup_left)
    (fixed_negative_le_normalizer K sigma
      (singletonFixedHom K sigma true j (Multiplicative.ofAdd (-a.toAdd))).property)

theorem fixedOrbitPositive_le_oppositeOrbitParabolic (K : Type) [Field K]
    (sigma : K≃+*K) (hsigma : Function.Involutive sigma) (a : Fin 4) :
    fixedOrbitPositive K sigma a≤
      (oppositeOrbitParabolic K sigma a).subgroupOf (signedFixed K sigma false) := by
  have hp (j : Fin 2) : fixedOrbitPositive K sigma (pairedOrbit j)≤
      (oppositeOrbitParabolic K sigma (pairedOrbit j)).subgroupOf (signedFixed K sigma false) := by
    rw [fixedOrbitPositive_paired K sigma hsigma j]
    rintro _ ⟨a,rfl⟩
    exact paired_chart_mem K sigma hsigma j a
  have hs (j : Fin 2) : fixedOrbitPositive K sigma (singletonOrbit j)≤
      (oppositeOrbitParabolic K sigma (singletonOrbit j)).subgroupOf (signedFixed K sigma false) := by
    rw [fixedOrbitPositive_singleton K sigma j]
    rintro _ ⟨a,rfl⟩
    exact singleton_chart_mem K sigma j a
  fin_cases a
  · exact hp 0
  · exact hp 1
  · exact hs 1
  · exact hs 0

theorem fixed_positive_inf_oppositeOrbitParabolic (K : Type) [Field K] [Finite K]
    (sigma : K≃+*K) (hsigma : Function.Involutive sigma) (a : Fin 4) :
    (oppositeOrbitParabolic K sigma a).subgroupOf (signedFixed K sigma false)=
      fixedOrbitPositive K sigma a := by
  apply le_antisymm
  · intro g hg
    change g.val∈orbitPositiveGroup K a
    rw [←positive_inf_orbitLowerFlag K a]
    exact ⟨g.property.1,oppositeOrbitParabolic_le_orbitLowerFlag K sigma a hg⟩
  · exact fixedOrbitPositive_le_oppositeOrbitParabolic K sigma hsigma a

end SymmetricSubgroupAsymptotics.CFSGE6GeckOppositeParabolicRootIntersection
