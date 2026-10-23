import SymmetricSubgroupAsymptotics.CFSGE6GeckIntermediateOvergroup
import SymmetricSubgroupAsymptotics.CFSGE6GeckSimpleOrbitFlags

/-! The four actual folded rank-one overgroups are exactly the minimal
strict overgroups of the intrinsic upper normalizer, in every group
J<=L<=P. Integral flags rule out every other simple Weyl representative;
actual overgroup extraction proves minimality without a BN-pair premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckMinimalOvergroups
open CFSGE6GeckIntermediateOvergroup CFSGE6GeckSimpleOrbitFlags
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckRelativeRootGenerated
open CFSGTwistedE6GeckFixedRangePreimage CFSGTwistedE6RelativeWeylOrbits
open CFSGTwistedE6FixedWordClassification
open CFSGTwistedE6GeckNormalizerEnvelope CFSGNormTwoGeckIntegralWord
open CFSGSerreQuadraticWeylWord

def simpleParabolic (K : Type) [Field K]
    (L : Subgroup (Matrix GeckIndex GeckIndex K)ˣ) (a : Fin 4) :
    Subgroup (Matrix GeckIndex GeckIndex K)ˣ :=
  upperIn K L ⊔ Subgroup.closure {canonicalWord rawData K (orbitWord a)}

theorem simpleParabolic_le_orbitFlag (K : Type) [Field K]
    (L : Subgroup (Matrix GeckIndex GeckIndex K)ˣ) (a : Fin 4) :
    simpleParabolic K L a≤orbitFlag K a := by
  apply sup_le (inf_le_left.trans (envelope_le_orbitFlag K a))
  apply (Subgroup.closure_le _).mpr
  exact Set.singleton_subset_iff.mpr (simple_weyl_mem_orbitFlag K a)

theorem upperIn_lt_simpleParabolic (K : Type) [Field K]
    (L : Subgroup (Matrix GeckIndex GeckIndex K)ˣ) (a : Fin 4) :
    upperIn K L<simpleParabolic K L a := by
  obtain ⟨b,hba⟩ := exists_ne a
  have hnot : canonicalWord rawData K (orbitWord a)∉upperIn K L := by
    intro h
    exact other_simple_weyl_not_mem_orbitFlag K b a (Ne.symm hba)
      (envelope_le_orbitFlag K b h.1)
  refine lt_iff_le_not_ge.mpr ⟨le_sup_left,?_⟩
  intro hle
  exact hnot (hle ((show Subgroup.closure {canonicalWord rawData K (orbitWord a)}≤
    simpleParabolic K L a from le_sup_right)
      (Subgroup.subset_closure (Set.mem_singleton _))))

theorem simpleParabolic_le_intermediate (K : Type) [Field K] (sigma : K≃+*K)
    (L : Subgroup (Matrix GeckIndex GeckIndex K)ˣ)
    (hJL : fixedRootGenerated K sigma≤L) (a : Fin 4) :
    simpleParabolic K L a≤L := by
  apply sup_le inf_le_right
  apply (Subgroup.closure_le _).mpr
  apply Set.singleton_subset_iff.mpr
  apply hJL
  simpa only [word_eq_canonicalWord,expandRelative,List.append_nil] using
    relativeWord_mem_generated K sigma [a]

theorem simpleParabolic_minimal (K : Type) [Field K] [Finite K] (sigma : K≃+*K)
    (L : Subgroup (Matrix GeckIndex GeckIndex K)ˣ)
    (hJL : fixedRootGenerated K sigma≤L) (hLP : L≤ambientFixedRangePreimage K sigma)
    (a : Fin 4) (H : Subgroup (Matrix GeckIndex GeckIndex K)ˣ)
    (hBH : upperIn K L<H) (hHP : H≤simpleParabolic K L a) :
    H=simpleParabolic K L a := by
  obtain ⟨b,hb⟩ := exists_simple_weyl_mem_of_upperIn_lt K sigma L H hJL hLP hBH
    (hHP.trans (simpleParabolic_le_intermediate K sigma L hJL a))
  have hba : b=a := by
    by_contra hne
    exact other_simple_weyl_not_mem_orbitFlag K a b hne
      (simpleParabolic_le_orbitFlag K L a (hHP hb))
  subst b
  apply le_antisymm hHP
  apply sup_le hBH.le
  exact (Subgroup.closure_le _).mpr (Set.singleton_subset_iff.mpr hb)

theorem minimal_overgroup_eq_simpleParabolic (K : Type) [Field K] [Finite K]
    (sigma : K≃+*K) (L : Subgroup (Matrix GeckIndex GeckIndex K)ˣ)
    (hJL : fixedRootGenerated K sigma≤L) (hLP : L≤ambientFixedRangePreimage K sigma)
    (H : Subgroup (Matrix GeckIndex GeckIndex K)ˣ)
    (hBH : upperIn K L<H) (hHL : H≤L)
    (hmin : ∀M : Subgroup (Matrix GeckIndex GeckIndex K)ˣ,
      upperIn K L<M→M≤H→M=H) :
    ∃a : Fin 4,H=simpleParabolic K L a := by
  obtain ⟨a,ha⟩ := exists_simple_weyl_mem_of_upperIn_lt K sigma L H hJL hLP hBH hHL
  refine ⟨a,(hmin _ (upperIn_lt_simpleParabolic K L a) ?_).symm⟩
  exact sup_le hBH.le ((Subgroup.closure_le _).mpr (Set.singleton_subset_iff.mpr ha))

theorem simpleParabolic_injective (K : Type) [Field K]
    (L : Subgroup (Matrix GeckIndex GeckIndex K)ˣ) : Function.Injective (simpleParabolic K L) := by
  intro a b he
  by_contra hne
  have hw : canonicalWord rawData K (orbitWord b)∈simpleParabolic K L a := by
    rw [he]
    exact (show Subgroup.closure {canonicalWord rawData K (orbitWord b)}≤
      simpleParabolic K L b from le_sup_right)
        (Subgroup.subset_closure (Set.mem_singleton _))
  exact other_simple_weyl_not_mem_orbitFlag K a b (Ne.symm hne)
    (simpleParabolic_le_orbitFlag K L a hw)

end SymmetricSubgroupAsymptotics.CFSGE6GeckMinimalOvergroups
