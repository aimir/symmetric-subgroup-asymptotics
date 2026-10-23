import SymmetricSubgroupAsymptotics.CFSGE6GeckOppositionUpperNormalizer
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOppositionSimpleRatio
import SymmetricSubgroupAsymptotics.CFSGE6GeckMinimalOvergroups

/-! The displayed opposite orbit parabolics are conjugates of the
already intrinsic positive minimal parabolics. The actual opposition
commutator is retained in the whole negative normalizer, rather than
being asserted to lie in a generated torus. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckOppositionParabolicTransport
open CFSGE6GeckOppositionUpperNormalizer CFSGTwistedE6GeckOppositionSimpleRatio
open CFSGE6GeckOppositeOrbitParabolic CFSGE6GeckMinimalOvergroups
open CFSGE6GeckIntermediateOvergroup CFSGTwistedE6GeckRelativeRootGenerated
open CFSGTwistedE6GeckRelativeOpposition CFSGTwistedE6GeckDiagramCovariance
open CFSGTwistedE6RelativeWeylOrbits CFSGSerreQuadraticWeylWord

private theorem conjugate_sup_closure {G : Type*} [Group G] (B N : Subgroup G)
    (e : MulAut G) (w d : G) (hB : B.map e.toMonoidHom=N) (hdN : d∈N)
    (he : e w=d*w) :
    (B⊔Subgroup.closure {w}).map e.toMonoidHom=N⊔Subgroup.closure {w} := by
  let H := (B⊔Subgroup.closure {w}).map e.toMonoidHom
  let Q := N⊔Subgroup.closure {w}
  have hN : N≤H := by
    rw [←hB]
    exact Subgroup.map_mono le_sup_left
  have hwH : e w∈H :=
    ⟨w,(show Subgroup.closure {w}≤B⊔Subgroup.closure {w} from le_sup_right)
      (Subgroup.subset_closure (Set.mem_singleton _)),rfl⟩
  have hw : w∈H := by
    have hh := H.mul_mem (H.inv_mem (hN hdN)) hwH
    rw [he] at hh
    simpa only [inv_mul_cancel_left] using hh
  apply le_antisymm
  · rw [Subgroup.map_sup,hB]
    apply sup_le le_sup_left
    apply Subgroup.map_le_iff_le_comap.mpr
    apply (Subgroup.closure_le _).mpr
    apply Set.singleton_subset_iff.mpr
    change e w∈Q
    rw [he]
    exact Q.mul_mem ((show N≤Q from le_sup_left) hdN)
      ((show Subgroup.closure {w}≤Q from le_sup_right)
        (Subgroup.subset_closure (Set.mem_singleton _)))
  · exact sup_le hN ((Subgroup.closure_le _).mpr (Set.singleton_subset_iff.mpr hw))

theorem oppositionSimpleRatio_mem_negativeNormalizer (K : Type) [Field K]
    (sigma : K≃+*K) (a : Fin 4) :
    oppositionSimpleRatio K a∈negativeGeneratedNormalizer K sigma := by
  have hW : canonicalWord rawData K (orbitWord a)∈fixedRootGenerated K sigma :=
    oppositeOrbitParabolic_le_generated K sigma a
      ((show Subgroup.closure {canonicalWord rawData K (orbitWord a)}≤
        oppositeOrbitParabolic K sigma a from le_sup_right)
          (Subgroup.subset_closure (Set.mem_singleton _)))
  have hO := relativeOpposition_mem_generated K sigma
  have hJ : oppositionSimpleRatio K a∈fixedRootGenerated K sigma := by
    change relativeOpposition K*canonicalWord rawData K (orbitWord a)*(relativeOpposition K)⁻¹*
      (canonicalWord rawData K (orbitWord a))⁻¹∈fixedRootGenerated K sigma
    exact (fixedRootGenerated K sigma).mul_mem
      ((fixedRootGenerated K sigma).mul_mem
        ((fixedRootGenerated K sigma).mul_mem hO hW)
        ((fixedRootGenerated K sigma).inv_mem hO))
      ((fixedRootGenerated K sigma).inv_mem hW)
  exact diagonal_generated_le_negativeNormalizer K sigma
    ⟨opposition_simple_commutator_mem_diagonalNormalizer K a,hJ⟩

theorem simpleParabolic_opposition_map (K : Type) [Field K] [Finite K]
    (sigma : K≃+*K) (a : Fin 4) :
    (simpleParabolic K (fixedRootGenerated K sigma) a).map
      (MulAut.conj (relativeOpposition K)).toMonoidHom=oppositeOrbitParabolic K sigma a := by
  apply conjugate_sup_closure _ _ (MulAut.conj (relativeOpposition K))
    (canonicalWord rawData K (orbitWord a)) (oppositionSimpleRatio K a)
    (upperIn_opposition_map K sigma) (oppositionSimpleRatio_mem_negativeNormalizer K sigma a)
  change relativeOpposition K*canonicalWord rawData K (orbitWord a)*(relativeOpposition K)⁻¹=
    (relativeOpposition K*canonicalWord rawData K (orbitWord a)*(relativeOpposition K)⁻¹*
      (canonicalWord rawData K (orbitWord a))⁻¹)*canonicalWord rawData K (orbitWord a)
  group

end SymmetricSubgroupAsymptotics.CFSGE6GeckOppositionParabolicTransport
