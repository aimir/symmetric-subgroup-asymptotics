import SymmetricSubgroupAsymptotics.SixPairCyclicSymmetricSocles
import SymmetricSubgroupAsymptotics.SixPairPrimitiveAllNormalB6
import SymmetricSubgroupAsymptotics.OriginalKernelElementaryChart
import SymmetricSubgroupAsymptotics.NormalGeneratorActualIntersectionImage
import SymmetricSubgroupAsymptotics.NormalGeneratorQuotientSocles
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CyclicSixPairSingletonTopOriginalSocles

/-- The cyclic pair action bounds every correlated actual kernel section;
the actual top normal image occupies the second generator position. -/
theorem normal_pairs_of_uniform_top {U : Subgroup (Equiv.Perm (Fin 12))}
    (F : BinaryPairFrame U (Fin 6))
    (hpair : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) F.top.range (Fin 6)) 1)
    (hTop : ∀ L : Subgroup F.top.range,L.Normal →
      ∃ x : Fin 1 → F.top.range,Subgroup.normalClosure (Set.range x)=L) :
    ∀ N : Subgroup U,N.Normal →
      ∃ x : Fin 2 → U,Subgroup.normalClosure (Set.range x)=N := by
  let A := SixPairPrimitiveAllNormalB6.kernelModule F
  let E := SixPairPrimitiveAllNormalB6.originalKernelChart F
  letI : FiniteDimensional (ZMod 2) A := by
    change FiniteDimensional (ZMod 2) F.kernelSpace
    infer_instance
  let j : Representation.IntertwiningMap A.ρ
      (permutationFunctionRepresentation (ZMod 2) F.top.range (Fin 6)) :=
    { toLinearMap := F.kernelSpace.subtype,isIntertwining' _ := rfl }
  have hu : UniformSubrepresentationGeneratorBound A.ρ 1 :=
    hpair.of_injective j (fun _ _ h => Subtype.ext h)
  let pi := F.top.rangeRestrict
  intro N hN
  letI := hN
  have hk : MarkedC4.normalGen (N ⊓ pi.ker)≤1 :=
    E.kernel_normalGen_le pi A F.top.rangeRestrict_surjective 1 hu _ inf_le_right
  letI : (N.map pi).Normal := Subgroup.Normal.map hN pi F.top.rangeRestrict_surjective
  obtain ⟨x,hx⟩ := hTop (N.map pi) inferInstance
  have hi : MarkedC4.normalGen (N.map pi)≤1 := normalGen_le_of_fin_tuple x hx
  have hn : MarkedC4.normalGen N≤2 :=
    normalGen_le_actual_intersection_add_image pi F.top.rangeRestrict_surjective N 1 1 hk hi
  exact exists_normal_generating_tuple_of_normalGen_le N hn

theorem normal_pairs {U : Subgroup (Equiv.Perm (Fin 12))}
    (F : BinaryPairFrame U (Fin 6)) (g : U)
    (hg : F.top g=SixPairCyclicSymmetricSocles.cycle)
    (hTop : ∀ L : Subgroup F.top.range,L.Normal →
      ∃ x : Fin 1 → F.top.range,Subgroup.normalClosure (Set.range x)=L) :
    ∀ N : Subgroup U,N.Normal →
      ∃ x : Fin 2 → U,Subgroup.normalClosure (Set.range x)=N :=
  normal_pairs_of_uniform_top F (SixPairCyclicSymmetricSocles.uniform F g hg) hTop

theorem quotientSocle_of_uniform_top {U : Subgroup (Equiv.Perm (Fin 12))}
    (F : BinaryPairFrame U (Fin 6))
    (hpair : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) F.top.range (Fin 6)) 1)
    (hTop : ∀ L : Subgroup F.top.range,L.Normal →
      ∃ x : Fin 1 → F.top.range,Subgroup.normalClosure (Set.range x)=L)
    (N : Subgroup U) [N.Normal] : SocleNormalGeneratorBound (U ⧸ N) 2 :=
  quotientSocleNormalGeneratorBound_of_normal_generating_tuples
    (normal_pairs_of_uniform_top F hpair hTop) N

theorem quotientSocle {U : Subgroup (Equiv.Perm (Fin 12))}
    (F : BinaryPairFrame U (Fin 6)) (g : U)
    (hg : F.top g=SixPairCyclicSymmetricSocles.cycle)
    (hTop : ∀ L : Subgroup F.top.range,L.Normal →
      ∃ x : Fin 1 → F.top.range,Subgroup.normalClosure (Set.range x)=L)
    (N : Subgroup U) [N.Normal] : SocleNormalGeneratorBound (U ⧸ N) 2 :=
  quotientSocleNormalGeneratorBound_of_normal_generating_tuples (normal_pairs F g hg hTop) N
end SymmetricSubgroupAsymptotics.CyclicSixPairSingletonTopOriginalSocles
