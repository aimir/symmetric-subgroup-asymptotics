import SymmetricSubgroupAsymptotics.WreathNormalBaseCoordinates
import SymmetricSubgroupAsymptotics.MinimalNormalCompositionCharts
import SymmetricSubgroupAsymptotics.SemisimpleNormalSubdirectRigidity
import SymmetricSubgroupAsymptotics.MinimalNormalInternalFactorOrdinaryGenerators

/-! The actual nonabelian local-kernel step in a full-component wreath
embedding. The global kernel is the literal kernel of the compressed
original embedding, retaining all diagonal relations. Local minimality,
original top transitivity, and the proved normal-subdirect rigidity give
actual global minimal normality. The ordinary bound charges a genuine
internally normal factor; no unproved nonabelian '+1' is asserted. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.WreathNonabelianChiefOrdinaryStep
open PermutationalWreathProduct

variable {G D D' Q I : Type} [Group G] [Finite G]
    [Group D] [Finite D] [Group D'] [Group Q] [Fintype I]
    [MulAction Q I] [MulAction.IsPretransitive Q I]
    (rho : G →* PermutationalWreathProduct D Q I) (phi : D →* D')

theorem kernel_le_base : Compression.kernel rho phi ≤ (rightHom.comp rho).ker := by
  intro g hg
  have hm : rho g ∈ (mapBase phi).ker := hg
  exact ((mem_mapBase_ker_iff phi (rho g)).mp hm).1

theorem normal_coordinate_range_eq_local_kernel
    (hrho : Function.Injective rho) (htop : Function.Surjective (rightHom.comp rho))
    (hfull : Compression.FullComponent rho) (hmin : IsMinimalNormalSubgroup phi.ker)
    (M : Subgroup G) [M.Normal] (hM : M ≠ ⊥)
    (hME : M ≤ Compression.kernel rho phi) (i : I) :
    (WreathNormalBaseCoordinates.coordinate rho M
      (hME.trans (kernel_le_base rho phi)) i).range = phi.ker := by
  have hn := WreathNormalBaseCoordinates.coordinate_range_normal rho M
    (hME.trans (kernel_le_base rho phi)) hfull i
  have hne := WreathNormalBaseCoordinates.all_coordinate_nontrivial rho M
    (hME.trans (kernel_le_base rho phi)) hrho htop hM i
  apply hmin.2.2 _ hn hne
  rintro d ⟨m, rfl⟩
  change (rho m.val).left i ∈ phi.ker
  have hm : rho m.val ∈ (mapBase phi).ker := hME m.property
  exact ((mem_mapBase_ker_iff phi (rho m.val)).mp hm).2 i

/-- Every nonzero original ambient-normal subkernel maps ONTO the local
kernel in every original block, not merely onto a chosen chart type. -/
theorem kernelCoordinate_restriction_surjective
    (hrho : Function.Injective rho) (htop : Function.Surjective (rightHom.comp rho))
    (hfull : Compression.FullComponent rho) (hmin : IsMinimalNormalSubgroup phi.ker)
    (M : Subgroup G) [M.Normal] (hM : M ≠ ⊥)
    (hME : M ≤ Compression.kernel rho phi) (i : I) :
    Function.Surjective ((Compression.kernelCoordinate rho phi i).comp
      (M.subgroupOf (Compression.kernel rho phi)).subtype) := by
  intro n
  have hn : n.val ∈ (WreathNormalBaseCoordinates.coordinate rho M
      (hME.trans (kernel_le_base rho phi)) i).range := by
    rw [normal_coordinate_range_eq_local_kernel rho phi hrho htop hfull hmin M hM hME i]
    exact n.property
  obtain ⟨m, hm⟩ := hn
  refine ⟨⟨⟨m.val, hME m.property⟩, m.property⟩, ?_⟩
  apply Subtype.ext
  change (rho m.val).left i = n.val
  exact hm

/-- The genuine nonabelian local-chief image is either zero or a minimal
normal subgroup of the original group. No ordinary generation is used. -/
theorem minimalNormal_kernel
    (hrho : Function.Injective rho) (htop : Function.Surjective (rightHom.comp rho))
    (hfull : Compression.FullComponent rho) (hmin : IsMinimalNormalSubgroup phi.ker)
    (hnc : ¬ IsMulCommutative phi.ker) (hE : Compression.kernel rho phi ≠ ⊥) :
    IsMinimalNormalSubgroup (Compression.kernel rho phi) := by
  classical
  have hlocal (L : Subgroup D) (hL : L.Normal) (hle : L ≤ phi.ker) :
      L = ⊥ ∨ L = phi.ker := by
    by_cases hz : L = ⊥
    · exact Or.inl hz
    · exact Or.inr (hmin.2.2 L hL hz hle)
  let C := semisimpleNormalChart_of_nonabelian_minimal phi.ker hlocal hnc
  let f (j : I × C.ι) : Compression.kernel rho phi →* C.factor j.2 :=
    (Pi.evalMonoidHom C.factor j.2).comp
      (C.equiv.toMonoidHom.comp (Compression.kernelCoordinate rho phi j.1))
  letI (j : I × C.ι) : IsSimpleGroup (C.factor j.2) := C.simple j.2
  have hjoint : Function.Injective (fun g j => f j g) := by
    intro a b hab
    apply Compression.kernelCoordinate_joint_injective rho phi hrho
    funext i
    apply C.equiv.injective
    funext j
    exact congrFun hab (i,j)
  refine ⟨inferInstance, hE, ?_⟩
  intro M hnormal hM hME
  letI : M.Normal := hnormal
  have hs (j : I × C.ι) : Function.Surjective
      ((f j).comp (M.subgroupOf (Compression.kernel rho phi)).subtype) := by
    have heval : Function.Surjective (Pi.evalMonoidHom C.factor j.2) := by
      intro x
      exact ⟨Pi.mulSingle j.2 x, Pi.mulSingle_eq_same j.2 x⟩
    exact heval.comp (C.equiv.surjective.comp
      (kernelCoordinate_restriction_surjective rho phi hrho htop hfull hmin M hM hME j.1))
  have htopM := SemisimpleNormalSubdirectRigidity.normal_subdirect_eq_top
    (fun j : I × C.ι => C.factor j.2) (fun j => C.centerless j.2) f hjoint
    (M.subgroupOf (Compression.kernel rho phi)) hs
  exact le_antisymm hME (Subgroup.subgroupOf_eq_top.mp htopM)

/-- Safe ordinary extension across this actual minimal normal kernel.
The factor's ORDINARY rank remains genuine and is not replaced by one. -/
theorem genRank_le_internal_factor
    (hrho : Function.Injective rho) (htop : Function.Surjective (rightHom.comp rho))
    (hfull : Compression.FullComponent rho) (hmin : IsMinimalNormalSubgroup phi.ker)
    (hnc : ¬ IsMulCommutative phi.ker) (hE : Compression.kernel rho phi ≠ ⊥)
    (A : Subgroup (Compression.kernel rho phi)) [A.Normal] (hA : A ≠ ⊥) :
    MarkedC4.genRank G ≤ MarkedC4.genRank A +
      MarkedC4.genRank (G ⧸ Compression.kernel rho phi) :=
  MinimalNormalInternalFactorOrdinaryGenerators.genRank_le (Compression.kernel rho phi) A
    (minimalNormal_kernel rho phi hrho htop hfull hmin hnc hE) hA

end SymmetricSubgroupAsymptotics.WreathNonabelianChiefOrdinaryStep
