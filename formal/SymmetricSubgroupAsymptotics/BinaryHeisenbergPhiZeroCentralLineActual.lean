import SymmetricSubgroupAsymptotics.BinaryHeisenbergPhiZeroCentralLineCapacity
import SymmetricSubgroupAsymptotics.BinaryHeisenbergCanonicalCarryTop
import SymmetricSubgroupAsymptotics.BinaryPairCoordinateCentralCapacity
import SymmetricSubgroupAsymptotics.BinaryPairAxisNaturalModule
import SymmetricSubgroupAsymptotics.BinaryPairLargeKernelCenter
import SymmetricSubgroupAsymptotics.NormalOrderTwo

/-! The scalar Heisenberg constant-line certificate applies to the SAME
original denominator and kernel. Only the inner zero model is used to
identify original generators; every outer lift offset is retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryHeisenbergPhiZeroCentralLineActual
local instance heisenbergPhiZeroCentralLineActualPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
open BinaryHeisenbergPhiZeroCentralLineCapacity
private abbrev Allowed := {i : Fin 4 // ∀ j : Fin 10,
  candidateAction i (K.inclusion (Pi.single j 1))-K.inclusion (Pi.single j 1)∈line.space}

private theorem canonical_closure
    {H : Subgroup (Equiv.Perm (Fin 16))} (E : BinaryPairFrame H (Fin 8))
    (hzero : H=E.splitAffineAction)
    (hH : E.top.range=Subgroup.closure (Set.range BinaryMenuCayley8T22.generators))
    (hK : E.kernelSpace=BinaryHeisenbergSixCanonicalGenerators.K.space) :
    H.map E.canonicalPointLabels.permCongrHom=Subgroup.closure (Set.range generators) := by
  have h := BinaryHeisenbergSixCanonicalGenerators.BinaryPairFrame.canonical_heisenberg_six_closure
    E hzero hH hK
  rw [BinaryHeisenbergCanonicalCarryTop.generators_eq] at h
  exact h

theorem original_central_capacity_le
    {H : Subgroup (Equiv.Perm (Fin 16))} (E : BinaryPairFrame H (Fin 8))
    (hzero : H=E.splitAffineAction)
    (hH : E.top.range=Subgroup.closure (Set.range BinaryMenuCayley8T22.generators))
    (hK : E.kernelSpace=BinaryHeisenbergSixCanonicalGenerators.K.space) :
    binaryCentralJointDisplacementCapacity E.originalCoordinateRepresentation K.space line.space≤8 := by
  let c := E.canonicalPointLabels.permCongrHom
  have hc := canonical_closure E hzero hH hK
  have hrows (i : Fin 6) : ∃ u : H,c u.val=generators i := by
    have hm : generators i∈H.map c := by
      rw [hc]
      exact Subgroup.subset_closure ⟨i,rfl⟩
    obtain ⟨u,hu,hui⟩ := hm
    exact ⟨⟨u,hu⟩,hui⟩
  choose u hu using hrows
  have hact (i : Fin 6) : E.originalCoordinateRepresentation (u i)=action i := by
    rw [E.originalCoordinateRepresentation_canonical,hu]
    rfl
  let f : binaryFixedDisplacements E.originalCoordinateRepresentation K.space line.space →
      binaryCoordinateFixedDisplacements K action line.space := fun v =>
    ⟨v.val,v.property.1,fun i => by rw [←hact];exact v.property.2 (u i)⟩
  have hf : Function.Injective f := by
    intro v z he
    exact Subtype.ext (congrArg
      (fun x : binaryCoordinateFixedDisplacements K action line.space => x.val) he)
  have hfixed : Nat.card (binaryFixedDisplacements E.originalCoordinateRepresentation K.space line.space)≤8 :=
    (Nat.card_le_card_of_injective f hf).trans fixed_card_le
  have hchoose (g : binaryCentralTrivialDisplacements E.originalCoordinateRepresentation K.space line.space) :
      ∃ i : Fin 4,c g.val.val=candidate i := by
    apply centralizer_cases
    intro i
    have he := congrArg (fun z : H => z.val)
      ((Subgroup.mem_center_iff.mp g.property.1 (u i)).symm)
    change g.val.val*(u i).val=(u i).val*g.val.val at he
    have hh := congrArg c he
    change c g.val.val*generators i=generators i*c g.val.val
    rw [←hu]
    simpa only [map_mul] using hh
  choose index hindex using hchoose
  let t : binaryCentralTrivialDisplacements E.originalCoordinateRepresentation K.space line.space → Allowed := fun g =>
    ⟨index g,by
      intro j
      have he : E.originalCoordinateRepresentation g.val=candidateAction (index g) := by
        rw [E.originalCoordinateRepresentation_canonical,hindex]
        rfl
      rw [←he]
      exact g.property.2 _ ⟨Pi.single j 1,rfl⟩⟩
  have ht : Function.Injective t := by
    intro g z he
    apply Subtype.ext
    apply Subtype.ext
    apply E.canonicalPointLabels.permCongrHom.injective
    have hi : index g=index z := congrArg (fun x : Allowed => x.val) he
    exact (hindex g).trans ((congrArg candidate hi).trans (hindex z).symm)
  have htop : Nat.card (binaryCentralTrivialDisplacements E.originalCoordinateRepresentation K.space line.space)≤1 :=
    (Nat.card_le_card_of_injective t ht).trans allowed_card_le
  exact (Nat.mul_le_mul hfixed htop).trans (by decide)

private theorem canonical_constant_one_eq_line :
    binaryEightCanonicalLayerChange (fun _ : Fin 16 => (1 : ZMod 2))=
      line.inclusion (fun _ : Fin 1 => 1) := by decide +kernel

namespace BinaryPairFrame
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : SymmetricSubgroupAsymptotics.BinaryPairFrame U (Fin 16))
    (E : SymmetricSubgroupAsymptotics.BinaryPairFrame F.top.range (Fin 8))
include F E

theorem original_normal_center_capacity_le
    (hzero : F.top.range=E.splitAffineAction)
    (hH : E.top.range=Subgroup.closure (Set.range BinaryMenuCayley8T22.generators))
    (hK : E.kernelSpace=BinaryHeisenbergSixCanonicalGenerators.K.space)
    (hS : (E.originalCoordinateSubrepresentation (F.axisNaturalSubrepresentation F.top.ker)).toSubmodule=K.space)
    (N : Subgroup U) [N.Normal] (hN : N≤F.top.ker)
    (hA : (F.ambientAxis N).map E.originalCoordinateEquiv.toLinearMap≤line.space) :
    Nat.card N*Nat.card (Subgroup.center (U ⧸ N))≤8 := by
  have hwhole : F.ambientAxis F.top.ker=F.kernelSpace := by
    apply le_antisymm (F.ambientAxis_le_kernelSpace F.top.ker)
    rintro v ⟨a,rfl⟩
    exact (F.bits_mem_ambientAxis F.top.ker a.toMul).mpr a.toMul.property
  have hspace : F.kernelSpace.map E.originalCoordinateEquiv.toLinearMap=K.space := by
    change (F.ambientAxis F.top.ker).map E.originalCoordinateEquiv.toLinearMap=_ at hS
    rwa [hwhole] at hS
  exact (F.kernel_center_card_mul_le_original_coordinate_central_capacity E N hN K.space line.space hspace hA).trans
    (original_central_capacity_le E hzero hH hK)

/-- Central original denominators have literal constant bits after the SAME
inner point chart. No choice of an abstractly isomorphic denominator occurs. -/
theorem central_axis_le_line [MulAction.IsPretransitive U X]
    (N : Subgroup U) (hNc : N≤Subgroup.center U) :
    (F.ambientAxis N).map E.originalCoordinateEquiv.toLinearMap≤line.space := by
  letI : MulAction.IsPretransitive F.top.range (Fin 16) := F.top_pretransitive
  rintro v ⟨a,ha,rfl⟩
  obtain ⟨k,hk,rfl⟩ := (F.mem_ambientAxis N a).mp ha
  change E.originalCoordinateEquiv (F.bits k)∈line.space
  rw [E.originalCoordinateEquiv_canonicalPointLabels]
  let c := F.bits k 0
  have he : (fun j => F.bits k (E.canonicalPointLabels.symm j))=
      c • (fun _ : Fin 16 => (1 : ZMod 2)) := by
    funext j
    simpa only [Pi.smul_apply,smul_eq_mul,mul_one] using
      F.central_kernel_bits_constant k (hNc hk) (E.canonicalPointLabels.symm j) (0 : Fin 16)
  rw [he,map_smul,canonical_constant_one_eq_line]
  exact line.space.smul_mem c ⟨_,rfl⟩

/-- In particular, the unique normal order-two denominator is handled
without a split hypothesis on the outer source. -/
theorem central_normal_quotient_center_capacity_le [MulAction.IsPretransitive U X]
    (hU : IsPGroup 2 U)
    (hzero : F.top.range=E.splitAffineAction)
    (hH : E.top.range=Subgroup.closure (Set.range BinaryMenuCayley8T22.generators))
    (hK : E.kernelSpace=BinaryHeisenbergSixCanonicalGenerators.K.space)
    (hS : (E.originalCoordinateSubrepresentation (F.axisNaturalSubrepresentation F.top.ker)).toSubmodule=K.space)
    (N : Subgroup U) [N.Normal] (hNc : N≤Subgroup.center U) :
    Nat.card N*Nat.card (Subgroup.center (U ⧸ N))≤8 := by
  have hwhole : F.ambientAxis F.top.ker=F.kernelSpace := by
    apply le_antisymm (F.ambientAxis_le_kernelSpace F.top.ker)
    rintro v ⟨a,rfl⟩
    exact (F.bits_mem_ambientAxis F.top.ker a.toMul).mpr a.toMul.property
  have hspace : F.kernelSpace.map E.originalCoordinateEquiv.toLinearMap=K.space := by
    change (F.ambientAxis F.top.ker).map E.originalCoordinateEquiv.toLinearMap=_ at hS
    rwa [hwhole] at hS
  have hd := E.originalCoordinateEquiv.finrank_map_eq F.kernelSpace
  rw [hspace,K.finrank] at hd
  have hc : Subgroup.center U≤F.top.ker := by
    apply F.original_center_le_kernel_of_half_lt hU (0 : Fin 16)
    omega
  exact original_normal_center_capacity_le F E hzero hH hK hS N (hNc.trans hc)
    (central_axis_le_line F E N hNc)

/-- Every original normal order-two denominator has centre at most four.
The centrality premise is proved from its actual order and normality. -/
theorem normal_order_two_quotient_center_card_le_four [MulAction.IsPretransitive U X]
    (hU : IsPGroup 2 U)
    (hzero : F.top.range=E.splitAffineAction)
    (hH : E.top.range=Subgroup.closure (Set.range BinaryMenuCayley8T22.generators))
    (hK : E.kernelSpace=BinaryHeisenbergSixCanonicalGenerators.K.space)
    (hS : (E.originalCoordinateSubrepresentation (F.axisNaturalSubrepresentation F.top.ker)).toSubmodule=K.space)
    (N : Subgroup U) [N.Normal] (hcard : Nat.card N=2) :
    Nat.card (Subgroup.center (U ⧸ N))≤4 := by
  have h := central_normal_quotient_center_capacity_le F E hU hzero hH hK hS N
    (NormalOrderTwo.le_center N hcard)
  rw [hcard] at h
  omega

end BinaryPairFrame
end SymmetricSubgroupAsymptotics.BinaryHeisenbergPhiZeroCentralLineActual
