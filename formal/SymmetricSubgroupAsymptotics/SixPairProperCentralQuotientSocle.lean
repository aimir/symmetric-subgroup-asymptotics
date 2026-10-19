import SymmetricSubgroupAsymptotics.SixPairFullKernelCentralizerTop
import SymmetricSubgroupAsymptotics.SixPairProperCentralQuotientCentralizer
import SymmetricSubgroupAsymptotics.ClassTwoNormalSocleCentralization

/-! The whole socle of a proper original central quotient lies in the
image of the SAME original kernel center. Actual class-two commutators,
physical head faithfulness, and single-indicator normal closure supply
all three steps; no normal list or quotient census enters the proof. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SixPairProperCentralQuotientSocle
open SixPairFullKernelCenter

variable {X I : Type} {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U I)
  (E : ProductBlockFrame F.top.range (Fin 3) (ZMod 2))

private theorem quotient_class_two (N : Subgroup U) [N.Normal] :
    ⁅((SixPairNestedTopFrames.nestedFrame F E).top.ker.map (QuotientGroup.mk' N)),
      ((SixPairNestedTopFrames.nestedFrame F E).top.ker.map (QuotientGroup.mk' N))⁆≤
    Subgroup.centralizer
      (((SixPairNestedTopFrames.nestedFrame F E).top.ker.map (QuotientGroup.mk' N)) :
        Set (U ⧸ N)) := by
  let C := SixPairNestedTopFrames.nestedFrame F E
  let q := QuotientGroup.mk' N
  apply Subgroup.commutator_le.mpr
  rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩
  apply Subgroup.mem_centralizer_iff.mpr
  rintro _ ⟨c,hc,rfl⟩
  have hh := SixPairThreePairKernelClassTwo.commutator_central F E
    (⟨a,ha⟩ : C.top.ker) (⟨b,hb⟩ : C.top.ker) (⟨c,hc⟩ : C.top.ker)
  have hh' : (a*b*a⁻¹*b⁻¹)*c=c*(a*b*a⁻¹*b⁻¹) := congrArg Subtype.val hh
  have hq := congrArg q hh'.symm
  simpa only [map_mul,map_inv] using hq

/-- Full socle containment for every proper original central denominator. -/
theorem socle_le_center_image [MulAction.IsPretransitive U X]
    (hfull : SixPairIndependentKernelNormalCommutators.Independent F E)
    (N : Subgroup U) [N.Normal] (hN : N≤centerImage F E)
    (hproper : ¬centerImage F E≤N) :
    finiteGroupSocle (U ⧸ N)≤(centerImage F E).map (QuotientGroup.mk' N) := by
  let C := SixPairNestedTopFrames.nestedFrame F E
  let q := QuotientGroup.mk' N
  let L := C.top.ker.map q
  letI : L.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective N)
  have hs := finiteGroupSocle_le_centralizer_of_class_two_normal L (quotient_class_two F E N)
  intro z hz
  obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective N z
  have hcomm : ∀ k : C.top.ker,g*k.val*g⁻¹*k.val⁻¹∈N := by
    intro k
    have hk : q k.val∈L := ⟨k.val,k.property,rfl⟩
    have he := Subgroup.mem_centralizer_iff.mp (hs hz) (q k.val) hk
    apply (QuotientGroup.eq_one_iff (N := N) _).mp
    change q (g*k.val*g⁻¹*k.val⁻¹)=1
    rw [map_mul,map_mul,map_mul,map_inv,map_inv]
    have he' : q k.val*q g=q g*q k.val := he
    rw [←he']
    simp [mul_assoc]
  have hgK : g∈C.top.ker :=
    SixPairFullKernelCentralizerTop.mem_kernel_of_commutators_mem_center F E hfull g
      (fun k => hN (hcomm k))
  let x : C.top.ker := ⟨g,hgK⟩
  have hx : x∈Subgroup.center C.top.ker :=
    SixPairProperCentralQuotientCentralizer.central_of_commutators_mem F E hfull N
      hproper x (fun k => hcomm k)
  exact ⟨g,(mem_centerImage F E x).mpr hx,rfl⟩

end SymmetricSubgroupAsymptotics.SixPairProperCentralQuotientSocle
