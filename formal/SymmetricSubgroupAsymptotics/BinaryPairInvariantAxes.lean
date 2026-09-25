import SymmetricSubgroupAsymptotics.BinaryPairFrameEquivariance
import SymmetricSubgroupAsymptotics.BinaryCoordinateSpaces
import SymmetricSubgroupAsymptotics.BinaryKernelNormalRegistry

/-! Every literal original normal supplies a compatible joint signature
in the independently enumerated coordinate-axis and top-normal registries.
The correlated kernel and original normal are recovered by the same
faithful chart; no action of U/(K∨N) on literal K is introduced. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X : Type*} {w : ℕ} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin w))

def coordinateTopAction : Representation (ZMod 2) F.top.range (Fin w → ZMod 2) :=
  (binaryPermutationRepresentation w).comp F.top.range.subtype

/-- The actual ambient coordinate image of the original intersection. -/
def ambientAxis (N : Subgroup U) : Submodule (ZMod 2) (Fin w → ZMod 2) :=
  ((AddMonoidHom.toMultiplicativeRight.symm F.bitsHom).comp
    (N.subgroupOf F.top.ker).subtype.toAdditive).range.toZModSubmodule 2

theorem mem_ambientAxis (N : Subgroup U) (v : Fin w → ZMod 2) :
    v∈F.ambientAxis N ↔ ∃ k : F.top.ker, (k:U)∈N ∧ F.bits k=v := by
  constructor
  · rintro ⟨k,hk⟩
    exact ⟨k.toMul.val,k.toMul.property,hk⟩
  · rintro ⟨k,hk,rfl⟩
    exact ⟨Additive.ofMul (⟨k,hk⟩ : N.subgroupOf F.top.ker),rfl⟩

theorem bits_mem_ambientAxis (N : Subgroup U) (k : F.top.ker) :
    F.bits k∈F.ambientAxis N ↔ (k:U)∈N := by
  rw [F.mem_ambientAxis]
  constructor
  · rintro ⟨l,hl,he⟩
    have hlk : l=k := F.bitsHom_injective (congrArg Multiplicative.ofAdd he)
    exact hlk ▸ hl
  · intro hk
    exact ⟨k,hk,rfl⟩

theorem ambientAxis_le_kernelSpace (N : Subgroup U) :
    F.ambientAxis N≤F.kernelSpace := by
  intro v hv
  obtain ⟨k,hk,rfl⟩ := (F.mem_ambientAxis N v).mp hv
  exact ⟨Additive.ofMul k,rfl⟩

theorem coordinateTopAction_bits (u : U) (k : F.top.ker) :
    F.coordinateTopAction (F.top.rangeRestrict u) (F.bits k)=
      F.bits (MulAut.conjNormal u k) := by
  funext i
  exact (F.bits_conjNormal u k i).symm

def kernelSubrepresentation : Subrepresentation F.coordinateTopAction where
  toSubmodule := F.kernelSpace
  apply_mem_toSubmodule t v hv := by
    obtain ⟨u,rfl⟩ := F.top.rangeRestrict_surjective t
    obtain ⟨k,rfl⟩ := hv
    change F.coordinateTopAction (F.top.rangeRestrict u) (F.bits k.toMul)∈F.kernelSpace
    rw [F.coordinateTopAction_bits]
    exact ⟨Additive.ofMul (MulAut.conjNormal u k.toMul),rfl⟩

/-- Original normality makes the retained axis invariant under the actual
Top=U/K action. It does not require a quotient action on K by U/(K∨N). -/
def axisSubrepresentation (N : Subgroup U) [N.Normal] :
    Subrepresentation F.coordinateTopAction where
  toSubmodule := F.ambientAxis N
  apply_mem_toSubmodule t v hv := by
    obtain ⟨u,rfl⟩ := F.top.rangeRestrict_surjective t
    obtain ⟨k,hk,rfl⟩ := (F.mem_ambientAxis N v).mp hv
    rw [F.coordinateTopAction_bits,F.bits_mem_ambientAxis]
    exact Subgroup.Normal.conj_mem (H := N) inferInstance _ hk u

/-- Every original normal gives the actual compatibility condition on its
joint axis/top signature. This also covers nonsplit, nonabelian lifts. -/
theorem original_normal_compatible (N : Subgroup U) [N.Normal]
    (t : F.top.range) (ht : t∈N.map F.top.rangeRestrict)
    (v : Fin w → ZMod 2) (hv : v∈F.kernelSpace) :
    F.coordinateTopAction t v-v ∈ F.ambientAxis N := by
  obtain ⟨u,hu,rfl⟩ := ht
  obtain ⟨k,rfl⟩ := hv
  let x : F.top.ker := k.toMul
  let c : F.top.ker := x⁻¹*MulAut.conjNormal u x
  have hc : (c:U)∈N := by
    have hconj := Subgroup.Normal.conj_mem (H := N) inferInstance u hu (x:U)⁻¹
    have h := N.mul_mem hconj (N.inv_mem hu)
    simpa only [c,MulAut.conjNormal_apply,Subgroup.coe_mul,Subgroup.coe_inv,
      inv_inv,mul_assoc] using h
  have he : F.bits c=F.coordinateTopAction (F.top.rangeRestrict u) (F.bits x)-F.bits x := by
    rw [F.coordinateTopAction_bits]
    have hmul := congrArg Multiplicative.toAdd (F.bitsHom.map_mul x⁻¹ (MulAut.conjNormal u x))
    have hinv := congrArg Multiplicative.toAdd (F.bitsHom.map_inv x)
    change F.bits c=F.bits x⁻¹+F.bits (MulAut.conjNormal u x) at hmul
    change F.bits x⁻¹= -F.bits x at hinv
    rw [hmul,hinv,sub_eq_add_neg,add_comm]
  change F.coordinateTopAction (F.top.rangeRestrict u) (F.bits x)-F.bits x∈F.ambientAxis N
  rw [← he]
  exact (F.bits_mem_ambientAxis N c).mpr hc

/-- The same faithful chart recovers the literal intersection; equal
coordinate axes cannot hide a different original kernel subgroup. -/
theorem ambientAxis_eq_iff (N M : Subgroup U) :
    F.ambientAxis N=F.ambientAxis M ↔ F.top.ker⊓N=F.top.ker⊓M := by
  constructor
  · intro h
    ext x
    constructor
    · rintro ⟨hx,hN⟩
      have hm := (F.bits_mem_ambientAxis N (⟨x,hx⟩ : F.top.ker)).mpr hN
      rw [h] at hm
      exact ⟨hx,(F.bits_mem_ambientAxis M (⟨x,hx⟩ : F.top.ker)).mp hm⟩
    · rintro ⟨hx,hM⟩
      have hm := (F.bits_mem_ambientAxis M (⟨x,hx⟩ : F.top.ker)).mpr hM
      rw [← h] at hm
      exact ⟨hx,(F.bits_mem_ambientAxis N (⟨x,hx⟩ : F.top.ker)).mp hm⟩
  · intro h
    ext v
    rw [F.mem_ambientAxis,F.mem_ambientAxis]
    apply exists_congr
    intro k
    apply and_congr_left
    intro _
    have he : ((k:U)∈F.top.ker⊓N) ↔ ((k:U)∈F.top.ker⊓M) := by rw [h]
    simpa only [Subgroup.mem_inf,k.property,true_and] using he

/-- The bad signatures with trivial top image have one literal normal:
their retained original kernel axis itself. -/
theorem normal_eq_of_trivial_top_and_axis (N A : Subgroup U)
    (hT : N.map F.top.rangeRestrict=⊥) (hA : A≤F.top.ker)
    (haxis : F.ambientAxis N=F.ambientAxis A) : N=A := by
  have hN : F.top.ker⊓N=N := by
    simpa only [MonoidHom.ker_rangeRestrict] using
      binary_normal_eq_intersection_of_top_trivial F.top.rangeRestrict N hT
  have h := (F.ambientAxis_eq_iff N A).mp haxis
  rw [hN,inf_eq_right.mpr hA] at h
  exact h

end SymmetricSubgroupAsymptotics.BinaryPairFrame
