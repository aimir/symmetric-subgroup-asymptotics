import SymmetricSubgroupAsymptotics.BinaryPairInvariantAxes
import SymmetricSubgroupAsymptotics.BinaryCoordinateCuts
import SymmetricSubgroupAsymptotics.BinaryPairJointSignatures
import Mathlib.FieldTheory.Finiteness

/-! Checked coordinate cuts are transported to literal original subgroups
through the reversible physical flip chart. Their cardinalities and full
fixed preimages retain the original source and all flip correlations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X : Type} {w : ℕ} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin w))

def coordinateKernelSubgroup (W : Submodule (ZMod 2) (Fin w → ZMod 2)) :
    Subgroup F.top.ker := W.toAddSubgroup.toSubgroup.comap F.bitsHom

def coordinateSubgroup (W : Submodule (ZMod 2) (Fin w → ZMod 2)) : Subgroup U :=
  (F.coordinateKernelSubgroup W).map F.top.ker.subtype

theorem mem_coordinateSubgroup (W : Submodule (ZMod 2) (Fin w → ZMod 2)) (x : U) :
    x∈F.coordinateSubgroup W ↔ ∃ k : F.top.ker, F.bits k∈W ∧ (k:U)=x := Iff.rfl

theorem coordinateSubgroup_le_kernel (W : Submodule (ZMod 2) (Fin w → ZMod 2)) :
    F.coordinateSubgroup W≤F.top.ker := by
  rintro x ⟨k,hk,rfl⟩
  exact k.property

theorem kernel_mem_coordinateSubgroup (W : Submodule (ZMod 2) (Fin w → ZMod 2))
    (k : F.top.ker) : (k:U)∈F.coordinateSubgroup W ↔ F.bits k∈W := by
  rw [F.mem_coordinateSubgroup]
  constructor
  · rintro ⟨l,hl,he⟩
    exact (Subtype.ext he : l=k) ▸ hl
  · exact fun hk => ⟨k,hk,rfl⟩

theorem coordinateSubgroup_mono {A C : Submodule (ZMod 2) (Fin w → ZMod 2)}
    (h : A≤C) : F.coordinateSubgroup A≤F.coordinateSubgroup C := by
  rintro x ⟨k,hk,rfl⟩
  exact ⟨k,h hk,rfl⟩

instance coordinateSubgroup_normal (C : Subrepresentation F.coordinateTopAction) :
    (F.coordinateSubgroup C.toSubmodule).Normal where
  conj_mem x hx u := by
    obtain ⟨k,hk,rfl⟩ := (F.mem_coordinateSubgroup C.toSubmodule x).mp hx
    refine ⟨MulAut.conjNormal u k,?_,rfl⟩
    change F.bits (MulAut.conjNormal u k)∈C.toSubmodule
    rw [← F.coordinateTopAction_bits]
    exact C.apply_mem_toSubmodule _ hk

def coordinateKernelHom (W : Submodule (ZMod 2) (Fin w → ZMod 2)) :
    F.coordinateKernelSubgroup W →* Multiplicative W where
  toFun k := Multiplicative.ofAdd ⟨F.bits k.val,k.property⟩
  map_one' := by
    apply congrArg Multiplicative.ofAdd
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd F.bitsHom.map_one
  map_mul' k l := by
    apply congrArg Multiplicative.ofAdd
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd (F.bitsHom.map_mul k.val l.val)

theorem coordinateKernelHom_bijective (W : Submodule (ZMod 2) (Fin w → ZMod 2))
    (hW : W≤F.kernelSpace) : Function.Bijective (F.coordinateKernelHom W) := by
  constructor
  · intro k l h
    apply Subtype.ext
    apply F.bitsHom_injective
    exact congrArg (fun z : Multiplicative W => Multiplicative.ofAdd z.toAdd.val) h
  · intro v
    obtain ⟨k,hk⟩ := hW v.toAdd.property
    change F.bits k.toMul=v.toAdd.val at hk
    refine ⟨⟨k.toMul,?_⟩,?_⟩
    · change F.bits k.toMul∈W
      exact hk.symm ▸ v.toAdd.property
    · apply congrArg Multiplicative.ofAdd
      exact Subtype.ext hk

/-- A subspace inside the actual correlated kernel has exactly the same
cardinality as its literal original preimage. -/
theorem coordinateSubgroup_card (W : Submodule (ZMod 2) (Fin w → ZMod 2))
    (hW : W≤F.kernelSpace) : Nat.card (F.coordinateSubgroup W)=Nat.card W := by
  have e := (F.coordinateKernelSubgroup W).equivMapOfInjective
    F.top.ker.subtype Subtype.val_injective
  change Nat.card ((F.coordinateKernelSubgroup W).map F.top.ker.subtype)=Nat.card W
  rw [← Nat.card_congr e.toEquiv]
  have f := MulEquiv.ofBijective (F.coordinateKernelHom W) (F.coordinateKernelHom_bijective W hW)
  exact (Nat.card_congr f.toEquiv).trans (Nat.card_congr Multiplicative.toAdd)

theorem coordinateSubgroup_ambientAxis (N : Subgroup U) :
    F.coordinateSubgroup (F.ambientAxis N)=F.top.ker⊓N := by
  ext x
  constructor
  · rintro ⟨k,hk,rfl⟩
    exact ⟨k.property,(F.bits_mem_ambientAxis N k).mp hk⟩
  · rintro ⟨hx,hn⟩
    exact ⟨⟨x,hx⟩,(F.bits_mem_ambientAxis N (⟨x,hx⟩:F.top.ker)).mpr hn,rfl⟩

/-- The actual commutator coordinate is the displacement under the
retained top action; this identity keeps its original source element. -/
theorem bits_commutator (u : U) (k : F.top.ker) :
    F.bits (k⁻¹*MulAut.conjNormal u k)=
      F.coordinateTopAction (F.top.rangeRestrict u) (F.bits k)-F.bits k := by
  rw [F.coordinateTopAction_bits]
  have hmul := congrArg Multiplicative.toAdd (F.bitsHom.map_mul k⁻¹ (MulAut.conjNormal u k))
  have hinv := congrArg Multiplicative.toAdd (F.bitsHom.map_inv k)
  change F.bits (k⁻¹*MulAut.conjNormal u k)=F.bits k⁻¹+F.bits (MulAut.conjNormal u k) at hmul
  change F.bits k⁻¹= -F.bits k at hinv
  rw [hmul,hinv,sub_eq_add_neg,add_comm]

end SymmetricSubgroupAsymptotics.BinaryPairFrame
