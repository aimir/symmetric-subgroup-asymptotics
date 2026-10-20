import SymmetricSubgroupAsymptotics.ProductQuartetAffineLinearProjection
import SymmetricSubgroupAsymptotics.BinaryPlaneWreathActualOddKernel
import SymmetricSubgroupAsymptotics.TransitiveFourBinaryOrAlternating
import SymmetricSubgroupAsymptotics.ProductBlockFrameTransitiveTop

/-! With zero actual odd local kernel, a nonbinary transitive quartet
action has A4 in its actual coarse top. No assumption on local independence,
primitive components or a finite degree-sixteen locator is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ProductBlockFrame
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathActualOddKernel
open BinaryPlaneAlternatingKernelPartition (Frame)

variable {X : Type} [Finite X] {T : Subgroup (Equiv.Perm X)}
  (C : ProductBlockFrame T (Fin 4) Plane)

 theorem zero_odd_coarse_contains_alternating [MulAction.IsPretransitive T X]
    (hzero : oddKernel C.quartetLinearImage=⊥) (hT : ¬IsPGroup 2 T) :
    alternatingGroup (Fin 4)≤C.top.range := by
  have hnot : ¬IsPGroup 2 C.top.range := by
    intro hB
    let D := C.quartetLinearImage
    let sig := signProjection D
    let top : D →* Equiv.Perm (Fin 4) :=
      (PermutationalWreathProduct.rightHom : Frame →* Equiv.Perm (Fin 4)).comp D.subtype
    have hinj : Function.Injective sig := (MonoidHom.ker_eq_bot_iff sig).mp hzero
    have hD : IsPGroup 2 D := by
      intro d
      have htop : (d : Frame).right∈C.top.range := by
        obtain ⟨t,ht⟩ := d.property
        exact ⟨t,congrArg (fun z : Frame => z.right) ht⟩
      obtain ⟨n,hn⟩ := hB ⟨(d : Frame).right,htop⟩
      let a := sig (d^(2^n))
      have ha : a.right=1 := by
        change top (d^(2^n))=1
        rw [map_pow]
        exact congrArg Subtype.val hn
      have hform : SemidirectProduct.inl a.left=a := SemidirectProduct.ext rfl ha.symm
      have hleft : a.left^2=1 := by
        rw [pow_two]
        apply Multiplicative.toAdd.injective
        apply Subtype.ext
        funext i
        exact (by decide : ∀ z : ZMod 2,z+z=0) (a.left.toAdd.val i)
      have ha2 : a^2=1 := by
        rw [←hform,←map_pow,hleft,map_one]
      refine ⟨n+1,hinj ?_⟩
      calc
        sig (d^(2^(n+1)))=(sig (d^(2^n)))^2 := by rw [Nat.pow_succ,pow_mul,map_pow]
        _=1 := ha2
        _=sig 1 := sig.map_one.symm
    have hpre := (hD.to_subgroup (⊤ : Subgroup D)).comap_of_ker_isPGroup
      C.quartetLinearMap C.quartetLinearMap_kernel_binary
    apply hT
    intro t
    obtain ⟨n,hn⟩ := hpre ⟨t,by trivial⟩
    exact ⟨n,congrArg Subtype.val hn⟩
  have htrans := C.top_range_transitive (fun x y => MulAction.exists_smul_eq T x y)
  exact (TransitiveFourBinaryOrAlternating.binary_or_alternating C.top.range htrans).resolve_left hnot

end SymmetricSubgroupAsymptotics.ProductBlockFrame
