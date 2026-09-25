import SymmetricSubgroupAsymptotics.PrimeAbelianization
import SymmetricSubgroupAsymptotics.FinitePermutationEncoding
import SymmetricSubgroupAsymptotics.FiniteCayleyGroup
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases

/-!
# Binary modules from literal physical pair frames

A frame is a bijection onto the original permutation points. Its actual
pair action identifies the literal kernel with its binary flip subspace.
No abstractly isomorphic action or enlarged product replaces the source.
-/

set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

/-- A two-point injective action is a translation in its binary coordinate. -/
theorem binary_injective_translate (f : ZMod 2 → ZMod 2)
    (hf : Function.Injective f) (b : ZMod 2) : f b=b+f 0 := by
  have h : ∀ f : ZMod 2 → ZMod 2, Function.Injective f →
      ∀ b : ZMod 2, f b=b+f 0 := by decide +kernel
  exact h f hf b

structure BinaryPairFrame {X : Type*} (U : Subgroup (Equiv.Perm X)) (I : Type*) where
  frame : I × ZMod 2 ≃ X
  top : U →* Equiv.Perm I
  intertwine : ∀ (u : U) (p : I × ZMod 2), (frame.symm ((u : Equiv.Perm X) (frame p))).1=top u p.1

namespace BinaryPairFrame

/-- A checked faithful row action installs the frame on the original
literal permutation subgroup. -/
def ofEquiv {X I H : Type*} [Group H] {U : Subgroup (Equiv.Perm X)}
    (e : H ≃* U) (top : H →* Equiv.Perm I) (frame : I × ZMod 2 ≃ X)
    (h : ∀ u p, (frame.symm ((e u : Equiv.Perm X) (frame p))).1=top u p.1) :
    BinaryPairFrame U I where
  frame := frame
  top := top.comp e.symm.toMonoidHom
  intertwine u p := by
    obtain ⟨v,rfl⟩ := e.surjective u
    simpa only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply] using h v p

variable {X I : Type*} {U : Subgroup (Equiv.Perm X)} (F : BinaryPairFrame U I)

/-- The actual translation of the original kernel element on each pair. -/
def bits (k : F.top.ker) (i : I) : ZMod 2 :=
  (F.frame.symm (((k : U) : Equiv.Perm X) (F.frame (i,0)))).2

theorem kernel_first (k : F.top.ker) (i : I) (b : ZMod 2) :
    (F.frame.symm (((k : U) : Equiv.Perm X) (F.frame (i,b)))).1=i := by
  rw [F.intertwine]
  have hk : F.top (k : U)=1 := k.property
  rw [hk]
  rfl

/-- Every point of the physical pair is recovered from its retained bit. -/
theorem kernel_action (k : F.top.ker) (i : I) (b : ZMod 2) :
    F.frame.symm (((k : U) : Equiv.Perm X) (F.frame (i,b)))=(i,b+F.bits k i) := by
  apply Prod.ext
  · exact F.kernel_first k i b
  · change _=b+(F.frame.symm (((k : U) : Equiv.Perm X) (F.frame (i,0)))).2
    apply binary_injective_translate (fun t => (F.frame.symm (((k : U) : Equiv.Perm X) (F.frame (i,t)))).2)
    intro a b hab
    have he : F.frame.symm (((k : U) : Equiv.Perm X) (F.frame (i,a)))=
        F.frame.symm (((k : U) : Equiv.Perm X) (F.frame (i,b))) :=
      Prod.ext ((F.kernel_first k i a).trans (F.kernel_first k i b).symm) hab
    exact congrArg Prod.snd (F.frame.injective
      (((k : U) : Equiv.Perm X).injective (F.frame.symm.injective he)))

/-- Literal kernel elements act as the certified translations. -/
theorem kernel_action_frame (k : F.top.ker) (i : I) (b : ZMod 2) :
    ((k : U) : Equiv.Perm X) (F.frame (i,b))=F.frame (i,b+F.bits k i) :=
  F.frame.symm.injective ((F.kernel_action k i b).trans (F.frame.symm_apply_apply _).symm)

def bitsHom : F.top.ker →* Multiplicative (I → ZMod 2) where
  toFun k := Multiplicative.ofAdd (F.bits k)
  map_one' := by
    apply congrArg Multiplicative.ofAdd
    funext i
    change (F.frame.symm (F.frame (i,0))).2=0
    rw [F.frame.symm_apply_apply]
  map_mul' a b := by
    apply congrArg Multiplicative.ofAdd
    funext i
    change (F.frame.symm (((a : U) : Equiv.Perm X)
      (((b : U) : Equiv.Perm X) (F.frame (i,0))))).2=F.bits a i+F.bits b i
    rw [F.kernel_action_frame,F.kernel_action]
    simp only [zero_add,add_comm]

/-- The full original kernel, with every correlation among pair flips,
is retained. In particular it is not replaced by the ambient flip product. -/
theorem bitsHom_injective : Function.Injective F.bitsHom := by
  intro a b hab
  have hbits : F.bits a=F.bits b := congrArg Multiplicative.toAdd hab
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  intro x
  obtain ⟨⟨i,t⟩,rfl⟩ := F.frame.surjective x
  rw [F.kernel_action_frame,F.kernel_action_frame,hbits]

/-- The actual image, not the whole coordinate vector space. -/
def kernelSpace : Submodule (ZMod 2) (I → ZMod 2) :=
  (AddMonoidHom.toMultiplicativeRight.symm F.bitsHom).range.toZModSubmodule 2

def kernelSpaceHom : F.top.ker →* Multiplicative F.kernelSpace where
  toFun k := Multiplicative.ofAdd ⟨F.bits k,⟨Additive.ofMul k,rfl⟩⟩
  map_one' := by
    apply congrArg Multiplicative.ofAdd
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd F.bitsHom.map_one
  map_mul' a b := by
    apply congrArg Multiplicative.ofAdd
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd (F.bitsHom.map_mul a b)

theorem kernelSpaceHom_bijective : Function.Bijective F.kernelSpaceHom := by
  constructor
  · intro a b hab
    apply F.bitsHom_injective
    exact congrArg (fun z : Multiplicative F.kernelSpace =>
      Multiplicative.ofAdd z.toAdd.val) hab
  · intro x
    obtain ⟨a,ha⟩ := x.toAdd.property
    refine ⟨a.toMul,?_⟩
    apply congrArg Multiplicative.ofAdd
    exact Subtype.ext ha

/-- A reversible binary-module chart of the original physical kernel. -/
def kernelChart : F.top.ker ≃* Multiplicative F.kernelSpace :=
  MulEquiv.ofBijective F.kernelSpaceHom F.kernelSpaceHom_bijective

end BinaryPairFrame
/-- Source reflection recovers every original point image directly from
its retained compact code, without re-evaluating long generator words. -/
theorem binaryPair_source_row_apply {w n : ℕ} {ι : Type*}
    {generators : ι → Equiv.Perm (Fin w)}
    (C : EncodedCayleyCertificate (permutationGeneratorEncoding generators) n)
    (i : Fin n) (x : Fin w) :
    C.toCayley.elements i x=finFunctionFinEquiv.symm (C.rows i) x := by
  have h : permutationCode (C.toCayley.elements i)=C.rows i := C.encode_elements i
  rw [← h]
  exact (congrFun (finFunctionFinEquiv.symm_apply_apply
    (fun x => C.toCayley.elements i x)) x).symm

end SymmetricSubgroupAsymptotics
