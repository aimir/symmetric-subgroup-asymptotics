import SymmetricSubgroupAsymptotics.PermutationBinaryHead
import SymmetricSubgroupAsymptotics.BinaryPairKernelHead

/-! Every original normal subgroup lying inside an actual pair kernel
has its own faithful flip subspace. Its complete original-conjugation
character space is transported exactly before the Boolean-width bound
is applied. No monotonicity of subgroup heads or enlargement to the full
flip kernel is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X I : Type} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U I) [MulAction U I]
    (hact : ∀ (u : U) (i : I), u • i=F.top u i)
    (N : Subgroup U) [N.Normal] (hN : N≤F.top.ker)

/-- The original subgroup inclusion followed by the actual faithful flip map. -/
def normalBitsHom : N →* Multiplicative (I → ZMod 2) :=
  F.bitsHom.comp (Subgroup.inclusion hN)

theorem normalBitsHom_injective : Function.Injective (F.normalBitsHom N hN) := by
  intro a b hab
  exact (Subgroup.inclusion_injective hN) (F.bitsHom_injective hab)

/-- The exact correlated image of N, not the full kernel image. -/
def normalKernelSpace : Submodule (ZMod 2) (I → ZMod 2) :=
  (AddMonoidHom.toMultiplicativeRight.symm (F.normalBitsHom N hN)).range.toZModSubmodule 2

def normalKernelSpaceHom : N →* Multiplicative (F.normalKernelSpace N hN) where
  toFun n := Multiplicative.ofAdd
    ⟨F.bits (Subgroup.inclusion hN n),⟨Additive.ofMul n,rfl⟩⟩
  map_one' := by
    apply congrArg Multiplicative.ofAdd
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd (F.normalBitsHom N hN).map_one
  map_mul' a b := by
    apply congrArg Multiplicative.ofAdd
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd ((F.normalBitsHom N hN).map_mul a b)

theorem normalKernelSpaceHom_bijective : Function.Bijective (F.normalKernelSpaceHom N hN) := by
  constructor
  · intro a b hab
    apply F.normalBitsHom_injective N hN
    exact congrArg (fun z : Multiplicative (F.normalKernelSpace N hN) =>
      Multiplicative.ofAdd z.toAdd.val) hab
  · intro x
    obtain ⟨n,hn⟩ := x.toAdd.property
    refine ⟨n.toMul,?_⟩
    apply congrArg Multiplicative.ofAdd
    exact Subtype.ext hn

/-- Reversible original group-to-module chart. -/
def normalKernelChart : N ≃* Multiplicative (F.normalKernelSpace N hN) :=
  MulEquiv.ofBijective (F.normalKernelSpaceHom N hN)
    (F.normalKernelSpaceHom_bijective N hN)

include hact in
theorem normalCoordinateAction_bits (u : U) (n : N) :
    permutationFunctionRepresentation (ZMod 2) U I u (F.bits (Subgroup.inclusion hN n))=
      F.bits (Subgroup.inclusion hN (MulAut.conjNormal u n)) := by
  rw [F.originalCoordinateAction_bits hact]
  rfl

/-- Stability uses conjugation by all of the original ambient U. -/
def normalKernelOriginalSubrepresentation :
    Subrepresentation (permutationFunctionRepresentation (ZMod 2) U I) where
  toSubmodule := F.normalKernelSpace N hN
  apply_mem_toSubmodule u v hv := by
    obtain ⟨n,rfl⟩ := hv
    change permutationFunctionRepresentation (ZMod 2) U I u
      (F.bits (Subgroup.inclusion hN n.toMul))∈F.normalKernelSpace N hN
    rw [F.normalCoordinateAction_bits hact N hN]
    exact ⟨Additive.ofMul (MulAut.conjNormal u n.toMul),rfl⟩

/-- The entire intrinsic invariant-character space is identified with
that of the same original subgroup under the same ambient conjugations. -/
def normalKernelOriginalCharactersEquiv :
    primeActionCharacters 2
      (representationGroupAction (F.normalKernelOriginalSubrepresentation hact N hN).toRepresentation)
      ≃ₗ[ZMod 2] primeRelativeCharacters 2 N :=
  (primeActionCharacterCongr 2 (F.normalKernelChart N hN)
    (normalChainSourceAction N)
    (representationGroupAction (F.normalKernelOriginalSubrepresentation hact N hN).toRepresentation)
    (by
      intro u n
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      change F.bits (Subgroup.inclusion hN (MulAut.conjNormal u n))=
        permutationFunctionRepresentation (ZMod 2) U I u
          (F.bits (Subgroup.inclusion hN n))
      exact (F.normalCoordinateAction_bits hact N hN u n).symm)).trans
    (normalChainSourceCharactersEquiv N 2)

include hact hN in
/-- The actual subgroup N can be any original normal inside the pair
kernel. The width is determined by the original transitive pair action. -/
theorem normal_kernel_relativeHead_le_width [Finite X] [Finite I]
    [MulAction.IsPretransitive U I] (hU : IsPGroup 2 U)
    (t : ℕ) (hcard : Nat.card I=2^t) (i : I) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 N)≤t.choose (t/2) := by
  rw [← (F.normalKernelOriginalCharactersEquiv hact N hN).finrank_eq]
  exact twoGroup_permutationSubrepresentationCharacterHead_le_width hU t hcard i
    (F.normalKernelOriginalSubrepresentation hact N hN)

include hact in
/-- In particular the exact intersection with an arbitrary original
normal is covered, retaining its own head rather than the full kernel's. -/
theorem intersection_kernel_relativeHead_le_width [Finite X] [Finite I]
    [MulAction.IsPretransitive U I] (hU : IsPGroup 2 U)
    (t : ℕ) (hcard : Nat.card I=2^t) (i : I) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 (N⊓F.top.ker))≤
      t.choose (t/2) :=
  F.normal_kernel_relativeHead_le_width hact (N⊓F.top.ker) inf_le_right hU t hcard i

end SymmetricSubgroupAsymptotics.BinaryPairFrame
