import SymmetricSubgroupAsymptotics.BinaryPairKernelHead

/-!
# Prime translation frames and the relative head of the block kernel

A prime translation frame identifies the points of an actual permutation
group `U` with `I × ZMod p`, so that `U` permutes the blocks `{i} × ZMod p`
through an actual top action and acts inside each block by a translation.
This is the general-prime form of the binary pair frame: for `p = 2` every
permutation of a block is a translation, and for odd `p` the translation
property is part of the data.

The literal block kernel is then the subrepresentation of the function
permutation module `ZMod p ^ I` given by its translation vectors, with the
original conjugation acting through the top action.  Its relative character
head is at most `|I| / p` when the top is a transitive `p`-group, and at most
`|I|` always.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- A frame of an actual permutation group by blocks of size `p` on which it
acts by translations. -/
structure PrimeTranslationFrame (p : ℕ) {X : Type*} (U : Subgroup (Equiv.Perm X))
    (I : Type*) where
  frame : I × ZMod p ≃ X
  top : U →* Equiv.Perm I
  intertwine : ∀ (u : U) (q : I × ZMod p), (frame.symm ((u : Equiv.Perm X) (frame q))).1 =
    top u q.1
  translate : ∀ (u : U) (i : I) (a : ZMod p),
    (frame.symm ((u : Equiv.Perm X) (frame (i, a)))).2 =
      a + (frame.symm ((u : Equiv.Perm X) (frame (i, 0)))).2

namespace PrimeTranslationFrame

variable {p : ℕ} {X I : Type*} {U : Subgroup (Equiv.Perm X)} (F : PrimeTranslationFrame p U I)

/-- The translation of an original element on one block. -/
def offset (u : U) (i : I) : ZMod p := (F.frame.symm ((u : Equiv.Perm X) (F.frame (i, 0)))).2

theorem action_frame (u : U) (i : I) (b : ZMod p) :
    (u : Equiv.Perm X) (F.frame (i, b)) = F.frame (F.top u i, b + F.offset u i) := by
  apply F.frame.symm.injective
  rw [F.frame.symm_apply_apply]
  exact Prod.ext (F.intertwine u (i, b)) (F.translate u i b)

/-- The translation vector of a kernel element. -/
def bits (k : F.top.ker) (i : I) : ZMod p := F.offset k i

theorem kernel_action_frame (k : F.top.ker) (i : I) (b : ZMod p) :
    ((k : U) : Equiv.Perm X) (F.frame (i, b)) = F.frame (i, b + F.bits k i) := by
  rw [F.action_frame]
  have hk : F.top (k : U) = 1 := k.property
  rw [hk]
  rfl

/-- The kernel as translation vectors. -/
def bitsHom : F.top.ker →* Multiplicative (I → ZMod p) where
  toFun k := Multiplicative.ofAdd (F.bits k)
  map_one' := by
    apply congrArg Multiplicative.ofAdd
    funext i
    change (F.frame.symm (F.frame (i, 0))).2 = 0
    rw [F.frame.symm_apply_apply]
  map_mul' a b := by
    apply congrArg Multiplicative.ofAdd
    funext i
    change (F.frame.symm (((a : U) : Equiv.Perm X)
      (((b : U) : Equiv.Perm X) (F.frame (i, 0))))).2 = F.bits a i + F.bits b i
    rw [F.kernel_action_frame, F.kernel_action_frame, F.frame.symm_apply_apply]
    simp only [zero_add]
    exact add_comm _ _

theorem bitsHom_injective : Function.Injective F.bitsHom := by
  intro a b hab
  have hbits : F.bits a = F.bits b := congrArg Multiplicative.toAdd hab
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  intro x
  obtain ⟨⟨i, t⟩, rfl⟩ := F.frame.surjective x
  rw [F.kernel_action_frame, F.kernel_action_frame, hbits]

variable [Fact p.Prime]

/-- The actual image of the kernel in `ZMod p ^ I`. -/
def kernelSpace : Submodule (ZMod p) (I → ZMod p) :=
  (AddMonoidHom.toMultiplicativeRight.symm F.bitsHom).range.toZModSubmodule p

def kernelSpaceHom : F.top.ker →* Multiplicative F.kernelSpace where
  toFun k := Multiplicative.ofAdd ⟨F.bits k, ⟨Additive.ofMul k, rfl⟩⟩
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
    obtain ⟨a, ha⟩ := x.toAdd.property
    refine ⟨a.toMul, ?_⟩
    apply congrArg Multiplicative.ofAdd
    exact Subtype.ext ha

/-- The kernel chart. -/
def kernelChart : F.top.ker ≃* Multiplicative F.kernelSpace :=
  MulEquiv.ofBijective F.kernelSpaceHom F.kernelSpaceHom_bijective

/-- Original conjugation is the top permutation action on translation vectors. -/
theorem bits_conjNormal (u : U) (k : F.top.ker) (i : I) :
    F.bits (MulAut.conjNormal u k) i = F.bits k ((F.top u)⁻¹ i) := by
  let j := (F.top u)⁻¹ i
  have hj : F.top u j = i := Equiv.apply_symm_apply (F.top u) i
  have he : (((MulAut.conjNormal u k : F.top.ker) : U) : Equiv.Perm X)
      ((u : Equiv.Perm X) (F.frame (j, 0))) =
        (u : Equiv.Perm X) (((k : U) : Equiv.Perm X) (F.frame (j, 0))) := by
    change ((u : Equiv.Perm X) * ((k : U) : Equiv.Perm X) * (u : Equiv.Perm X)⁻¹)
      ((u : Equiv.Perm X) (F.frame (j, 0))) = _
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply]
  rw [F.action_frame, F.kernel_action_frame, F.kernel_action_frame, F.action_frame] at he
  have hbits := congrArg Prod.snd (F.frame.injective he)
  simp only [hj, zero_add] at hbits
  exact add_left_cancel (hbits.trans (add_comm _ _))

variable [MulAction U I] (hact : ∀ (u : U) (i : I), u • i = F.top u i)

include hact

theorem originalCoordinateAction_bits (u : U) (k : F.top.ker) :
    permutationFunctionRepresentation (ZMod p) U I u (F.bits k) =
      F.bits (MulAut.conjNormal u k) := by
  funext i
  rw [permutationFunctionRepresentation_apply, hact, map_inv]
  exact (F.bits_conjNormal u k i).symm

/-- The kernel image is stable under the original group. -/
def kernelOriginalSubrepresentation :
    Subrepresentation (permutationFunctionRepresentation (ZMod p) U I) where
  toSubmodule := F.kernelSpace
  apply_mem_toSubmodule u v hv := by
    obtain ⟨k, rfl⟩ := hv
    change permutationFunctionRepresentation (ZMod p) U I u (F.bits k.toMul) ∈ F.kernelSpace
    rw [F.originalCoordinateAction_bits hact]
    exact ⟨Additive.ofMul (MulAut.conjNormal u k.toMul), rfl⟩

/-- The invariant characters of the subrepresentation are the relative
characters of the literal kernel. -/
def kernelOriginalCharactersEquiv :
    primeActionCharacters p
        (representationGroupAction (F.kernelOriginalSubrepresentation hact).toRepresentation)
      ≃ₗ[ZMod p] primeRelativeCharacters p F.top.ker :=
  (primeActionCharacterCongr p F.kernelChart
    (normalChainSourceAction F.top.ker)
    (representationGroupAction (F.kernelOriginalSubrepresentation hact).toRepresentation)
    (by
      intro u k
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      change F.bits (MulAut.conjNormal u k) =
        permutationFunctionRepresentation (ZMod p) U I u (F.bits k)
      exact (F.originalCoordinateAction_bits hact u k).symm)).trans
    (normalChainSourceCharactersEquiv F.top.ker p)

/-- The coarse bound for any block set. -/
theorem kernel_relativeHead_le_card [Finite I] :
    Module.finrank (ZMod p) (primeRelativeCharacters p F.top.ker) ≤ Nat.card I := by
  classical
  letI := Fintype.ofFinite I
  rw [← (F.kernelOriginalCharactersEquiv hact).finrank_eq]
  have h := subrepresentationCharacterHead_le_ambient_elementFixedSpace
    (permutationFunctionRepresentation (ZMod p) U I)
    (F.kernelOriginalSubrepresentation hact) (1 : U)
  have h' := h.trans (Submodule.finrank_le
    (representationElementFixedSpace (permutationFunctionRepresentation (ZMod p) U I) 1))
  simpa only [Module.finrank_pi, Nat.card_eq_fintype_card] using h'

/-- A transitive `p`-group top gives the bound `|I| / p`. -/
theorem kernel_relativeHead_le_div [Finite I] [Nontrivial I]
    [MulAction.IsPretransitive U I] (hU : IsPGroup p U) :
    Module.finrank (ZMod p) (primeRelativeCharacters p F.top.ker) ≤ Nat.card I / p := by
  rw [← (F.kernelOriginalCharactersEquiv hact).finrank_eq]
  exact pGroup_permutationSubrepresentationCharacterHead_le_div hU
    (F.kernelOriginalSubrepresentation hact)

end PrimeTranslationFrame
end SymmetricSubgroupAsymptotics
