import SymmetricSubgroupAsymptotics.BinaryInducedHead
import SymmetricSubgroupAsymptotics.PermutationSubrepresentationHead

/-! The original transitive permutation-function module injects into
coinduction from its actual point stabilizer. The resulting Boolean-width
bound applies to each original subrepresentation and its own invariant
forms, rather than to the ambient module's head. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable (k G X : Type) [Field k] [Group G] [MulAction G X]

/-- The inverse in the orbit coordinate matches the original left action
on functions and the actual right-translation convention of coinduction. -/
def permutationStabilizerCoinduction (x : X) :
    (permutationFunctionRepresentation k G X).IntertwiningMap
      (Representation.coind (MulAction.stabilizer G x).subtype
        (Representation.trivial k (MulAction.stabilizer G x) k)) where
  toLinearMap := {
    toFun := fun f => ⟨fun g => f (g⁻¹ • x), by
      intro h g
      change f (((h : G)*g)⁻¹ • x)=f (g⁻¹ • x)
      rw [mul_inv_rev,mul_smul]
      have hh : (h : G)⁻¹ • x=x := (h⁻¹).property
      rw [hh]⟩
    map_add' := by intro f f'; apply Subtype.ext; funext g; rfl
    map_smul' := by intro a f; apply Subtype.ext; funext g; rfl }
  isIntertwining' g := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext h
    change f (g⁻¹ • (h⁻¹ • x))=f ((h*g)⁻¹ • x)
    rw [mul_inv_rev,mul_smul]

theorem permutationStabilizerCoinduction_injective [MulAction.IsPretransitive G X]
    (x : X) : Function.Injective (permutationStabilizerCoinduction k G X x) := by
  intro f f' h
  funext y
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G x y
  have he := congrFun (congrArg Subtype.val h) g⁻¹
  change f ((g⁻¹)⁻¹ • x)=f' ((g⁻¹)⁻¹ • x) at he
  simpa only [inv_inv,hg] using he

variable {k G X}

/-- The entire original acting 2-group is retained; the action need not
be faithful. Only its actual transitive degree is used. -/
theorem twoGroup_permutationSubrepresentationHead_le_width
    [Finite G] [Finite X] [MulAction.IsPretransitive G X]
    (hG : IsPGroup 2 G) (t : ℕ) (hcard : Nat.card X=2^t) (x : X)
    (M : Subrepresentation (permutationFunctionRepresentation k G X)) :
    Module.finrank k
      (M.toRepresentation.IntertwiningMap (Representation.trivial k G k))≤
        t.choose (t/2) := by
  let φ := (permutationStabilizerCoinduction k G X x).comp
    (ThreeGroupHead.inclusion _ M)
  have hi : Function.Injective φ :=
    (permutationStabilizerCoinduction_injective k G X x).comp Subtype.val_injective
  have hindex : (MulAction.stabilizer G x).index=2^t :=
    (MulAction.index_stabilizer_of_transitive G x).trans hcard
  simpa only [Module.finrank_self,one_mul] using
    twoGroup_coinduced_injective_head_le hG (MulAction.stabilizer G x)
      (Representation.trivial k (MulAction.stabilizer G x) k) t hindex
      M.toRepresentation φ hi

/-- The same intrinsic bound on the original prime-valued invariant
characters, with the coefficient field allowed to be any prime field. -/
theorem twoGroup_permutationSubrepresentationCharacterHead_le_width
    {p : ℕ} [Fact p.Prime] {G X : Type} [Group G] [Finite G]
    [Finite X] [MulAction G X] [MulAction.IsPretransitive G X]
    (hG : IsPGroup 2 G) (t : ℕ) (hcard : Nat.card X=2^t) (x : X)
    (M : Subrepresentation (permutationFunctionRepresentation (ZMod p) G X)) :
    Module.finrank (ZMod p)
      (primeActionCharacters p (representationGroupAction M.toRepresentation))≤
        t.choose (t/2) := by
  letI := Fintype.ofFinite X
  rw [representationCharacterHead_finrank_eq_coinvariants,
    ← representationHead_finrank_eq_coinvariants]
  exact twoGroup_permutationSubrepresentationHead_le_width hG t hcard x M

end SymmetricSubgroupAsymptotics
