import SymmetricSubgroupAsymptotics.AbelianExtensionFixedSpaceIdentityReserve
import SymmetricSubgroupAsymptotics.PermutationSubrepresentationHead

/-! An actual binary abelian kernel embeds equivariantly in the literal
UNSIGNED permutation module of its original quotient. Original fixed
kernel elements inject into original ambient fixed functions. The
extension need not split, and the kernel need not be the full base or
augmentation. No top-group class bound or action classification is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.AbelianExtensionUnsignedPermutationClassBound
open AbelianExtensionConjugation
variable {G X : Type*} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] [IsMulCommutative N]
    [Finite X] [MulAction (G ⧸ N) X]

/-- Fixed kernel elements retain their actual equivariant coordinates.
The upper bound uses the actual cyclic orbits of this same element. -/
theorem fixed_card_le_cyclic_orbits
    (f : N →* Multiplicative (X→ZMod 2)) (hf : Function.Injective f)
    (hintertwine : ∀ (q : G ⧸ N) (n : N),
      (f (quotientConjugation N q n)).toAdd=
        permutationFunctionRepresentation (ZMod 2) (G ⧸ N) X q (f n).toAdd)
    (q : G ⧸ N) :
    Nat.card {n : N // quotientConjugation N q n=n}≤
      2^Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers q) X) := by
  letI : Fintype X := Fintype.ofFinite X
  let F : {n : N // quotientConjugation N q n=n} →
      representationElementFixedSpace (permutationFunctionRepresentation (ZMod 2) (G ⧸ N) X) q :=
    fun n => ⟨(f n.val).toAdd,by
      apply (mem_representationElementFixedSpace _ _ _).mpr
      rw [←hintertwine,n.property]⟩
  have hF : Function.Injective F := by
    intro a b h
    apply Subtype.ext
    apply hf
    apply Multiplicative.toAdd.injective
    exact congrArg (fun z : representationElementFixedSpace
      (permutationFunctionRepresentation (ZMod 2) (G ⧸ N) X) q => z.val) h
  have hcard : Nat.card (ZMod 2)=2 := by
    rw [Nat.card_eq_fintype_card,ZMod.card]
  have hdim := permutation_elementFixedSpace_le_cyclicOrbitCount
    (k:=ZMod 2) (G:=G ⧸ N) (X:=X) q
  calc
    _≤Nat.card (representationElementFixedSpace
        (permutationFunctionRepresentation (ZMod 2) (G ⧸ N) X) q) :=
      Nat.card_le_card_of_injective F hF
    _=Nat.card (ZMod 2)^Module.finrank (ZMod 2) (representationElementFixedSpace
        (permutationFunctionRepresentation (ZMod 2) (G ⧸ N) X) q) :=
      Module.natCard_eq_pow_finrank
    _≤2^Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers q) X) := by
      rw [hcard]
      exact Nat.pow_le_pow_right (by decide) hdim

/-- Every original nonidentity quotient element has at most n-2 cyclic
orbits, so the actual binary extension has at most(k(Q)+1)2^(n-2)
classes. The point condition is structural and remains for the actual
model bridge to establish. -/
theorem class_card_le_class_add_one_mul
    (f : N →* Multiplicative (X→ZMod 2)) (hf : Function.Injective f)
    (hintertwine : ∀ (q : G ⧸ N) (n : N),
      (f (quotientConjugation N q n)).toAdd=
        permutationFunctionRepresentation (ZMod 2) (G ⧸ N) X q (f n).toAdd)
    (hquotient : 4≤Nat.card (G ⧸ N))
    (hcycles : ∀ q : G ⧸ N, q≠1 →
      Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers q) X)≤Nat.card X-2) :
    Nat.card (ConjClasses G)≤(Nat.card (ConjClasses (G ⧸ N))+1)*2^(Nat.card X-2) := by
  letI : Fintype X := Fintype.ofFinite X
  have hbinary : Nat.card (ZMod 2)=2 := by rw [Nat.card_eq_fintype_card,ZMod.card]
  have hsize : Nat.card N≤2^Nat.card X := by
    have hh := Nat.card_le_card_of_injective f hf
    have hc : Nat.card (Multiplicative (X→ZMod 2))=2^Nat.card X := by
      rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (X→ZMod 2) ≃ (X→ZMod 2)),
        Nat.card_fun,hbinary]
    exact hh.trans_eq hc
  have hreserve : 2^Nat.card X≤4*2^(Nat.card X-2) := by
    calc
      2^Nat.card X≤2^((Nat.card X-2)+2) := Nat.pow_le_pow_right (by decide) (by omega)
      _=4*2^(Nat.card X-2) := by rw [pow_add]; ring
  apply AbelianExtensionFixedSpaceIdentityReserve.class_card_le_class_add_one_mul N
    (2^(Nat.card X-2)) hquotient (hsize.trans hreserve)
  intro q hq
  exact (fixed_card_le_cyclic_orbits N f hf hintertwine q).trans
    (Nat.pow_le_pow_right (by decide) (hcycles q hq))

end SymmetricSubgroupAsymptotics.AbelianExtensionUnsignedPermutationClassBound
