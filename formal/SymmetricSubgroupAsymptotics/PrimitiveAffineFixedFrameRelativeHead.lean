import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveBlockTransfer
import SymmetricSubgroupAsymptotics.OriginalKernelNormalSubrepresentation
import SymmetricSubgroupAsymptotics.RepresentationCoinvariantHead
import SymmetricSubgroupAsymptotics.RelativeSecondIsomorphism

/-!
# The fixed-frame relative-head inequality

This file proves the extension-theoretic half of the fixed-frame argument.
For an elementary normal subgroup `E ◁ G`, a normal subgroup `K ◁ G`
has a binary relative head obtained from two literal pieces:

* the intersection `K ∩ E`, viewed as an invariant subrepresentation of
  the actual quotient representation on `E`;
* the image of `K` in `G / E`, with its original quotient conjugation action.

No splitting of the extension is used.  The proof is the relative-head
chain inequality, the relative second isomorphism theorem, and the exact
identification of the intersection head with the coinvariants of its
literal subrepresentation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-! ## Inflating a representation along a surjection does not change its head -/

variable {k A B V : Type} [Field k] [Group A] [Group B]
  [AddCommGroup V] [Module k V]

/-- Intertwining maps to the trivial line are unchanged after inflating a
representation along an onto ambient-group map. -/
def representationHeadCompSurjectiveEquiv
    (q : A →* B) (hq : Function.Surjective q)
    (rho : Representation k B V) :
    Representation.IntertwiningMap (rho.comp q)
        (Representation.trivial k A k) ≃ₗ[k]
      Representation.IntertwiningMap rho
        (Representation.trivial k B k) where
  toFun f :=
    { toLinearMap := f.toLinearMap
      isIntertwining' := by
        intro b
        obtain ⟨a, rfl⟩ := hq b
        apply LinearMap.ext
        intro v
        exact Representation.IntertwiningMap.isIntertwining _ _ f a v }
  invFun f :=
    { toLinearMap := f.toLinearMap
      isIntertwining' := by
        intro a
        apply LinearMap.ext
        intro v
        exact Representation.IntertwiningMap.isIntertwining _ _ f (q a) v }
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem representationHeadCompSurjective_finrank_eq
    (q : A →* B) (hq : Function.Surjective q)
    (rho : Representation k B V) :
    Module.finrank k
        (Representation.IntertwiningMap (rho.comp q)
          (Representation.trivial k A k)) =
      Module.finrank k
        (Representation.IntertwiningMap rho
          (Representation.trivial k B k)) :=
  (representationHeadCompSurjectiveEquiv q hq rho).finrank_eq

/-! ## The literal elementary intersection chart -/

variable {G : Type} [Group G] [Finite G]
variable (E : Subgroup G) [E.Normal]
variable (C : ElementaryMinimalNormalChart E)

private abbrev ElementaryIntersection
    (K : Subgroup G) := K ⊓ E

private abbrev ElementaryIntersectionSubrepresentation
    (K : Subgroup G) [K.Normal] :=
  C.originalKernelChart.normalSubrepresentation
    (QuotientGroup.mk' E) (QuotientGroup.mk'_surjective E)
    C.quotientRepresentation K

private abbrev ElementaryIntersectionModule
    (K : Subgroup G) [K.Normal] :=
  (ElementaryIntersectionSubrepresentation E C K).toSubmodule

omit [Finite G] in
/-- Membership in the stored invariant subrepresentation is literal
membership in `K`.  Keeping this equivalence separate makes the group
equivalence below just the restriction of the original elementary chart. -/
theorem elementaryIntersectionModule_mem_iff
    (K : Subgroup G) [K.Normal] (e : E) :
    (C.equiv e).toAdd ∈
        ElementaryIntersectionSubrepresentation E C K ↔
      (e.1 : G) ∈ K := by
  let A := C.quotientRepresentation
  let q : G →* G ⧸ E := QuotientGroup.mk' E
  let k : q.ker := C.quotientKernelEquiv (C.equiv e)
  have hkernel :
      (C.originalKernelChart.kernelCoordinates q A).ker ≤
        K.subgroupOf q.ker := by
    intro x hx
    have hx1 : x = 1 := by
      apply C.originalKernelChart.equiv.symm.injective
      exact (MonoidHom.mem_ker.mp hx).trans
        (map_one C.originalKernelChart.equiv.symm).symm
    subst x
    exact Subgroup.one_mem _
  have hkcoord :
      (C.originalKernelChart.kernelCoordinates q A k).toAdd =
        (C.equiv e).toAdd := by
    dsimp only [k, q, OriginalKernelModuleChart.kernelCoordinates,
      ElementaryMinimalNormalChart.originalKernelChart]
    change (C.equiv (C.equiv.symm (C.equiv e))).toAdd = _
    rw [C.equiv.apply_symm_apply]
  change (C.equiv e).toAdd ∈
      C.originalKernelChart.normalSubrepresentation q
        (QuotientGroup.mk'_surjective E) A K ↔
    (e.1 : G) ∈ K
  rw [← hkcoord]
  change (C.originalKernelChart.kernelCoordinates q A k).toAdd ∈
      sectionSubgroupImage
        (C.originalKernelChart.kernelCoordinates q A)
        (K.subgroupOf q.ker) ↔ _
  rw [sectionSubgroupImage_mem_iff
    (C.originalKernelChart.kernelCoordinates q A)
    (K.subgroupOf q.ker) hkernel k]
  change (k.1 : G) ∈ K ↔ (e.1 : G) ∈ K
  simp only [k, q,
    ElementaryMinimalNormalChart.quotientKernelEquiv_coe,
    C.equiv.symm_apply_apply]

/-- The multiplicative group of the literal invariant intersection is the
actual subgroup `K ∩ E`.  This is an equivalence onto the stored
subrepresentation, not an enlargement to the whole elementary kernel. -/
def elementaryIntersectionMulEquiv
    (K : Subgroup G) [K.Normal] :
    ElementaryIntersection E K ≃*
      Multiplicative (ElementaryIntersectionModule E C K) where
  toFun x := Multiplicative.ofAdd
    (⟨(C.equiv ⟨x.1, x.2.2⟩).toAdd,
      (elementaryIntersectionModule_mem_iff E C K
        ⟨x.1, x.2.2⟩).2 x.2.1⟩ : ElementaryIntersectionModule E C K)
  invFun v :=
    let e : E := C.equiv.symm (Multiplicative.ofAdd v.toAdd.1)
    ⟨e.1,
      (elementaryIntersectionModule_mem_iff E C K e).1 (by
        have heq : (C.equiv e).toAdd = v.toAdd.1 := by
          dsimp only [e]
          rw [C.equiv.apply_symm_apply]
          rfl
        rw [heq]
        exact v.toAdd.2),
      e.2⟩
  left_inv x := by
    apply Subtype.ext
    change (C.equiv.symm (C.equiv ⟨x.1, x.2.2⟩)).1 = x.1
    exact congrArg Subtype.val (C.equiv.symm_apply_apply ⟨x.1, x.2.2⟩)
  right_inv v := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd
      (C.equiv.apply_symm_apply (Multiplicative.ofAdd v.toAdd.1))
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    let ex : E := ⟨x.1, x.2.2⟩
    let ey : E := ⟨y.1, y.2.2⟩
    change (C.equiv (ex * ey)).toAdd =
      (C.equiv ex).toAdd + (C.equiv ey).toAdd
    exact congrArg Multiplicative.toAdd (map_mul C.equiv ex ey)

omit [Finite G] in
/-- The preceding equivalence respects the original ambient conjugation.
On the module side the action is the literal quotient representation,
inflated back along `G → G/E`. -/
theorem elementaryIntersectionMulEquiv_equivariant
    (K : Subgroup G) [K.Normal]
    (g : G) (x : ElementaryIntersection E K) :
    elementaryIntersectionMulEquiv E C K (MulAut.conjNormal g x) =
      representationGroupAction
        ((ElementaryIntersectionSubrepresentation E C K).toRepresentation.comp
          (QuotientGroup.mk' E)) g
        (elementaryIntersectionMulEquiv E C K x) := by
  unfold elementaryIntersectionMulEquiv
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  let ex : E := ⟨x.1, x.2.2⟩
  change (C.equiv (MulAut.conjNormal g ex)).toAdd =
    C.quotientRepresentation.ρ (QuotientGroup.mk' E g)
      (C.equiv ex).toAdd
  exact (C.quotientRepresentation_apply g ex).symm

/-- Relative characters of `K ∩ E` are exactly the character head of
its literal invariant subrepresentation. -/
def elementaryIntersectionRelativeCharacterEquiv
    (K : Subgroup G) [K.Normal] :
    primeRelativeCharacters C.p (ElementaryIntersection E K) ≃ₗ[ZMod C.p]
      Representation.IntertwiningMap
        (ElementaryIntersectionSubrepresentation E C K).toRepresentation
        (Representation.trivial (ZMod C.p) (G ⧸ E) (ZMod C.p)) :=
  (normalChainSourceCharactersEquiv
      (ElementaryIntersection E K) C.p).symm |>.trans
    ((primeActionCharacterCongr C.p
      (elementaryIntersectionMulEquiv E C K)
      (normalChainSourceAction (ElementaryIntersection E K))
      (representationGroupAction
        ((ElementaryIntersectionSubrepresentation E C K).toRepresentation.comp
          (QuotientGroup.mk' E)))
      (elementaryIntersectionMulEquiv_equivariant E C K)).symm.trans
      ((representationCharacterHeadEquiv
        ((ElementaryIntersectionSubrepresentation E C K).toRepresentation.comp
          (QuotientGroup.mk' E))).trans
        (representationHeadCompSurjectiveEquiv
          (QuotientGroup.mk' E) (QuotientGroup.mk'_surjective E)
          (ElementaryIntersectionSubrepresentation E C K).toRepresentation)))

omit [Finite G] in
theorem elementaryIntersection_relativeHead_eq_coinvariants
    (K : Subgroup G) [K.Normal] :
    Module.finrank (ZMod C.p)
        (primeRelativeCharacters C.p (ElementaryIntersection E K)) =
      Module.finrank (ZMod C.p)
        (ElementaryIntersectionSubrepresentation E C K).toRepresentation.Coinvariants := by
  let W : Subrepresentation C.quotientRepresentation.ρ :=
    ElementaryIntersectionSubrepresentation E C K
  letI : FiniteDimensional (ZMod C.p) C.quotientRepresentation :=
    C.finiteDimensional
  letI : Module (ZMod C.p) W.toSubmodule := W.toSubmodule.module
  letI : FiniteDimensional (ZMod C.p) W.toSubmodule :=
    FiniteDimensional.finiteDimensional_submodule W.toSubmodule
  exact (elementaryIntersectionRelativeCharacterEquiv E C K).finrank_eq.trans
    (representationHead_finrank_eq_coinvariants
      (ElementaryIntersectionSubrepresentation E C K).toRepresentation)

/-! ## Fixed-frame rank addition -/

/-- The exact fixed-frame inequality.  The original relative head of every
normal subgroup is bounded by the head of its invariant elementary
intersection plus the relative head of its literal image in the quotient.
-/
theorem elementaryExtension_relativeHead_le_intersection_add_quotient
    (K : Subgroup G) [K.Normal] :
    Module.finrank (ZMod C.p) (primeRelativeCharacters C.p K) ≤
      Module.finrank (ZMod C.p)
          (ElementaryIntersectionSubrepresentation E C K).toRepresentation.Coinvariants +
        Module.finrank (ZMod C.p)
          (primeRelativeCharacters C.p (normalChainQuotient E K)) := by
  have hchain := primeRelativeHead_chain_le (K ⊓ E) K C.p inf_le_left
  rw [elementaryIntersection_relativeHead_eq_coinvariants E C K,
    primeRelativeHead_second_isomorphism C.p K E] at hchain
  exact hchain

/-- Uniform numerical form used by the finite-frame rows. -/
theorem elementaryExtension_relativeHead_le
    (K : Subgroup G) [K.Normal]
    (a b : ℕ)
    (hmodule : Module.finrank (ZMod C.p)
      (ElementaryIntersectionSubrepresentation E C K).toRepresentation.Coinvariants ≤ a)
    (htop : Module.finrank (ZMod C.p)
      (primeRelativeCharacters C.p (normalChainQuotient E K)) ≤ b) :
    Module.finrank (ZMod C.p) (primeRelativeCharacters C.p K) ≤ a + b :=
  (elementaryExtension_relativeHead_le_intersection_add_quotient E C K).trans
    (Nat.add_le_add hmodule htop)

end SymmetricSubgroupAsymptotics

end
