import SymmetricSubgroupAsymptotics.BinaryPairNormalHead
import SymmetricSubgroupAsymptotics.BinaryPairCoordinateSubgroups
import SymmetricSubgroupAsymptotics.RepresentationCoinvariantHead
import SymmetricSubgroupAsymptotics.PrimeRelativeRadical
import SymmetricSubgroupAsymptotics.PGroupNormalGeneratorCharacterEquality

/-! The actual axis of any original normal subgroup inside the pair kernel
retains its whole ambient invariant-character space and its literal radical.
Coinvariants are intrinsic to that same axis, under the actual top image. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- Surjecting onto the actual acting group changes neither invariant
forms nor their evaluations on the original vector space. -/
def trivialHeadCompSurjectiveEquiv
    {k A T V : Type*} [Field k] [Group A] [Group T]
    [AddCommGroup V] [Module k V] (rho : Representation k T V)
    (f : A →* T) (hf : Function.Surjective f) :
    Representation.IntertwiningMap (rho.comp f) (Representation.trivial k A k) ≃ₗ[k]
      rho.IntertwiningMap (Representation.trivial k T k) where
  toFun l := {
    toLinearMap := l.toLinearMap
    isIntertwining' := by
      intro t
      obtain ⟨a,rfl⟩ := hf t
      exact l.isIntertwining' a }
  invFun l := {
    toLinearMap := l.toLinearMap
    isIntertwining' := fun a => l.isIntertwining' (f a) }
  left_inv l := by ext v; rfl
  right_inv l := by ext v; rfl
  map_add' l m := by ext v; rfl
  map_smul' c l := by ext v; rfl

namespace BinaryPairFrame
variable {X : Type} {w : ℕ} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin w)) (B : Subgroup U) [B.Normal]
    (hB : B ≤ F.top.ker)

/-- The actual correlated flip chart on B itself. -/
def axisNormalHom : B →* Multiplicative (F.ambientAxis B) where
  toFun b := Multiplicative.ofAdd
    ⟨F.bits ⟨b.val,hB b.property⟩,
      (F.bits_mem_ambientAxis B ⟨b.val,hB b.property⟩).mpr b.property⟩
  map_one' := by
    apply congrArg Multiplicative.ofAdd
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd F.bitsHom.map_one
  map_mul' b c := by
    apply congrArg Multiplicative.ofAdd
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd
      (F.bitsHom.map_mul ⟨b.val,hB b.property⟩ ⟨c.val,hB c.property⟩)

omit [B.Normal] in
theorem axisNormalHom_bijective : Function.Bijective (F.axisNormalHom B hB) := by
  constructor
  · intro a b he
    apply Subtype.ext
    have hk := F.bitsHom_injective
      (congrArg (fun v : Multiplicative (F.ambientAxis B) =>
        Multiplicative.ofAdd v.toAdd.val) he)
    exact congrArg (fun k : F.top.ker => k.val) hk
  · intro v
    obtain ⟨k,hk,he⟩ := (F.mem_ambientAxis B v.toAdd.val).mp v.toAdd.property
    refine ⟨⟨k.val,hk⟩,?_⟩
    apply congrArg Multiplicative.ofAdd
    exact Subtype.ext he

def axisNormalChart : B ≃* Multiplicative (F.ambientAxis B) :=
  MulEquiv.ofBijective (F.axisNormalHom B hB) (F.axisNormalHom_bijective B hB)

def axisRelativeCharacterEquiv :
    primeActionCharacters 2 (representationGroupAction
      ((F.axisSubrepresentation B).toRepresentation.comp F.top.rangeRestrict))
        ≃ₗ[ZMod 2] primeRelativeCharacters 2 B :=
  (primeActionCharacterCongr 2 (F.axisNormalChart B hB)
    (normalChainSourceAction B)
    (representationGroupAction
      ((F.axisSubrepresentation B).toRepresentation.comp F.top.rangeRestrict))
    (by
      intro u b
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      exact (F.coordinateTopAction_bits u ⟨b.val,hB b.property⟩).symm)).trans
    (normalChainSourceCharactersEquiv B 2)

/-- Complete original invariant characters are dual to the coinvariants
of the same retained axis. -/
def axisRelativeCoinvariantsDualEquiv :
    primeRelativeCharacters 2 B ≃ₗ[ZMod 2]
      Module.Dual (ZMod 2) (F.axisSubrepresentation B).toRepresentation.Coinvariants :=
  (F.axisRelativeCharacterEquiv B hB).symm.trans
    ((representationCharacterHeadEquiv
      ((F.axisSubrepresentation B).toRepresentation.comp F.top.rangeRestrict)).trans
      ((trivialHeadCompSurjectiveEquiv _ F.top.rangeRestrict
        F.top.rangeRestrict_surjective).trans
        (representationHeadCoinvariantsDualEquiv _)))

@[simp] theorem axisRelativeCoinvariantsDualEquiv_apply
    (chi : primeRelativeCharacters 2 B) (b : B) :
    F.axisRelativeCoinvariantsDualEquiv B hB chi
      (Representation.Coinvariants.mk (F.axisSubrepresentation B).toRepresentation
        (F.axisNormalChart B hB b).toAdd) = chi.1 (Additive.ofMul b) := by
  have he := congrArg
    (fun c : primeRelativeCharacters 2 B => c.1 (Additive.ofMul b))
    ((F.axisRelativeCharacterEquiv B hB).apply_symm_apply chi)
  exact he

include hB in
theorem axis_relativeHead_eq_coinvariants [Finite X] :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 B) =
      Module.finrank (ZMod 2) (F.axisSubrepresentation B).toRepresentation.Coinvariants :=
  (F.axisRelativeCoinvariantsDualEquiv B hB).finrank_eq.trans Subspace.dual_finrank_eq

include hB in
/-- The radical is transported on each literal original element. -/
theorem axis_mem_radical_iff (k : F.top.ker) (hkB : k.val ∈ B) :
    k.val ∈ primeRelativeRadical 2 B ↔
      F.bits k ∈ (Representation.Coinvariants.ker
        (F.axisSubrepresentation B).toRepresentation).map
          (F.axisSubrepresentation B).toSubmodule.subtype := by
  let b : B := ⟨k.val,hkB⟩
  let v : F.ambientAxis B := (F.axisNormalChart B hB b).toAdd
  have hz : k.val ∈ primeRelativeRadical 2 B ↔
      ∀ l : Module.Dual (ZMod 2)
        (F.axisSubrepresentation B).toRepresentation.Coinvariants,
        l (Representation.Coinvariants.mk
          (F.axisSubrepresentation B).toRepresentation v)=0 := by
    rw [coe_mem_primeRelativeRadical_iff 2 B b,
      mem_primeRelativeRadicalKernel_iff]
    constructor
    · intro h l
      obtain ⟨chi,rfl⟩ := (F.axisRelativeCoinvariantsDualEquiv B hB).surjective l
      exact (F.axisRelativeCoinvariantsDualEquiv_apply B hB chi b).trans (h chi)
    · intro h chi
      exact (F.axisRelativeCoinvariantsDualEquiv_apply B hB chi b).symm.trans
        (h (F.axisRelativeCoinvariantsDualEquiv B hB chi))
  rw [hz,Module.forall_dual_apply_eq_zero_iff,
    Representation.Coinvariants.mk_eq_zero]
  constructor
  · intro hv
    exact ⟨v,hv,rfl⟩
  · rintro ⟨a,ha,he⟩
    have hav : a=v := Subtype.ext he
    exact hav ▸ ha

include hB in
theorem axis_normalGen_eq_coinvariants [Finite X] (hU : IsPGroup 2 U) :
    MarkedC4.normalGen B =
      Module.finrank (ZMod 2) (F.axisSubrepresentation B).toRepresentation.Coinvariants :=
  (pGroup_normalGen_eq_primeRelativeHead 2 hU B).trans
    (F.axis_relativeHead_eq_coinvariants B hB)

end BinaryPairFrame
end SymmetricSubgroupAsymptotics
