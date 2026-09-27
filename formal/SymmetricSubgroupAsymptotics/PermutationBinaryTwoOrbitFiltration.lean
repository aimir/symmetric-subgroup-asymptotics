import SymmetricSubgroupAsymptotics.RepresentationHeadExact
import SymmetricSubgroupAsymptotics.PermutationBinaryFourAugmentation
import SymmetricSubgroupAsymptotics.PermutationBinaryRankTwoOrbits

/-! Equality in the actual two-orbit head filtration.

The first term is the literal image of the kernel of restriction to the
second orbit. The second term is the actual restriction image. Equality
forces each of these subspaces to be its original augmentation
hyperplane and forces the original correlated module to have dimension
six. This alone does not identify that module with a product; the
possible extension graph is explicitly not discarded here.
-/
set_option autoImplicit false
noncomputable section
open scoped Classical
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics.PermutationBinaryTwoOrbitFiltration

open RepresentationHeadExact

variable {G X : Type} [Group G] [Finite G] [MulAction G X] [Finite X]
    (M : Subrepresentation (permutationFunctionRepresentation (ZMod 2) G X))

/-- The actual first-coordinate image of the kernel of the second
original orbit restriction. -/
def firstKernelImage (o₁ o₂ : MulAction.orbitRel.Quotient G X) :
    Subrepresentation (permutationFunctionRepresentation (ZMod 2) G o₁.orbit) :=
  ((permutationSubrepresentationOrbitRestriction M o₁).comp
    (kernelInclusion (permutationSubrepresentationOrbitRestriction M o₂))).range

/-- The complete image of restriction to the second original orbit. -/
def secondImage (o₂ : MulAction.orbitRel.Quotient G X) :
    Subrepresentation (permutationFunctionRepresentation (ZMod 2) G o₂.orbit) :=
  (permutationSubrepresentationOrbitRestriction M o₂).range

theorem jointInjective (o₁ o₂ : MulAction.orbitRel.Quotient G X)
    (hcover : ∀ o : MulAction.orbitRel.Quotient G X,o=o₁ ∨ o=o₂) :
    Function.Injective (fun m : M.toSubmodule =>
      (permutationSubrepresentationOrbitRestriction M o₁ m,
        permutationSubrepresentationOrbitRestriction M o₂ m)) := by
  intro m m' h
  apply permutationSubrepresentationOrbitRestriction_jointly_injective M
  funext o
  rcases hcover o with rfl | rfl
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

/-- Literal filtration equality at two four-point original orbits.
Neither the coordinate images nor the kernel intersection is supplied
as a head-maximizing module. -/
theorem filtration_eq_augmentation
    (hG : IsPGroup 2 G)
    (o₁ o₂ : MulAction.orbitRel.Quotient G X)
    (hcover : ∀ o : MulAction.orbitRel.Quotient G X,o=o₁ ∨ o=o₂)
    (hcard₁ : Nat.card o₁.orbit=4) (hcard₂ : Nat.card o₂.orbit=4)
    (hhead : 4≤Module.finrank (ZMod 2)
      (M.toRepresentation.IntertwiningMap (Representation.trivial (ZMod 2) G (ZMod 2)))) :
    (firstKernelImage M o₁ o₂).toSubmodule=
        PermutationAugmentation.space (ZMod 2) o₁.orbit ∧
      (secondImage M o₂).toSubmodule=
        PermutationAugmentation.space (ZMod 2) o₂.orbit ∧
      Module.finrank (ZMod 2) M.toSubmodule=6 := by
  let x₁ : o₁.orbit := ⟨o₁.nonempty_orbit.choose,o₁.nonempty_orbit.choose_spec⟩
  let x₂ : o₂.orbit := ⟨o₂.nonempty_orbit.choose,o₂.nonempty_orbit.choose_spec⟩
  have hb₁ := twoGroup_permutationSubrepresentationHead_le_width hG 2
    (by simpa using hcard₁) x₁ (firstKernelImage M o₁ o₂)
  have hb₂ := twoGroup_permutationSubrepresentationHead_le_width hG 2
    (by simpa using hcard₂) x₂ (secondImage M o₂)
  norm_num at hb₁ hb₂
  have hsplit := head_finrank_le_two_coordinates
    (permutationSubrepresentationOrbitRestriction M o₁)
    (permutationSubrepresentationOrbitRestriction M o₂) (jointInjective M o₁ o₂ hcover)
  change Module.finrank (ZMod 2)
      (M.toRepresentation.IntertwiningMap (Representation.trivial (ZMod 2) G (ZMod 2)))≤
    Module.finrank (ZMod 2) ((firstKernelImage M o₁ o₂).toRepresentation.IntertwiningMap
      (Representation.trivial (ZMod 2) G (ZMod 2)))+
    Module.finrank (ZMod 2) ((secondImage M o₂).toRepresentation.IntertwiningMap
      (Representation.trivial (ZMod 2) G (ZMod 2))) at hsplit
  have hh₁ : 2≤Module.finrank (ZMod 2)
      ((firstKernelImage M o₁ o₂).toRepresentation.IntertwiningMap
        (Representation.trivial (ZMod 2) G (ZMod 2))) := by omega
  have hh₂ : 2≤Module.finrank (ZMod 2)
      ((secondImage M o₂).toRepresentation.IntertwiningMap
        (Representation.trivial (ZMod 2) G (ZMod 2))) := by omega
  obtain ⟨hd₁,he₁⟩ := PermutationBinaryFourAugmentation.eq_augmentation_of_head_ge_two
    (firstKernelImage M o₁ o₂) hG x₁ hcard₁ hh₁
  obtain ⟨hd₂,he₂⟩ := PermutationBinaryFourAugmentation.eq_augmentation_of_head_ge_two
    (secondImage M o₂) hG x₂ hcard₂ hh₂
  let f₂ := permutationSubrepresentationOrbitRestriction M o₂
  let f₁ := (permutationSubrepresentationOrbitRestriction M o₁).comp (kernelInclusion f₂)
  have hi : Function.Injective f₁ := by
    intro v w h
    apply Subtype.ext
    apply jointInjective M o₁ o₂ hcover
    apply Prod.ext
    · exact h
    · exact v.property.trans w.property.symm
  have hk := (LinearEquiv.ofInjective f₁.toLinearMap hi).finrank_eq
  change Module.finrank (ZMod 2) f₂.toLinearMap.ker=
    Module.finrank (ZMod 2) (firstKernelImage M o₁ o₂).toSubmodule at hk
  have hr := f₂.toLinearMap.finrank_range_add_finrank_ker
  change Module.finrank (ZMod 2) (secondImage M o₂).toSubmodule+
    Module.finrank (ZMod 2) f₂.toLinearMap.ker=
      Module.finrank (ZMod 2) M.toSubmodule at hr
  exact ⟨he₁,he₂,by omega⟩

/-- The four-dimensional trivial quotient supplies the extremal head
internally. The two chosen orbit labels name actual orbit subsets. -/
theorem exists_filtration_eq_augmentation
    {A : Type} [AddCommGroup A] [Module (ZMod 2) A] [FiniteDimensional (ZMod 2) A]
    (hG : IsPGroup 2 G)
    (hclasses : Nat.card (MulAction.orbitRel.Quotient G X)=2)
    (hcard : ∀ o : MulAction.orbitRel.Quotient G X,Nat.card o.orbit=4)
    (q : M.toSubmodule →ₗ[ZMod 2] A) (hq : Function.Surjective q)
    (htrivial : ∀ (g : G) (m : M.toSubmodule),q (M.toRepresentation g m)=q m)
    (hA : 4≤Module.finrank (ZMod 2) A) :
    ∃ o₁ o₂ : MulAction.orbitRel.Quotient G X,
      o₁≠o₂ ∧ (∀ o : MulAction.orbitRel.Quotient G X,o=o₁ ∨ o=o₂) ∧
      (firstKernelImage M o₁ o₂).toSubmodule=
        PermutationAugmentation.space (ZMod 2) o₁.orbit ∧
      (secondImage M o₂).toSubmodule=
        PermutationAugmentation.space (ZMod 2) o₂.orbit ∧
      Module.finrank (ZMod 2) M.toSubmodule=6 := by
  obtain ⟨o₁,o₂,hne,huniv⟩ := Nat.card_eq_two_iff.mp hclasses
  have hcover : ∀ o : MulAction.orbitRel.Quotient G X,o=o₁ ∨ o=o₂ := by
    intro o
    have hm : o∈({o₁,o₂} : Set (MulAction.orbitRel.Quotient G X)) := by
      rw [huniv]
      exact Set.mem_univ o
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using hm
  let q' : M.toRepresentation.Coinvariants →ₗ[ZMod 2] A :=
    Representation.Coinvariants.lift M.toRepresentation q (by
      intro g
      apply LinearMap.ext
      exact htrivial g)
  have hq' : Function.Surjective q' := by
    intro a
    obtain ⟨m,rfl⟩ := hq a
    exact ⟨Representation.Coinvariants.mk M.toRepresentation m,rfl⟩
  have hdim := LinearMap.finrank_le_finrank_of_surjective hq'
  rw [← representationHead_finrank_eq_coinvariants] at hdim
  exact ⟨o₁,o₂,hne,hcover,filtration_eq_augmentation M hG o₁ o₂ hcover
    (hcard o₁) (hcard o₂) (hA.trans hdim)⟩

end SymmetricSubgroupAsymptotics.PermutationBinaryTwoOrbitFiltration
