import SymmetricSubgroupAsymptotics.RepresentationGeneratorHead
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RepresentationTheory.Subrepresentation

/-! An invariant character annihilates the image of each actual element
minus the identity. Dual rank-nullity therefore bounds the character head
by that element's fixed space, also for an arbitrary actual subrepresentation.
No restriction of characters to fixed vectors is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- The fixed space of one specified element in the original representation. -/
def representationElementFixedSpace (ρ : Representation k G V) (g : G) : Submodule k V :=
  LinearMap.ker (ρ g - LinearMap.id)

@[simp] theorem mem_representationElementFixedSpace
    (ρ : Representation k G V) (g : G) (v : V) :
    v ∈ representationElementFixedSpace ρ g ↔ ρ g v = v := by
  change ρ g v - v = 0 ↔ _
  exact sub_eq_zero

/-- Invariant linear forms embed in the annihilator of `(ρ(g)-1)V`. -/
def representationHeadToElementAnnihilator (ρ : Representation k G V) (g : G) :
    ρ.IntertwiningMap (Representation.trivial k G k) →ₗ[k]
      (LinearMap.range (ρ g - LinearMap.id)).dualAnnihilator :=
  (Representation.IntertwiningMap.toLinearMapl (ρ := ρ)
    (σ := Representation.trivial k G k)).codRestrict _ (by
      intro f
      apply (Submodule.mem_dualAnnihilator _).mpr
      rintro _ ⟨v, rfl⟩
      change f.toLinearMap (ρ g v - v) = 0
      rw [map_sub]
      have hf : f (ρ g v) = f v :=
        Representation.IntertwiningMap.isIntertwining _ _ f g v
      exact sub_eq_zero.mpr hf)

theorem representationHeadToElementAnnihilator_injective
    (ρ : Representation k G V) (g : G) :
    Function.Injective (representationHeadToElementAnnihilator ρ g) := by
  intro f f' h
  exact Representation.IntertwiningMap.toLinearMap_injective _ _ (congrArg Subtype.val h)

/-- The head bound follows from annihilator dimension and rank-nullity,
including when the characteristic divides the order of the chosen element. -/
theorem representationHead_le_elementFixedSpace [FiniteDimensional k V]
    (ρ : Representation k G V) (g : G) :
    Module.finrank k (ρ.IntertwiningMap (Representation.trivial k G k)) ≤
      Module.finrank k (representationElementFixedSpace ρ g) := by
  have h := (representationHeadToElementAnnihilator ρ g).finrank_le_finrank_of_injective
    (representationHeadToElementAnnihilator_injective ρ g)
  have hd : Module.finrank k (LinearMap.range (ρ g - LinearMap.id)).dualAnnihilator =
      Module.finrank k (representationElementFixedSpace ρ g) := by
    exact Nat.add_left_cancel ((Subspace.finrank_add_finrank_dualAnnihilator_eq
      (LinearMap.range (ρ g - LinearMap.id))).trans
        (LinearMap.finrank_range_add_finrank_ker (ρ g - LinearMap.id)).symm)
  exact h.trans_eq hd

/-- The element-fixed space of an actual subrepresentation embeds in the
fixed space of its ambient original representation. -/
def subrepresentationElementFixedInclusion (ρ : Representation k G V)
    (M : Subrepresentation ρ) (g : G) :
    representationElementFixedSpace M.toRepresentation g →ₗ[k]
      representationElementFixedSpace ρ g where
  toFun v := ⟨v.1.1, by
    apply (mem_representationElementFixedSpace ρ g _).mpr
    have hv := (mem_representationElementFixedSpace M.toRepresentation g v.1).mp v.2
    exact congrArg Subtype.val hv⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem subrepresentationHead_le_ambient_elementFixedSpace [FiniteDimensional k V]
    (ρ : Representation k G V) (M : Subrepresentation ρ) (g : G) :
    Module.finrank k (M.toRepresentation.IntertwiningMap (Representation.trivial k G k)) ≤
      Module.finrank k (representationElementFixedSpace ρ g) := by
  apply (representationHead_le_elementFixedSpace M.toRepresentation g).trans
  apply (subrepresentationElementFixedInclusion ρ M g).finrank_le_finrank_of_injective
  intro v w h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun x : representationElementFixedSpace ρ g => (x : V)) h

theorem subrepresentationCharacterHead_le_ambient_elementFixedSpace
    {p : ℕ} [Fact p.Prime] {G₀ V₀ : Type*} [Group G₀]
    [AddCommGroup V₀] [Module (ZMod p) V₀] [FiniteDimensional (ZMod p) V₀]
    (ρ : Representation (ZMod p) G₀ V₀) (M : Subrepresentation ρ) (g : G₀) :
    Module.finrank (ZMod p)
      (primeActionCharacters p (representationGroupAction M.toRepresentation)) ≤
        Module.finrank (ZMod p) (representationElementFixedSpace ρ g) := by
  rw [(representationCharacterHeadEquiv M.toRepresentation).finrank_eq]
  exact subrepresentationHead_le_ambient_elementFixedSpace ρ M g

end SymmetricSubgroupAsymptotics
