import SymmetricSubgroupAsymptotics.RepresentationElementHead

/-!
# Heads of actual equivariant quotients

Precomposition by the given equivariant surjection injects invariant linear
forms on its target into those on its source. For a source which is an actual
subrepresentation, the checked element-fixed-space bound therefore also
controls the quotient head. No section or semisimplicity is required.
-/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {k G V Q : Type*} [Field k] [Group G]
    [AddCommGroup V] [Module k V] [AddCommGroup Q] [Module k Q]

/-- The actual invariant form is pulled back along the original map. -/
def representationHeadPrecompose (ρ : Representation k G V)
    (σ : Representation k G Q) (f : ρ.IntertwiningMap σ) :
    σ.IntertwiningMap (Representation.trivial k G k) →ₗ[k]
      ρ.IntertwiningMap (Representation.trivial k G k) where
  toFun ℓ := ℓ.comp f
  map_add' _ _ := by ext v; rfl
  map_smul' _ _ := by ext v; rfl

@[simp] theorem representationHeadPrecompose_apply
    (ρ : Representation k G V) (σ : Representation k G Q)
    (f : ρ.IntertwiningMap σ)
    (ℓ : σ.IntertwiningMap (Representation.trivial k G k)) (v : V) :
    representationHeadPrecompose ρ σ f ℓ v = ℓ (f v) := rfl

/-- Surjectivity gives equality of the original target forms at every vector;
it does not assert that fixed vectors or invariant forms admit a section. -/
theorem representationHeadPrecompose_injective
    (ρ : Representation k G V) (σ : Representation k G Q)
    (f : ρ.IntertwiningMap σ) (hf : Function.Surjective f) :
    Function.Injective (representationHeadPrecompose ρ σ f) := by
  intro ℓ ℓ' h
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro q
  obtain ⟨v, rfl⟩ := hf q
  exact congrArg (fun u : ρ.IntertwiningMap (Representation.trivial k G k) => u v) h

/-- The head of the actual quotient is bounded by the head of its source.
Only the source is assumed finite-dimensional. -/
theorem representationQuotientHead_le_source [FiniteDimensional k V]
    (ρ : Representation k G V) (σ : Representation k G Q)
    (f : ρ.IntertwiningMap σ) (hf : Function.Surjective f) :
    Module.finrank k (σ.IntertwiningMap (Representation.trivial k G k)) ≤
      Module.finrank k (ρ.IntertwiningMap (Representation.trivial k G k)) :=
  (representationHeadPrecompose ρ σ f).finrank_le_finrank_of_injective
    (representationHeadPrecompose_injective ρ σ f hf)

/-- A quotient of an actual subrepresentation has head bounded by the fixed
space of the specified element in the original ambient representation. -/
theorem subrepresentationQuotientHead_le_ambient_elementFixedSpace
    [FiniteDimensional k V] (ρ : Representation k G V)
    (M : Subrepresentation ρ) (σ : Representation k G Q)
    (f : M.toRepresentation.IntertwiningMap σ) (hf : Function.Surjective f)
    (g : G) :
    Module.finrank k (σ.IntertwiningMap (Representation.trivial k G k)) ≤
      Module.finrank k (representationElementFixedSpace ρ g) :=
  (representationQuotientHead_le_source M.toRepresentation σ f hf).trans
    (subrepresentationHead_le_ambient_elementFixedSpace ρ M g)

/-- Unbundled interface for the given linear quotient map and its exact
equivariance equations, retaining the same acting group and both actions. -/
theorem subrepresentationQuotientHead_le_ambient_elementFixedSpace_of_equivariant
    [FiniteDimensional k V] (ρ : Representation k G V)
    (M : Subrepresentation ρ) (σ : Representation k G Q)
    (f : M.toSubmodule →ₗ[k] Q)
    (heq : ∀ g v, f (M.toRepresentation g v) = σ g (f v))
    (hf : Function.Surjective f) (g : G) :
    Module.finrank k (σ.IntertwiningMap (Representation.trivial k G k)) ≤
      Module.finrank k (representationElementFixedSpace ρ g) :=
  subrepresentationQuotientHead_le_ambient_elementFixedSpace ρ M σ
    (f.intertwiningMap_of_isIntertwiningMap M.toRepresentation σ heq) hf g

/-- Prime action characters of the actual target inject into those of the
actual source via the same original equivariant surjection. -/
theorem representationQuotientCharacterHead_le_source
    {p : ℕ} [Fact p.Prime] {G₀ V₀ Q₀ : Type*} [Group G₀]
    [AddCommGroup V₀] [Module (ZMod p) V₀] [FiniteDimensional (ZMod p) V₀]
    [AddCommGroup Q₀] [Module (ZMod p) Q₀]
    (ρ : Representation (ZMod p) G₀ V₀) (σ : Representation (ZMod p) G₀ Q₀)
    (f : ρ.IntertwiningMap σ) (hf : Function.Surjective f) :
    Module.finrank (ZMod p) (primeActionCharacters p (representationGroupAction σ)) ≤
      Module.finrank (ZMod p) (primeActionCharacters p (representationGroupAction ρ)) := by
  rw [(representationCharacterHeadEquiv σ).finrank_eq,
    (representationCharacterHeadEquiv ρ).finrank_eq]
  exact representationQuotientHead_le_source ρ σ f hf

/-- The quotient-head bound on literal prime action characters, using the
given linear surjection and its original equivariance data. -/
theorem subrepresentationQuotientCharacterHead_le_ambient_elementFixedSpace
    {p : ℕ} [Fact p.Prime] {G₀ V₀ Q₀ : Type*} [Group G₀]
    [AddCommGroup V₀] [Module (ZMod p) V₀] [FiniteDimensional (ZMod p) V₀]
    [AddCommGroup Q₀] [Module (ZMod p) Q₀]
    (ρ : Representation (ZMod p) G₀ V₀) (M : Subrepresentation ρ)
    (σ : Representation (ZMod p) G₀ Q₀) (f : M.toSubmodule →ₗ[ZMod p] Q₀)
    (heq : ∀ g v, f (M.toRepresentation g v) = σ g (f v))
    (hf : Function.Surjective f) (g : G₀) :
    Module.finrank (ZMod p) (primeActionCharacters p (representationGroupAction σ)) ≤
      Module.finrank (ZMod p) (representationElementFixedSpace ρ g) := by
  rw [(representationCharacterHeadEquiv σ).finrank_eq]
  exact subrepresentationQuotientHead_le_ambient_elementFixedSpace_of_equivariant
    ρ M σ f heq hf g

end SymmetricSubgroupAsymptotics
