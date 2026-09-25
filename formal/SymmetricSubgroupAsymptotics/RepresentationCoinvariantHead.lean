import SymmetricSubgroupAsymptotics.RepresentationGeneratorHead
import Mathlib.RepresentationTheory.Coinvariants
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Invariant linear forms are exactly the dual of the intrinsic
coinvariants of the same actual representation. No semisimplicity or
surjective restriction of ambient invariant forms is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- Descend the original invariant form through its own coinvariants;
the inverse is precomposition with the actual quotient map. -/
def representationHeadCoinvariantsDualEquiv (ρ : Representation k G V) :
    ρ.IntertwiningMap (Representation.trivial k G k) ≃ₗ[k]
      Module.Dual k ρ.Coinvariants where
  toFun f := Representation.Coinvariants.lift ρ f.toLinearMap (by
    intro g
    ext v
    exact Representation.IntertwiningMap.isIntertwining _ _ f g v)
  invFun ℓ := {
    toLinearMap := ℓ.comp (Representation.Coinvariants.mk ρ)
    isIntertwining' := by
      intro g
      ext v
      exact congrArg ℓ (Representation.Coinvariants.mk_self_apply ρ g v) }
  left_inv f := by ext v; rfl
  right_inv ℓ := by
    apply Representation.Coinvariants.hom_ext
    ext v
    rfl
  map_add' f f' := by
    apply Representation.Coinvariants.hom_ext
    ext v
    rfl
  map_smul' r f := by
    apply Representation.Coinvariants.hom_ext
    ext v
    rfl

@[simp] theorem representationHeadCoinvariantsDualEquiv_apply_mk
    (ρ : Representation k G V)
    (f : ρ.IntertwiningMap (Representation.trivial k G k)) (v : V) :
    representationHeadCoinvariantsDualEquiv ρ f (Representation.Coinvariants.mk ρ v) = f v :=
  rfl

theorem representationHead_finrank_eq_coinvariants [FiniteDimensional k V]
    (ρ : Representation k G V) :
    Module.finrank k (ρ.IntertwiningMap (Representation.trivial k G k)) =
      Module.finrank k ρ.Coinvariants :=
  (representationHeadCoinvariantsDualEquiv ρ).finrank_eq.trans Subspace.dual_finrank_eq

/-- The exact prime-character endpoint on the original action. Apply
this to M.toRepresentation to retain M's intrinsic coinvariants. -/
theorem representationCharacterHead_finrank_eq_coinvariants
    {p : ℕ} [Fact p.Prime] {G₀ V₀ : Type*} [Group G₀]
    [AddCommGroup V₀] [Module (ZMod p) V₀] [FiniteDimensional (ZMod p) V₀]
    (ρ : Representation (ZMod p) G₀ V₀) :
    Module.finrank (ZMod p) (primeActionCharacters p (representationGroupAction ρ)) =
      Module.finrank (ZMod p) ρ.Coinvariants :=
  (representationCharacterHeadEquiv ρ).finrank_eq.trans
    (representationHead_finrank_eq_coinvariants ρ)

end SymmetricSubgroupAsymptotics
