import SymmetricSubgroupAsymptotics.ComplementCount
import Mathlib.Algebra.Module.ZMod

/-!
# The universal elementary binary quotient through its characters

The dual of the actual binary character space is a canonical realization of
the maximal elementary binary quotient of a finite group. Evaluation is onto,
and every homomorphism to a finite binary vector space factors uniquely through
it. This supplies the terminal graph source and its exact character exponent.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable (T : Type*) [Group T]

/-- Literal binary characters, with pointwise vector-space operations. -/
abbrev BinaryCharacters := Additive T →+ ZMod 2

instance [Finite T] : Finite (BinaryCharacters T) :=
  Finite.of_injective (fun f : BinaryCharacters T ↦ (f : Additive T → ZMod 2))
    DFunLike.coe_injective

/-- A canonical model for A₂(T), without a choice of basis or characters. -/
abbrev BinaryAbelianization := Module.Dual (ZMod 2) (BinaryCharacters T)

instance [Finite T] : Finite (BinaryAbelianization T) :=
  Finite.of_injective (fun f : BinaryAbelianization T ↦
    (f : BinaryCharacters T → ZMod 2)) DFunLike.coe_injective

/-- Evaluation on all actual characters. -/
def binaryAbelianizationMap : Additive T →+ BinaryAbelianization T where
  toFun t :=
    { toFun := fun χ ↦ χ t
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  map_zero' := by ext χ; exact χ.map_zero
  map_add' := by intro t u; ext χ; exact χ.map_add t u

@[simp] theorem binaryAbelianizationMap_apply (t : Additive T) (χ : BinaryCharacters T) :
    binaryAbelianizationMap T t χ = χ t := rfl

/-- Finite character duality proves that evaluation is an actual quotient,
not merely an injection into a space of formal coordinates. -/
theorem binaryAbelianizationMap_surjective [Finite T] :
    Function.Surjective (binaryAbelianizationMap T) := by
  let R : Submodule (ZMod 2) (BinaryAbelianization T) :=
    (binaryAbelianizationMap T).range.toZModSubmodule 2
  have hR : R = ⊤ := by
    apply Submodule.dualAnnihilator_eq_bot_iff.mp
    apply bot_unique
    intro ℓ hℓ
    obtain ⟨χ,rfl⟩ := (Module.evalEquiv (ZMod 2) (BinaryCharacters T)).surjective ℓ
    have hχ : χ = 0 := by
      ext t
      have h := (Submodule.mem_dualAnnihilator _).mp hℓ
        (binaryAbelianizationMap T t) (show binaryAbelianizationMap T t ∈ R from ⟨t,rfl⟩)
      exact h
    simp [hχ]
  intro x
  have hx : x ∈ R := by rw [hR]; trivial
  exact hx

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- Pullback of scalar characters along an actual map. -/
def binaryCharacterPullback (f : Additive T →+ V) :
    Module.Dual (ZMod 2) V →ₗ[ZMod 2] BinaryCharacters T where
  toFun ℓ := ℓ.toAddMonoidHom.comp f
  map_add' := by intro a b; ext t; rfl
  map_smul' := by intro a b; ext t; rfl

/-- Universal factor map, constructed by finite-dimensional duality. -/
def binaryAbelianizationLift [Finite V] (f : Additive T →+ V) :
    BinaryAbelianization T →ₗ[ZMod 2] V :=
  (Module.evalEquiv (ZMod 2) V).symm.toLinearMap.comp (binaryCharacterPullback T f).dualMap

@[simp] theorem binaryAbelianizationLift_apply [Finite V]
    (f : Additive T →+ V) (t : Additive T) :
    binaryAbelianizationLift T f (binaryAbelianizationMap T t) = f t := by
  apply (Module.evalEquiv (ZMod 2) V).injective
  ext ℓ
  simp [binaryAbelianizationLift, binaryCharacterPullback, LinearMap.dualMap_apply]

/-- All actual maps into a binary vector space, with no quotient by conjugacy
or by coboundaries. -/
def binaryAbelianizationHomEquiv [Finite T] [Finite V] :
    (Additive T →+ V) ≃ (BinaryAbelianization T →ₗ[ZMod 2] V) where
  toFun := binaryAbelianizationLift T
  invFun f := f.toAddMonoidHom.comp (binaryAbelianizationMap T)
  left_inv f := by ext t; exact binaryAbelianizationLift_apply T f t
  right_inv f := by
    ext x
    obtain ⟨t,rfl⟩ := binaryAbelianizationMap_surjective T x
    exact binaryAbelianizationLift_apply T _ t

/-- The same universal property in multiplicative group notation. -/
def binaryAbelianizationGroupHomEquiv [Finite T] [Finite V] :
    (T →* Multiplicative V) ≃ (BinaryAbelianization T →ₗ[ZMod 2] V) :=
  AddMonoidHom.toMultiplicativeRight.symm.trans (binaryAbelianizationHomEquiv T)

/-- The exact binary character rank of the whole group. -/
def binaryCharacterRank : ℕ := Module.finrank (ZMod 2) (BinaryCharacters T)

theorem binaryAbelianization_finrank [Finite T] :
    Module.finrank (ZMod 2) (BinaryAbelianization T) = binaryCharacterRank T := by
  exact Subspace.dual_finrank_eq

theorem binaryAbelianizationHom_card [Finite T] [Finite V] :
    Nat.card (Additive T →+ V) =
      2 ^ (binaryCharacterRank T * Module.finrank (ZMod 2) V) := by
  rw [Nat.card_congr (binaryAbelianizationHomEquiv T),
    Module.natCard_eq_pow_finrank (K := ZMod 2), Module.finrank_linearMap,
    binaryAbelianization_finrank]
  simp

theorem binaryAbelianizationGroupHom_card [Finite T] [Finite V] :
    Nat.card (T →* Multiplicative V) =
      2 ^ (binaryCharacterRank T * Module.finrank (ZMod 2) V) := by
  rw [Nat.card_congr AddMonoidHom.toMultiplicativeRight.symm]
  exact binaryAbelianizationHom_card T

end SymmetricSubgroupAsymptotics
