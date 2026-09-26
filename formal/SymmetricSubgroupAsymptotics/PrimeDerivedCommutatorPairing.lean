import SymmetricSubgroupAsymptotics.PrimeRetainedCommutatorHead
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.Algebra.Group.Hom.Instances
import Mathlib.Algebra.Module.ZMod

/-! Every whole-ambient invariant character of the actual derived subgroup
gives an alternating pairing on the actual abelianization. Its values are
the original commutators, not a chosen extension or an abstract group model.
An elementary abelianization can therefore be given matrix coordinates
without replacing the retained-character obstruction.
-/
set_option autoImplicit false
noncomputable section
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics

variable {G : Type*} [Group G]

/-- An original commutator with its literal membership in G'. -/
def derivedCommutatorElement (a b : G) : commutator G :=
  ⟨⁅a,b⁆, Subgroup.commutator_mem_commutator
    (Subgroup.mem_top a) (Subgroup.mem_top b)⟩

private theorem derivedCommutatorElement_mul_left (a b c : G) :
    derivedCommutatorElement (a*b) c =
      MulAut.conjNormal a (derivedCommutatorElement b c) *
        derivedCommutatorElement a c :=
  Subtype.ext (commutatorElement_mul_left_eq_conj_mul a b c)

private theorem derivedCommutatorElement_mul_right (a b c : G) :
    derivedCommutatorElement a (b*c) =
      derivedCommutatorElement a b *
        MulAut.conjNormal b (derivedCommutatorElement a c) := by
  apply Subtype.ext
  change ⁅a,b*c⁆ = ⁅a,b⁆ * (b * ⁅a,c⁆ * b⁻¹)
  rw [commutatorElement_mul_right_eq_mul_conj]
  simp only [mul_assoc]

variable (p : ℕ) [Fact p.Prime]

/-- Evaluate the same invariant derived character on the original pair. -/
def derivedCharacterCommutator
    (χ : primeRelativeCharacters p (commutator G)) (a b : G) : ZMod p :=
  χ.1 (Additive.ofMul (derivedCommutatorElement a b))

theorem derivedCharacterCommutator_one_left
    (χ : primeRelativeCharacters p (commutator G)) (b : G) :
    derivedCharacterCommutator p χ 1 b = 0 := by
  have he : derivedCommutatorElement (1 : G) b = 1 :=
    Subtype.ext (commutatorElement_one_left b)
  unfold derivedCharacterCommutator
  rw [he]
  exact χ.1.map_zero

theorem derivedCharacterCommutator_one_right
    (χ : primeRelativeCharacters p (commutator G)) (a : G) :
    derivedCharacterCommutator p χ a 1 = 0 := by
  have he : derivedCommutatorElement a (1 : G) = 1 :=
    Subtype.ext (commutatorElement_one_right a)
  unfold derivedCharacterCommutator
  rw [he]
  exact χ.1.map_zero

theorem derivedCharacterCommutator_mul_left
    (χ : primeRelativeCharacters p (commutator G)) (a b c : G) :
    derivedCharacterCommutator p χ (a*b) c =
      derivedCharacterCommutator p χ a c + derivedCharacterCommutator p χ b c := by
  unfold derivedCharacterCommutator
  rw [derivedCommutatorElement_mul_left]
  change χ.1 (Additive.ofMul (MulAut.conjNormal a (derivedCommutatorElement b c)) +
    Additive.ofMul (derivedCommutatorElement a c)) = _
  have hc : χ.1 (Additive.ofMul (MulAut.conjNormal a (derivedCommutatorElement b c))) =
      χ.1 (Additive.ofMul (derivedCommutatorElement b c)) :=
    χ.2 a (derivedCommutatorElement b c)
  rw [map_add, hc, add_comm]

theorem derivedCharacterCommutator_mul_right
    (χ : primeRelativeCharacters p (commutator G)) (a b c : G) :
    derivedCharacterCommutator p χ a (b*c) =
      derivedCharacterCommutator p χ a b + derivedCharacterCommutator p χ a c := by
  unfold derivedCharacterCommutator
  rw [derivedCommutatorElement_mul_right]
  change χ.1 (Additive.ofMul (derivedCommutatorElement a b) +
    Additive.ofMul (MulAut.conjNormal b (derivedCommutatorElement a c))) = _
  have hc : χ.1 (Additive.ofMul (MulAut.conjNormal b (derivedCommutatorElement a c))) =
      χ.1 (Additive.ofMul (derivedCommutatorElement a c)) :=
    χ.2 b (derivedCommutatorElement a c)
  rw [map_add, hc]

theorem derivedCharacterCommutator_self
    (χ : primeRelativeCharacters p (commutator G)) (a : G) :
    derivedCharacterCommutator p χ a a = 0 := by
  have he : derivedCommutatorElement a a = 1 := Subtype.ext (commutatorElement_self a)
  unfold derivedCharacterCommutator
  rw [he]
  exact χ.1.map_zero

/-- The second-variable homomorphism uses whole-G invariance of χ. -/
def derivedCharacterCommutatorRight
    (χ : primeRelativeCharacters p (commutator G)) (a : G) :
    G →* Multiplicative (ZMod p) where
  toFun b := Multiplicative.ofAdd (derivedCharacterCommutator p χ a b)
  map_one' := derivedCharacterCommutator_one_right p χ a
  map_mul' b c := derivedCharacterCommutator_mul_right p χ a b c

/-- Factor the second variable through the actual abelianization, then
use first-variable additivity to obtain the outer homomorphism. -/
def derivedCharacterCommutatorToAbelianization
    (χ : primeRelativeCharacters p (commutator G)) :
    G →* (Abelianization G →* Multiplicative (ZMod p)) where
  toFun a := Abelianization.lift (derivedCharacterCommutatorRight p χ a)
  map_one' := by
    apply Abelianization.hom_ext
    ext b
    exact derivedCharacterCommutator_one_left p χ b
  map_mul' a b := by
    apply Abelianization.hom_ext
    ext c
    exact derivedCharacterCommutator_mul_left p χ a b c

/-- The actual alternating pairing, packaged additively through the
multiplicative type tag. Both arguments are literally G/G'. -/
def derivedCharacterPairing
    (χ : primeRelativeCharacters p (commutator G)) :
    Abelianization G →* (Abelianization G →* Multiplicative (ZMod p)) :=
  Abelianization.lift (derivedCharacterCommutatorToAbelianization p χ)

@[simp] theorem derivedCharacterPairing_of
    (χ : primeRelativeCharacters p (commutator G)) (a b : G) :
    derivedCharacterPairing p χ (Abelianization.of a) (Abelianization.of b) =
      Multiplicative.ofAdd (derivedCharacterCommutator p χ a b) := rfl

theorem derivedCharacterPairing_self
    (χ : primeRelativeCharacters p (commutator G)) (a : Abelianization G) :
    derivedCharacterPairing p χ a a = 1 := by
  refine QuotientGroup.induction_on a ?_
  intro g
  exact derivedCharacterCommutator_self p χ g

/-- An explicit additive version, convertible to a linear map whenever
the actual abelianization has its prime-field module structure. -/
def derivedCharacterPairingAdd
    (χ : primeRelativeCharacters p (commutator G)) (a : Additive (Abelianization G)) :
    Additive (Abelianization G) →+ ZMod p where
  toFun b := (derivedCharacterPairing p χ a.toMul b.toMul).toAdd
  map_zero' := congrArg Multiplicative.toAdd (map_one (derivedCharacterPairing p χ a.toMul))
  map_add' b c := congrArg Multiplicative.toAdd
    (map_mul (derivedCharacterPairing p χ a.toMul) b.toMul c.toMul)

/-- Matrix consumers may install the canonical elementary-abelian module
on G/G'. No choice of basis or assertion of its dimension is hidden here. -/
def derivedCharacterBilinear
    [Module (ZMod p) (Additive (Abelianization G))]
    (χ : primeRelativeCharacters p (commutator G)) :
    Additive (Abelianization G) →ₗ[ZMod p]
      Additive (Abelianization G) →ₗ[ZMod p] ZMod p :=
  AddMonoidHom.toZModLinearMap p {
    toFun := fun a => (derivedCharacterPairingAdd p χ a).toZModLinearMap p
    map_zero' := by
      ext b
      change (derivedCharacterPairing p χ 1 b.toMul).toAdd = 0
      rw [map_one]
      rfl
    map_add' := by
      intro a b
      ext c
      change (derivedCharacterPairing p χ (a.toMul*b.toMul) c.toMul).toAdd = _
      rw [map_mul]
      rfl }

@[simp] theorem derivedCharacterBilinear_of
    [Module (ZMod p) (Additive (Abelianization G))]
    (χ : primeRelativeCharacters p (commutator G)) (a b : G) :
    derivedCharacterBilinear p χ
      (Additive.ofMul (Abelianization.of a))
      (Additive.ofMul (Abelianization.of b)) = derivedCharacterCommutator p χ a b := rfl

theorem derivedCharacterBilinear_self
    [Module (ZMod p) (Additive (Abelianization G))]
    (χ : primeRelativeCharacters p (commutator G)) (a : Additive (Abelianization G)) :
    derivedCharacterBilinear p χ a a = 0 :=
  congrArg Multiplicative.toAdd (derivedCharacterPairing_self p χ a.toMul)

/-- The family of forms is linear in the actual invariant character. -/
def derivedCharacterBilinearMap
    [Module (ZMod p) (Additive (Abelianization G))] :
    primeRelativeCharacters p (commutator G) →ₗ[ZMod p]
      Additive (Abelianization G) →ₗ[ZMod p]
        Additive (Abelianization G) →ₗ[ZMod p] ZMod p where
  toFun := derivedCharacterBilinear p
  map_add' χ ψ := by
    ext a b
    change (derivedCharacterPairing p (χ+ψ) a.toMul b.toMul).toAdd =
      (derivedCharacterPairing p χ a.toMul b.toMul).toAdd +
        (derivedCharacterPairing p ψ a.toMul b.toMul).toAdd
    refine QuotientGroup.induction_on a.toMul ?_
    intro g
    refine QuotientGroup.induction_on b.toMul ?_
    intro h
    rfl
  map_smul' c χ := by
    ext a b
    change (derivedCharacterPairing p (c • χ) a.toMul b.toMul).toAdd =
      c • (derivedCharacterPairing p χ a.toMul b.toMul).toAdd
    refine QuotientGroup.induction_on a.toMul ?_
    intro g
    refine QuotientGroup.induction_on b.toMul ?_
    intro h
    rfl

/-- The same character in the actual retained image vanishes on every
row from N and every original ambient column of this pairing. -/
theorem retained_derivedCharacterPairing_eq_one
    (N : Subgroup G) [N.Normal] (hDN : commutator G ≤ N)
    (χ : primeRelativeCharacters p (commutator G))
    (hχ : χ ∈ normalChainRetainedCharacters (commutator G) N p hDN)
    (n : N) (g : G) :
    derivedCharacterPairing p χ (Abelianization.of (n : G)) (Abelianization.of g) = 1 := by
  have hz := normalChainRetainedCharacters_le_mixedAnnihilator
    (commutator G) N p hDN (Subgroup.commutator_mono le_top le_rfl) hχ n g
  exact hz

theorem retained_derivedCharacterBilinear_eq_zero
    [Module (ZMod p) (Additive (Abelianization G))]
    (N : Subgroup G) [N.Normal] (hDN : commutator G ≤ N)
    (χ : primeRelativeCharacters p (commutator G))
    (hχ : χ ∈ normalChainRetainedCharacters (commutator G) N p hDN)
    (n : N) (g : G) :
    derivedCharacterBilinear p χ (Additive.ofMul (Abelianization.of (n : G)))
      (Additive.ofMul (Abelianization.of g)) = 0 :=
  congrArg Multiplicative.toAdd (retained_derivedCharacterPairing_eq_one p N hDN χ hχ n g)

end SymmetricSubgroupAsymptotics
