import SymmetricSubgroupAsymptotics.CharacterDualityImports

/-!
# The actual maximal elementary prime quotient

Evaluation on all prime-field characters gives an explicit vector-space
model of the elementary quotient. All original group homomorphisms into
prime-field modules factor uniquely through this actual surjection.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime] (G : Type*) [Group G]

abbrev PrimeCharacters := Additive G →+ ZMod p

instance [Finite G] : Finite (PrimeCharacters p G) :=
  Finite.of_injective (fun f : PrimeCharacters p G => (f : Additive G → ZMod p))
    DFunLike.coe_injective

/-- The dual of the actual scalar-character space. -/
abbrev PrimeAbelianization := Module.Dual (ZMod p) (PrimeCharacters p G)

instance [Finite G] : Finite (PrimeAbelianization p G) :=
  Finite.of_injective (fun f : PrimeAbelianization p G =>
    (f : PrimeCharacters p G → ZMod p)) DFunLike.coe_injective

def primeAbelianizationMap : Additive G →+ PrimeAbelianization p G where
  toFun g :=
    { toFun := fun χ => χ g
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_zero' := by ext χ; exact χ.map_zero
  map_add' := by intro x y; ext χ; exact χ.map_add x y

@[simp] theorem primeAbelianizationMap_apply (g : Additive G) (χ : PrimeCharacters p G) :
    primeAbelianizationMap p G g χ = χ g := rfl

theorem primeAbelianizationMap_surjective [Finite G] :
    Function.Surjective (primeAbelianizationMap p G) := by
  let S : Submodule (ZMod p) (PrimeAbelianization p G) :=
    (primeAbelianizationMap p G).range.toZModSubmodule p
  have hS : S = ⊤ := by
    apply Submodule.dualAnnihilator_eq_bot_iff.mp
    apply bot_unique
    intro ℓ hℓ
    obtain ⟨χ,rfl⟩ := (Module.evalEquiv (ZMod p) (PrimeCharacters p G)).surjective ℓ
    have hχ : χ = 0 := by
      ext g
      exact (Submodule.mem_dualAnnihilator _).mp hℓ
        (primeAbelianizationMap p G g) ⟨g,rfl⟩
    simp [hχ]
  intro x
  have hx : x ∈ S := by rw [hS]; trivial
  exact hx

variable {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

def primeCharacterPullback (f : Additive G →+ V) :
    Module.Dual (ZMod p) V →ₗ[ZMod p] PrimeCharacters p G where
  toFun ℓ := ℓ.toAddMonoidHom.comp f
  map_add' := by intro a b; ext g; rfl
  map_smul' := by intro a b; ext g; rfl

def primeAbelianizationLift [Finite V] (f : Additive G →+ V) :
    PrimeAbelianization p G →ₗ[ZMod p] V :=
  (Module.evalEquiv (ZMod p) V).symm.toLinearMap.comp (primeCharacterPullback p G f).dualMap

@[simp] theorem primeAbelianizationLift_apply [Finite V]
    (f : Additive G →+ V) (g : Additive G) :
    primeAbelianizationLift p G f (primeAbelianizationMap p G g) = f g := by
  apply (Module.evalEquiv (ZMod p) V).injective
  ext ℓ
  simp [primeAbelianizationLift,primeCharacterPullback,LinearMap.dualMap_apply]

/-- Unique factorization retains every original homomorphism. -/
def primeAbelianizationHomEquiv [Finite G] [Finite V] :
    (Additive G →+ V) ≃ (PrimeAbelianization p G →ₗ[ZMod p] V) where
  toFun := primeAbelianizationLift p G
  invFun f := f.toAddMonoidHom.comp (primeAbelianizationMap p G)
  left_inv f := by ext g; exact primeAbelianizationLift_apply p G f g
  right_inv f := by
    ext x
    obtain ⟨g,rfl⟩ := primeAbelianizationMap_surjective p G x
    exact primeAbelianizationLift_apply p G _ g

/-- Multiplicative form of the literal elementary quotient map. -/
def primeAbelianizationGroupMap : G →* Multiplicative (PrimeAbelianization p G) :=
  AddMonoidHom.toMultiplicativeRight (primeAbelianizationMap p G)

theorem primeAbelianizationGroupMap_surjective [Finite G] :
    Function.Surjective (primeAbelianizationGroupMap p G) :=
  primeAbelianizationMap_surjective p G

section Functor

variable {G} {H L : Type*} [Group H] [Group L]

/-- The induced map is functorial in the actual group homomorphism. -/
def primeAbelianizationMapHom [Finite H] (f : G →* H) :
    PrimeAbelianization p G →ₗ[ZMod p] PrimeAbelianization p H :=
  primeAbelianizationLift p G
    ((primeAbelianizationMap p H).comp f.toAdditive)

@[simp] theorem primeAbelianizationMapHom_apply [Finite H] (f : G →* H) (x : G) :
    primeAbelianizationMapHom p f (primeAbelianizationMap p G (Additive.ofMul x)) =
      primeAbelianizationMap p H (Additive.ofMul (f x)) :=
  primeAbelianizationLift_apply p G _ _

@[simp] theorem primeAbelianizationMapHom_id [Finite G] :
    primeAbelianizationMapHom p (MonoidHom.id G) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  obtain ⟨g,rfl⟩ := primeAbelianizationMap_surjective p G x
  exact primeAbelianizationMapHom_apply p (MonoidHom.id G) g.toMul

theorem primeAbelianizationMapHom_comp [Finite G] [Finite H] [Finite L]
    (f : G →* H) (g : H →* L) :
    primeAbelianizationMapHom p (g.comp f) =
      (primeAbelianizationMapHom p g).comp (primeAbelianizationMapHom p f) := by
  apply LinearMap.ext
  intro x
  obtain ⟨t,rfl⟩ := primeAbelianizationMap_surjective p G x
  change primeAbelianizationMapHom p (g.comp f) (primeAbelianizationMap p G t) =
    primeAbelianizationMapHom p g (primeAbelianizationMapHom p f (primeAbelianizationMap p G t))
  simp only [primeAbelianizationMapHom,primeAbelianizationLift_apply,
    AddMonoidHom.comp_apply]
  rfl

end Functor

end SymmetricSubgroupAsymptotics
