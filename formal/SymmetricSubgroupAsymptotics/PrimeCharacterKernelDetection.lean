import SymmetricSubgroupAsymptotics.PrimeCharacterKernelOrbits

/-! Exact double-annihilator detection for a retained subspace of the
original scalar characters. The kernel is the actual common group kernel,
not a selected generating subset or an abstract quotient replacement. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime] {G : Type*} [Group G] [Finite G]

/-- Named original character inclusion. Its explicit type prevents
repeated inference through the submodule and character-group instances. -/
def primeCharacterSubspaceEmbedding
    (W : Submodule (ZMod p) (PrimeCharacters p G)) : W →ₗ[ZMod p] PrimeCharacters p G where
  toFun := Subtype.val
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

theorem primeCharacterSubspaceEmbedding_injective
    (W : Submodule (ZMod p) (PrimeCharacters p G)) :
    Function.Injective (primeCharacterSubspaceEmbedding p (G := G) W) :=
  Subtype.val_injective

theorem primeCharacter_mem_iff_vanishes_retained_kernel
    (W : Submodule (ZMod p) (PrimeCharacters p G)) (χ : PrimeCharacters p G) :
    χ ∈ W ↔ ∀ g : G, g ∈ (retainedCharacterEvaluation p (G := G) (V := W)
      (primeCharacterSubspaceEmbedding p (G := G) W)).ker →
      χ (Additive.ofMul g)=0 := by
  constructor
  · intro hχ g hg
    exact (mem_retainedCharacterEvaluation_ker_iff p (G := G) (V := W)
      (primeCharacterSubspaceEmbedding p (G := G) W) g).mp hg ⟨χ,hχ⟩
  · intro hχ
    apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff W χ).mp
    intro ℓ hℓ
    obtain ⟨g,rfl⟩ := primeAbelianizationMap_surjective p G ℓ
    apply hχ g.toMul
    apply (mem_retainedCharacterEvaluation_ker_iff p (G := G) (V := W)
      (primeCharacterSubspaceEmbedding p (G := G) W) g.toMul).mpr
    intro ψ
    exact (Submodule.mem_dualAnnihilator _).mp hℓ ψ.val ψ.property

end SymmetricSubgroupAsymptotics
