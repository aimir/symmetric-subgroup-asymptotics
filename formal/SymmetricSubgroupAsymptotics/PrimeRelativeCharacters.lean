import SymmetricSubgroupAsymptotics.PrimeAbelianization
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Relative prime heads, with the actual extension obstruction retained.
For an arbitrary onto map of finite groups, restriction of characters lands
in the original conjugation-invariant character space of its literal kernel.
Its image consists precisely of the characters that actually extend. The
rank identity retains this image, rather than replacing it by all invariant
characters (which would discard the transgression obstruction). -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
variable (p : ℕ) [Fact p.Prime]
variable {G H : Type*} [Group G] [Group H]

def primeCharacterInflation (π : G →* H) :
    PrimeCharacters p H →ₗ[ZMod p] PrimeCharacters p G where
  toFun χ := χ.comp π.toAdditive
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem primeCharacterInflation_injective (π : G →* H)
    (hπ : Function.Surjective π) : Function.Injective (primeCharacterInflation p π) := by
  intro χ ψ he
  ext y
  obtain ⟨x,rfl⟩ := hπ y
  exact DFunLike.congr_fun he (Additive.ofMul x)

/-- Original group isomorphisms transport complete character spaces. -/
def primeCharacterCongr (e : G ≃* H) :
    PrimeCharacters p H ≃ₗ[ZMod p] PrimeCharacters p G :=
  LinearEquiv.ofBijective (primeCharacterInflation p e.toMonoidHom)
    ⟨primeCharacterInflation_injective p e.toMonoidHom e.surjective,by
      intro χ
      refine ⟨χ.comp e.symm.toMonoidHom.toAdditive,?_⟩
      ext x
      change χ (Additive.ofMul (e.symm (e x)))=χ (Additive.ofMul x)
      rw [e.symm_apply_apply]⟩

theorem primeCharacter_finrank_congr (e : G ≃* H) :
    Module.finrank (ZMod p) (PrimeCharacters p G) =
      Module.finrank (ZMod p) (PrimeCharacters p H) :=
  (primeCharacterCongr p e).finrank_eq.symm

/-- Relative characters use the actual ambient conjugation action. -/
def primeRelativeCharacters (N : Subgroup G) [N.Normal] :
    Submodule (ZMod p) (PrimeCharacters p N) where
  carrier := {χ | ∀ g : G, ∀ n : N,
    χ (Additive.ofMul (⟨g*(n:G)*g⁻¹,Subgroup.Normal.conj_mem inferInstance _ n.2 g⟩:N)) =
      χ (Additive.ofMul n)}
  zero_mem' := by intro g n; rfl
  add_mem' := by intro χ ψ hχ hψ g n; exact congrArg₂ (·+·) (hχ g n) (hψ g n)
  smul_mem' := by intro c χ hχ g n; exact congrArg (c • ·) (hχ g n)

/-- Original restriction lands in the relative, not absolute, kernel head. -/
def primeCharacterRestriction (N : Subgroup G) [N.Normal] :
    PrimeCharacters p G →ₗ[ZMod p] primeRelativeCharacters p N where
  toFun χ := ⟨χ.comp N.subtype.toAdditive,by
    intro g n
    change χ ((Additive.ofMul g+Additive.ofMul (n:G)) + -Additive.ofMul g) =
      χ (Additive.ofMul (n:G))
    simp only [map_add,map_neg]
    abel⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- This is the actual retained annihilator of extension obstructions:
an invariant kernel character belongs iff an original character extends it. -/
def primeExtendibleRelativeCharacters (π : G →* H) :
    Submodule (ZMod p) (primeRelativeCharacters p π.ker) :=
  LinearMap.range (primeCharacterRestriction p π.ker)

theorem primeExtendibleRelativeCharacters_mem_iff (π : G →* H)
    (χ : primeRelativeCharacters p π.ker) :
    χ ∈ primeExtendibleRelativeCharacters p π ↔
      ∃ ψ : PrimeCharacters p G, ∀ n : π.ker,
        ψ (Additive.ofMul (n:G)) = χ.1 (Additive.ofMul n) := by
  constructor
  · rintro ⟨ψ,hψ⟩
    refine ⟨ψ,fun n => ?_⟩
    exact DFunLike.congr_fun (congrArg Subtype.val hψ) (Additive.ofMul n)
  · rintro ⟨ψ,hψ⟩
    refine ⟨ψ,Subtype.ext ?_⟩
    ext n
    exact hψ n

/-- Exactness holds for every original extension, including nonsplit and
nonabelian kernels. Surjectivity of restriction is not assumed. -/
theorem primeCharacterRestriction_ker (π : G →* H) (hπ : Function.Surjective π) :
    LinearMap.ker (primeCharacterRestriction p π.ker) =
      LinearMap.range (primeCharacterInflation p π) := by
  ext χ
  constructor
  · intro hχ
    have hz : ∀ x : G, x∈π.ker → χ (Additive.ofMul x)=0 := by
      intro x hx
      have he := congrArg Subtype.val (LinearMap.mem_ker.mp hχ)
      exact DFunLike.congr_fun he (Additive.ofMul (⟨x,hx⟩:π.ker))
    have hs : Function.Surjective π.toAdditive := hπ
    let ψ := π.toAdditive.liftOfSurjective hs ⟨χ,fun x hx => hz x.toMul hx⟩
    refine ⟨ψ,?_⟩
    ext x
    exact AddMonoidHom.liftOfRightInverse_comp_apply π.toAdditive
      (Function.surjInv hs) (Function.rightInverse_surjInv hs)
      ⟨χ,fun x hx => hz x.toMul hx⟩ x
  · rintro ⟨ψ,rfl⟩
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    ext n
    change ψ (Additive.ofMul (π (n:G)))=0
    rw [show π (n:G)=1 from n.2]
    exact ψ.map_zero

/-- Exact rank decomposition retains the actual extendible subspace. -/
theorem primeCharacterRank_extension_eq [Finite G] [Finite H]
    (π : G →* H) (hπ : Function.Surjective π) :
    Module.finrank (ZMod p) (PrimeCharacters p G) =
      Module.finrank (ZMod p) (PrimeCharacters p H) +
        Module.finrank (ZMod p) (primeExtendibleRelativeCharacters p π) := by
  have h := (primeCharacterRestriction p π.ker).finrank_range_add_finrank_ker
  rw [primeCharacterRestriction_ker p π hπ,
    LinearMap.finrank_range_of_inj (primeCharacterInflation_injective p π hπ)] at h
  exact h.symm.trans (Nat.add_comm _ _)

/-- The coarse relative-head inequality follows only after the retained
annihilator has been identified. -/
theorem primeCharacterRank_extension_le [Finite G] [Finite H]
    (π : G →* H) (hπ : Function.Surjective π) :
    Module.finrank (ZMod p) (PrimeCharacters p G) ≤
      Module.finrank (ZMod p) (PrimeCharacters p H) +
        Module.finrank (ZMod p) (primeRelativeCharacters p π.ker) := by
  rw [primeCharacterRank_extension_eq p π hπ]
  exact Nat.add_le_add_left (Submodule.finrank_le _) _

end SymmetricSubgroupAsymptotics
