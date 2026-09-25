import SymmetricSubgroupAsymptotics.PrimeRelativeCharacters

/-! Exact invariant-character restriction in an arbitrary compatible
equivariant extension. The actual extendible restriction image is retained;
there is no assumption of a split extension or of surjective restriction. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
variable (p : ℕ) [Fact p.Prime]
variable {A G H : Type*} [Group A] [Group G] [Group H]

def primeActionCharacters (ρ : A →* MulAut G) :
    Submodule (ZMod p) (PrimeCharacters p G) where
  carrier := {χ | ∀ a : A, ∀ g : G, χ (Additive.ofMul (ρ a g))=χ (Additive.ofMul g)}
  zero_mem' := by intro a g; rfl
  add_mem' := by intro χ ψ hχ hψ a g; exact congrArg₂ (·+·) (hχ a g) (hψ a g)
  smul_mem' := by intro c χ hχ a g; exact congrArg (c • ·) (hχ a g)

variable (π : G →* H) (ρ : A →* MulAut G) (σ : A →* MulAut H)
variable (heq : ∀ a g,π (ρ a g)=σ a (π g))

def primeActionKernelCharacters : Submodule (ZMod p) (PrimeCharacters p π.ker) where
  carrier := {χ | ∀ a : A, ∀ g : π.ker,
    χ (Additive.ofMul (⟨ρ a (g:G),by
      change π (ρ a (g:G))=1
      rw [heq,g.2,map_one]⟩:π.ker)) =
      χ (Additive.ofMul g)}
  zero_mem' := by intro a g; rfl
  add_mem' := by intro χ ψ hχ hψ a g; exact congrArg₂ (·+·) (hχ a g) (hψ a g)
  smul_mem' := by intro c χ hχ a g; exact congrArg (c • ·) (hχ a g)

def primeActionInflation : primeActionCharacters p σ →ₗ[ZMod p] primeActionCharacters p ρ where
  toFun χ := ⟨primeCharacterInflation p π χ.1,by
    intro a g
    change χ.1 (Additive.ofMul (π (ρ a g)))=χ.1 (Additive.ofMul (π g))
    rw [heq]
    exact χ.2 a (π g)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem primeActionInflation_injective (hπ : Function.Surjective π) :
    Function.Injective (primeActionInflation p π ρ σ heq) := by
  intro χ ψ h
  apply Subtype.ext
  exact primeCharacterInflation_injective p π hπ (congrArg Subtype.val h)

def primeActionRestriction : primeActionCharacters p ρ →ₗ[ZMod p]
    primeActionKernelCharacters p π ρ σ heq where
  toFun χ := ⟨χ.1.comp π.ker.subtype.toAdditive,by
    intro a g
    exact χ.2 a (g:G)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def primeActionExtendibleCharacters :
    Submodule (ZMod p) (primeActionKernelCharacters p π ρ σ heq) :=
  LinearMap.range (primeActionRestriction p π ρ σ heq)

theorem primeActionRestriction_ker (hπ : Function.Surjective π) :
    LinearMap.ker (primeActionRestriction p π ρ σ heq)=
      LinearMap.range (primeActionInflation p π ρ σ heq) := by
  ext χ
  constructor
  · intro hχ
    have hz : χ.1∈LinearMap.ker (primeCharacterRestriction p π.ker) := by
      apply LinearMap.mem_ker.mpr
      apply Subtype.ext
      have hχ0 : primeActionRestriction p π ρ σ heq χ=0 := LinearMap.mem_ker.mp hχ
      have h0 := congrArg (fun z : primeActionKernelCharacters p π ρ σ heq =>
        (z:PrimeCharacters p π.ker)) hχ0
      exact h0
    rw [primeCharacterRestriction_ker p π hπ] at hz
    obtain ⟨ψ,hψ⟩ := hz
    have hψinv : ψ∈primeActionCharacters p σ := by
      intro a y
      obtain ⟨x,rfl⟩ := hπ y
      have h1 := DFunLike.congr_fun hψ (Additive.ofMul (ρ a x))
      have h2 := DFunLike.congr_fun hψ (Additive.ofMul x)
      change ψ (Additive.ofMul (σ a (π x)))=ψ (Additive.ofMul (π x))
      rw [← heq]
      exact h1.trans ((χ.2 a x).trans h2.symm)
    exact ⟨⟨ψ,hψinv⟩,Subtype.ext hψ⟩
  · rintro ⟨ψ,rfl⟩
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    ext g
    change ψ.1 (Additive.ofMul (π (g:G)))=0
    rw [show π (g:G)=1 from g.2]
    exact ψ.1.map_zero

theorem primeActionCharacterRank_extension_eq [Finite G] [Finite H]
    (hπ : Function.Surjective π) :
    Module.finrank (ZMod p) (primeActionCharacters p ρ)=
      Module.finrank (ZMod p) (primeActionCharacters p σ) +
        Module.finrank (ZMod p) (primeActionExtendibleCharacters p π ρ σ heq) := by
  have h := (primeActionRestriction p π ρ σ heq).finrank_range_add_finrank_ker
  rw [primeActionRestriction_ker p π ρ σ heq hπ,
    LinearMap.finrank_range_of_inj (primeActionInflation_injective p π ρ σ heq hπ)] at h
  exact h.symm.trans (Nat.add_comm _ _)

theorem primeActionCharacterRank_extension_le [Finite G] [Finite H]
    (hπ : Function.Surjective π) :
    Module.finrank (ZMod p) (primeActionCharacters p ρ)≤
      Module.finrank (ZMod p) (primeActionCharacters p σ) +
        Module.finrank (ZMod p) (primeActionKernelCharacters p π ρ σ heq) := by
  rw [primeActionCharacterRank_extension_eq p π ρ σ heq hπ]
  exact Nat.add_le_add_left (Submodule.finrank_le _) _

end SymmetricSubgroupAsymptotics
