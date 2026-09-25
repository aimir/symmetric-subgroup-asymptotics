import SymmetricSubgroupAsymptotics.PrimeRelativeHeadChain
import Mathlib.GroupTheory.IsPerfect
import Mathlib.GroupTheory.PGroup

/-! Perfect layers and layers of coprime prime-power exponent have zero
relative prime head. These are exact vanishing statements for characters,
not capacity-loss statements for arbitrary modules with odd-order action. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
variable (p : ℕ) [Fact p.Prime]
variable {G : Type*} [Group G]

theorem primeCharacter_eq_zero_of_perfect [Group.IsPerfect G]
    (χ : PrimeCharacters p G) : χ=0 := by
  let f : G →* Multiplicative (ZMod p) := AddMonoidHom.toMultiplicativeRight χ
  letI : Group.IsPerfect f.range := Group.IsPerfect.range f
  letI : Subsingleton f.range := Group.IsPerfect.subsingleton_of_isMulCommutative
  apply AddMonoidHom.ext
  intro g
  have h : (⟨f g.toMul,⟨g.toMul,rfl⟩⟩:f.range)=1 := Subsingleton.elim _ _
  exact congrArg (fun x : f.range => Multiplicative.toAdd (x:Multiplicative (ZMod p))) h

/-- Only coprimality with the character prime is used here. -/
theorem primeCharacter_eq_zero_of_power_group (q : ℕ)
    (hq : (q:ZMod p)≠0) (hG : IsPGroup q G) (χ : PrimeCharacters p G) : χ=0 := by
  apply AddMonoidHom.ext
  intro g
  obtain ⟨k,hk⟩ := hG g.toMul
  have h := congrArg (fun x : G => χ (Additive.ofMul x)) hk
  change χ ((q^k) • g)=χ 0 at h
  rw [map_nsmul,map_zero,nsmul_eq_mul,Nat.cast_pow] at h
  exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ hq)

theorem primeCharacters_subsingleton_of_perfect [Group.IsPerfect G] :
    Subsingleton (PrimeCharacters p G) :=
  ⟨fun χ ψ => (primeCharacter_eq_zero_of_perfect p χ).trans
    (primeCharacter_eq_zero_of_perfect p ψ).symm⟩

theorem primeCharacters_subsingleton_of_power_group (q : ℕ)
    (hq : (q:ZMod p)≠0) (hG : IsPGroup q G) : Subsingleton (PrimeCharacters p G) :=
  ⟨fun χ ψ => (primeCharacter_eq_zero_of_power_group p q hq hG χ).trans
    (primeCharacter_eq_zero_of_power_group p q hq hG ψ).symm⟩

theorem primeRelativeHead_perfect {A : Type*} [Group A] (N : Subgroup A) [N.Normal]
    [Group.IsPerfect N] : Module.finrank (ZMod p) (primeRelativeCharacters p N)=0 := by
  letI := primeCharacters_subsingleton_of_perfect p (G := N)
  exact Module.finrank_zero_of_subsingleton

theorem primeRelativeHead_power_group {A : Type*} [Group A] (N : Subgroup A) [N.Normal]
    (q : ℕ) (hq : (q:ZMod p)≠0) (hN : IsPGroup q N) :
    Module.finrank (ZMod p) (primeRelativeCharacters p N)=0 := by
  letI := primeCharacters_subsingleton_of_power_group p q hq hN
  exact Module.finrank_zero_of_subsingleton

/-- A perfect lower layer contributes exactly zero even in a nonsplit
normal chain; the original upper quotient action remains unchanged. -/
theorem primeRelativeHead_chain_perfect_kernel {A : Type*} [Group A] [Finite A]
    (B C : Subgroup A) [B.Normal] [C.Normal] [Group.IsPerfect B] (hBC : B≤C) :
    Module.finrank (ZMod p) (primeRelativeCharacters p C)=
      Module.finrank (ZMod p) (primeRelativeCharacters p (normalChainQuotient B C)) := by
  letI := primeCharacters_subsingleton_of_perfect p (G := B)
  have h0 : Module.finrank (ZMod p) (normalChainRetainedCharacters B C p hBC)=0 :=
    Module.finrank_zero_of_subsingleton
  simpa only [h0,Nat.add_zero] using primeRelativeHead_chain_eq B C p hBC

/-- The same exact elimination holds for a layer whose element orders
are powers of a scalar invertible in the character field. -/
theorem primeRelativeHead_chain_power_kernel {A : Type*} [Group A] [Finite A]
    (B C : Subgroup A) [B.Normal] [C.Normal] (hBC : B≤C)
    (q : ℕ) (hq : (q:ZMod p)≠0) (hB : IsPGroup q B) :
    Module.finrank (ZMod p) (primeRelativeCharacters p C)=
      Module.finrank (ZMod p) (primeRelativeCharacters p (normalChainQuotient B C)) := by
  letI := primeCharacters_subsingleton_of_power_group p q hq hB
  have h0 : Module.finrank (ZMod p) (normalChainRetainedCharacters B C p hBC)=0 :=
    Module.finrank_zero_of_subsingleton
  simpa only [h0,Nat.add_zero] using primeRelativeHead_chain_eq B C p hBC

end SymmetricSubgroupAsymptotics
