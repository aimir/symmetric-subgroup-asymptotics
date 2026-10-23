import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Group.Subgroup.Ker

/-! Actual automorphisms of a prime-cardinality group are abelian, and a
nonidentity automorphism fixes no nonidentity group element. These are
structural statements, with no named-group recognition hypothesis. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimeCardAutomorphismAction

variable {N : Type*} [Group N] [hprime : Fact (Nat.card N).Prime]
include hprime

theorem aut_eq_one_of_fixed_ne_one (a : MulAut N) (n : N) (hn : n≠1)
    (hfix : a n=n) : a=1 := by
  let F : Subgroup N := a.toMonoidHom.eqLocus (MonoidHom.id N)
  have hnF : n ∈ F := hfix
  have hF : F≠⊥ := by
    intro he
    rw [he] at hnF
    exact hn (Subgroup.mem_bot.mp hnF)
  have htop : F=⊤ := F.eq_bot_or_eq_top_of_prime_card.resolve_left hF
  apply MulEquiv.ext
  intro x
  change a x=x
  have hx : x ∈ F := by rw [htop]; exact Subgroup.mem_top x
  exact hx

theorem mulAut_isMulCommutative : IsMulCommutative (MulAut N) := by
  letI : IsCyclic N := isCyclic_of_prime_card (p := Nat.card N) rfl
  let e := IsCyclic.mulAutMulEquiv N
  apply isMulCommutative_iff.mpr
  intro a b
  apply e.injective
  rw [map_mul,map_mul,mul_comm]

theorem faithful_action_free {H : Type*} [Group H] (φ : H →* MulAut N)
    (hφ : Function.Injective φ) :
    ∀ (h : H), h≠1 → ∀ n : N, φ h n=n → n=1 := by
  intro h hh n hfix
  by_contra hn
  have he : φ h=1 := aut_eq_one_of_fixed_ne_one (φ h) n hn hfix
  exact hh (hφ (he.trans (map_one φ).symm))

theorem faithful_action_isMulCommutative {H : Type*} [Group H]
    (φ : H →* MulAut N) (hφ : Function.Injective φ) : IsMulCommutative H := by
  have hc := (isMulCommutative_iff.mp (mulAut_isMulCommutative (N := N)))
  apply isMulCommutative_iff.mpr
  intro h k
  apply hφ
  rw [map_mul,map_mul]
  exact hc _ _

end SymmetricSubgroupAsymptotics.PrimeCardAutomorphismAction
