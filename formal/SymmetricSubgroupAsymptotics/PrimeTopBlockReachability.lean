import SymmetricSubgroupAsymptotics.BlockKernelClassBound
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-! A prime ORIGINAL top image forces every outside element to cycle
through all original blocks. Powers are taken in the original group;
no outside element is required to have prime order. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimeTopBlockReachability
open OriginalBlockClassBound

variable {A X : Type} [Group A] [MulAction A X] [MulAction.IsPretransitive A X]

theorem outside_power_reaches (p : ℕ) (hp : p.Prime)
    (htop : Nat.card (Top (A:=A) (X:=X))=p)
    (g : A) (hg : g∉Kernel (A:=A) (X:=X)) (x y : X) :
    ∃j : ℤ,(g^j)•x=y := by
  let f : A→*Equiv.Perm X := topMap (A:=A) (X:=X)
  let t : f.range := ⟨f g,⟨g,rfl⟩⟩
  have ht : t≠1 := by
    intro he
    exact hg (congrArg (fun z : f.range=>z.val) he)
  obtain ⟨a,ha⟩ := MulAction.exists_smul_eq A x y
  let u : f.range := ⟨f a,⟨a,rfl⟩⟩
  letI : Fact p.Prime := ⟨hp⟩
  have hu : u∈Subgroup.zpowers t := mem_zpowers_of_prime_card htop ht
  obtain ⟨j,hj⟩ := Subgroup.mem_zpowers_iff.mp hu
  have hv := congrArg (fun z : f.range=>z.val) hj
  change (f g)^j=f a at hv
  rw [←map_zpow] at hv
  have he := congrArg (fun r : Equiv.Perm X=>r x) hv
  exact ⟨j,(show (g^j)•x=a•x from he).trans ha⟩

variable {Ω : Type} [MulAction A Ω] (b : Ω→X)
    (hb : ∀ (a:A) (ω:Ω),b (a•ω)=a•b ω)

include hb in
theorem outside_power_reaches_fibre (p : ℕ) (hp : p.Prime)
    (htop : Nat.card (Top (A:=A) (X:=X))=p)
    (g : A) (hg : g∉Kernel (A:=A) (X:=X)) (ω:Ω) (x₀:X) :
    ∃j : ℤ,b ((g^j)•ω)=x₀ := by
  obtain ⟨j,hj⟩ := outside_power_reaches p hp htop g hg (b ω) x₀
  exact ⟨j,(hb (g^j) ω).trans hj⟩

end SymmetricSubgroupAsymptotics.PrimeTopBlockReachability
