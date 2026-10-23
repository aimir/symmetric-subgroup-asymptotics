import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Data.Nat.Prime.Basic

/-! Actual centralizers in an abelian prime-index extension, including
nonsplit extensions. Every outside element generates the whole group
together with the original kernel. Its fixed subgroup in that kernel
is exactly the intersection with the original group centre, independent
of the outside representative. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimeIndexAbelianCentralizers
variable {G : Type*} [Group G]

theorem overgroup_eq_top_of_prime_index (N K : Subgroup G) (p : ℕ) (hp : p.Prime)
    (hindex : N.index=p) (hNK : N≤K) (x : G) (hx : x∈K) (hxN : x∉N) : K=⊤ := by
  have hd : K.index∣p := hindex ▸ Subgroup.index_dvd_of_le hNK
  rcases (Nat.dvd_prime hp).mp hd with h1|hpK
  · exact Subgroup.index_eq_one.mp h1
  · have hr := Subgroup.relIndex_mul_index hNK
    rw [hindex,hpK] at hr
    have hr1 : N.relIndex K=1 := by
      apply Nat.mul_right_cancel (m:=p) hp.pos
      simpa only [one_mul] using hr
    exact False.elim (hxN (Subgroup.relIndex_eq_one.mp hr1 hx))

variable (N : Subgroup G) [IsMulCommutative N]

theorem kernel_le_centralizer (n : N) : N≤Subgroup.centralizer {(n:G)} := by
  intro y hy
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  exact congrArg (fun z : N=>z.val) (mul_comm' (⟨y,hy⟩ : N) n)

theorem kernel_element_central_of_commutes_outside (p : ℕ) (hp : p.Prime) (hindex : N.index=p)
    (x : G) (hx : x∉N) (n : N) (hxn : Commute x (n:G)) : (n:G)∈Subgroup.center G := by
  have htop := overgroup_eq_top_of_prime_index N (Subgroup.centralizer {(n:G)}) p hp hindex
    (kernel_le_centralizer N n) x (Subgroup.mem_centralizer_singleton_iff.mpr hxn.eq) hx
  apply Subgroup.mem_center_iff.mpr
  intro g
  apply Subgroup.mem_centralizer_singleton_iff.mp
  rw [htop]
  exact Subgroup.mem_top g

def fixedKernel (x : G) : Subgroup N := (Subgroup.centralizer {x}).comap N.subtype

def centralKernel : Subgroup N := (Subgroup.center G).comap N.subtype

theorem fixedKernel_eq_centralKernel (p : ℕ) (hp : p.Prime) (hindex : N.index=p)
    (x : G) (hx : x∉N) : fixedKernel N x=centralKernel N := by
  ext n
  constructor
  · intro hn
    exact kernel_element_central_of_commutes_outside N p hp hindex x hx n
      (Subgroup.mem_centralizer_singleton_iff.mp hn).symm
  · intro hn
    exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_center_iff.mp hn x).symm

theorem centralizer_eq_kernel_of_noncentral (p : ℕ) (hp : p.Prime) (hindex : N.index=p)
    (n : N) (hn : (n:G)∉Subgroup.center G) : Subgroup.centralizer {(n:G)}=N := by
  apply le_antisymm _ (kernel_le_centralizer N n)
  intro x hx
  by_contra hxN
  exact hn (kernel_element_central_of_commutes_outside N p hp hindex x hxN n
    (Subgroup.mem_centralizer_singleton_iff.mp hx))

end SymmetricSubgroupAsymptotics.PrimeIndexAbelianCentralizers
