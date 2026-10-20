import SymmetricSubgroupAsymptotics.NormalQuotientOrderedTransversal

/-! A normal p-subgroup gives an original-group triangular transversal
for the point-stabilizer inclusion H≤HN. No subnormality of H in G is
assumed, and the representatives all lie in the actual normal p-subgroup. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem normalPGroup_orbit_orderedTransversal
    (H N : Subgroup G) [N.Normal] (hN : IsPGroup p N) :
    ∃ r : ℕ, ∃ D : OrderedCosetData H (H⊔N) (PrimeCosetGrid p r)
        (primeCosetGridLT p r) (primeCosetGridComparable p r),
      ∀ a, D.repr a∈N := by
  let P := H.subgroupOf N
  obtain ⟨r,hr⟩ := hN.index P
  obtain ⟨D⟩ := pGroup_orderedCosetTransversal hN P r hr
  let T : PrimeCosetGrid p r → G := fun a => (D.repr a : G)
  have hTmem : ∀ a, T a∈N := fun a => (D.repr a).property
  let E : OrderedCosetData H (H⊔N) (PrimeCosetGrid p r)
      (primeCosetGridLT p r) (primeCosetGridComparable p r) := {
    le := le_sup_left
    repr := T
    mem := fun a => Subgroup.mem_sup_right (hTmem a)
    factor := by
      intro y hy
      obtain ⟨h,hh,n,hn,hhn⟩ := Subgroup.mem_sup_of_normal_right.mp hy
      obtain ⟨u,hu,a,hua⟩ := D.factor ⟨n,hn⟩ (Subgroup.mem_top _)
      refine ⟨h*(u : G),H.mul_mem hh hu,a,?_⟩
      have he := congrArg (fun z : N => (z : G)) hua
      change n=(u : G)*T a at he
      rw [←hhn,he,mul_assoc]
    unique := by
      intro a b hab
      apply D.unique a b
      change ((D.repr a*(D.repr b)⁻¹ : N) : G)∈H
      exact hab
    triangular := by
      intro a b c hab hbc
      obtain ⟨u,hu,e,hec,he⟩ := D.triangular a b c hab hbc
      refine ⟨(u : G),hu,e,hec,?_⟩
      exact congrArg (fun z : N => (z : G)) he }
  exact ⟨r,E,hTmem⟩

end SymmetricSubgroupAsymptotics
