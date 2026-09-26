import SymmetricSubgroupAsymptotics.PrimeRelativeRadicalPresentation
import Mathlib.Algebra.Group.Hom.Basic

/-! Generator reduction for the actual invariant-character radical.
The p-th powers of an actual generating family suffice only after the
full mixed commutator [N,G] is retained. This matches the relative radical
constructed by the carrier producer. No finiteness, group-order, quotient
dimension, or p-group premise is needed for the presentation equality. -/
set_option autoImplicit false
noncomputable section
open scoped commutatorElement IsMulCommutative

namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime]
    {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    {ι κ : Type*}

/-- The displayed generators belong to the literal original subgroup N.
Their p-th powers, together with [N,G], generate its exact relative radical. -/
theorem primeRelativeRadical_eq_generated_pow_commutator
    (gens : ι → N) (hgen : Subgroup.closure (Set.range gens) = ⊤) :
    primeRelativeRadical p N =
      Subgroup.closure (Set.range (fun i => (gens i : G)^p)) ⊔
        ⁅N,(⊤ : Subgroup G)⁆ := by
  let S : Subgroup G :=
    Subgroup.closure (Set.range (fun i => (gens i : G)^p)) ⊔ ⁅N,(⊤ : Subgroup G)⁆
  have hSN : S ≤ N := by
    apply sup_le
    · apply (Subgroup.closure_le N).mpr
      rintro _ ⟨i,rfl⟩
      exact N.pow_mem (gens i).2 p
    · exact Subgroup.commutator_le_left N ⊤
  have hcomm : ⁅N,(⊤ : Subgroup G)⁆ ≤ S := le_sup_right
  letI : S.Normal := Subgroup.commutator_top_right_le_iff.mp
    ((Subgroup.commutator_mono hSN le_rfl).trans hcomm)
  let D : Subgroup N := S.subgroupOf N
  letI : IsMulCommutative (N ⧸ D) := by
    apply Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
    intro n hn
    change (n : G) ∈ S
    have hm : (n : G) ∈ (commutator N).map N.subtype := ⟨n,hn,rfl⟩
    rw [N.map_subtype_commutator] at hm
    exact hcomm ((Subgroup.commutator_mono le_rfl le_top) hm)
  let q : N →* N ⧸ D := QuotientGroup.mk' D
  let f : N →* N ⧸ D := (powMonoidHom p).comp q
  have hkernel : Subgroup.closure (Set.range gens) ≤ f.ker := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    change (q (gens i))^p=1
    rw [← map_pow]
    apply (QuotientGroup.eq_one_iff _).mpr
    change (gens i : G)^p ∈ S
    exact (show Subgroup.closure (Set.range (fun i => (gens i : G)^p)) ≤ S
      from le_sup_left) (Subgroup.subset_closure (Set.mem_range_self i))
  have hpowers (n : N) : (n : G)^p ∈ S := by
    have hn : n ∈ f.ker := hkernel (hgen.symm ▸ Subgroup.mem_top n)
    have he : q (n^p)=1 := by
      rw [map_pow]
      exact hn
    exact (QuotientGroup.eq_one_iff (N := D) (n^p)).mp he
  apply le_antisymm
  · rw [primeRelativeRadical_eq_powerCommutator]
    apply sup_le
    · apply (Subgroup.closure_le S).mpr
      rintro _ ⟨n,rfl⟩
      exact hpowers n
    · exact hcomm
  · apply sup_le
    · apply (Subgroup.closure_le (primeRelativeRadical p N)).mpr
      rintro _ ⟨i,rfl⟩
      exact pow_mem_primeRelativeRadical p N (gens i)
    · exact (primeRelativePowerCommutator_commutator_le p N).trans
        (primeRelativePowerCommutator_le_radical p N)

/-- A producer can keep its original ambient generator values. The
closure equation supplies both their membership and complete generation;
no new generators or replacement subgroup are chosen. -/
theorem primeRelativeRadical_eq_ambient_generator_pow_commutator
    (gens : ι → G) (hgen : Subgroup.closure (Set.range gens) = N) :
    primeRelativeRadical p N =
      Subgroup.closure (Set.range (fun i => (gens i)^p)) ⊔
        ⁅N,(⊤ : Subgroup G)⁆ := by
  let original : ι → N := fun i => ⟨gens i,by
    rw [← hgen]
    exact Subgroup.subset_closure (Set.mem_range_self i)⟩
  have horiginal : Subgroup.closure (Set.range original) = ⊤ := by
    apply Subgroup.map_injective N.subtype_injective
    rw [MonoidHom.map_closure]
    have himage : N.subtype '' Set.range original = Set.range gens := by
      ext x
      constructor
      · rintro ⟨n,⟨i,rfl⟩,rfl⟩
        exact Set.mem_range_self i
      · rintro ⟨i,rfl⟩
        exact ⟨original i,Set.mem_range_self i,rfl⟩
    rw [himage,hgen,← MonoidHom.range_eq_map,Subgroup.range_subtype]
  exact primeRelativeRadical_eq_generated_pow_commutator p N original horiginal

/-- Literal finite tuples for N and [N,G] give one literal tuple for the
radical. The mixed-commutator generation equation is an explicit proof
obligation, not a claim that normality or a declared order suffices. -/
theorem primeRelativeRadical_eq_closure_generator_powers_and_commutators
    (gens : ι → G) (hgen : Subgroup.closure (Set.range gens) = N)
    (commutators : κ → G)
    (hcomm : Subgroup.closure (Set.range commutators) = ⁅N,(⊤ : Subgroup G)⁆) :
    primeRelativeRadical p N =
      Subgroup.closure (Set.range (Sum.elim (fun i => (gens i)^p) commutators)) := by
  rw [Set.Sum.elim_range,Subgroup.closure_union,hcomm]
  exact primeRelativeRadical_eq_ambient_generator_pow_commutator p N gens hgen

end SymmetricSubgroupAsymptotics
