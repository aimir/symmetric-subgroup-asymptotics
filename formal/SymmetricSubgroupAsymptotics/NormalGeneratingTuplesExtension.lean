import SymmetricSubgroupAsymptotics.NormalGeneratorQuotientSocles
import SymmetricSubgroupAsymptotics.CoprimeCyclicQuotientSocles
import SymmetricSubgroupAsymptotics.PrimeRelativeHeadNormalGenerators
import Mathlib.Data.Fin.Tuple.Basic

/-! Normal-generator bounds in an actual extension. The kernel bound is
on normal subgroups of the actual kernel, with its own conjugation action;
this is stronger than the ambient bound required in the conclusion. The
proof lifts original image generators and retains the original kernel. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

theorem normal_generating_tuples_extension
    {G Q : Type} [Group G] [Group Q] {a b : ℕ}
    (pi : G →* Q) (hpi : Function.Surjective pi)
    (hK : ∀ N : Subgroup pi.ker, N.Normal →
      ∃ x : Fin a → pi.ker, Subgroup.normalClosure (Set.range x) = N)
    (hQ : ∀ N : Subgroup Q, N.Normal →
      ∃ x : Fin b → Q, Subgroup.normalClosure (Set.range x) = N) :
    ∀ N : Subgroup G, N.Normal →
      ∃ x : Fin (a + b) → G, Subgroup.normalClosure (Set.range x) = N := by
  intro N hN
  letI : N.Normal := hN
  obtain ⟨x, hx⟩ := hK (N.comap pi.ker.subtype) (hN.comap _)
  obtain ⟨y, hy⟩ := hQ (N.map pi) (hN.map pi hpi)
  have hxN (i : Fin a) : (x i : G) ∈ N := by
    change x i ∈ N.comap pi.ker.subtype
    rw [← hx]
    exact Subgroup.subset_normalClosure (Set.mem_range_self i)
  have hlift : ∀ i, ∃ z : G, z ∈ N ∧ pi z = y i := by
    intro i
    have h : y i ∈ N.map pi := by
      rw [← hy]
      exact Subgroup.subset_normalClosure (Set.mem_range_self i)
    exact h
  choose y' hyN hy' using hlift
  let z : Fin (a + b) → G := Fin.addCases (fun i => (x i : G)) y'
  let C : Subgroup G := Subgroup.normalClosure (Set.range z)
  letI : C.Normal := by dsimp [C]; infer_instance
  have hxC (i : Fin a) : (x i : G) ∈ C := by
    have h := Subgroup.subset_normalClosure (Set.mem_range_self (f := z) (i.castAdd b))
    simpa only [z, Fin.addCases_left] using h
  have hyC (i : Fin b) : y' i ∈ C := by
    have h := Subgroup.subset_normalClosure (Set.mem_range_self (f := z) (i.natAdd a))
    simpa only [z, Fin.addCases_right] using h
  have hCN : C ≤ N := by
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨i, rfl⟩
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa only [z, Fin.addCases_left] using hxN j
    · intro j
      simpa only [z, Fin.addCases_right] using hyN j
  have hkernel : N.comap pi.ker.subtype ≤ C.comap pi.ker.subtype := by
    rw [← hx]
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨i, rfl⟩
    exact hxC i
  have himage : N.map pi ≤ C.map pi := by
    letI : (C.map pi).Normal := Subgroup.Normal.map inferInstance pi hpi
    rw [← hy]
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨i, rfl⟩
    exact ⟨y' i, hyC i, hy' i⟩
  refine ⟨z, le_antisymm hCN ?_⟩
  intro n hn
  obtain ⟨c, hc, he⟩ := himage (show pi n ∈ N.map pi from ⟨n, hn, rfl⟩)
  have hker : n * c⁻¹ ∈ pi.ker := by
    change pi (n * c⁻¹) = 1
    rw [map_mul, map_inv, he, mul_inv_cancel]
  have hd : n * c⁻¹ ∈ C :=
    hkernel (show (⟨n * c⁻¹, hker⟩ : pi.ker) ∈ N.comap pi.ker.subtype from
      N.mul_mem hn (N.inv_mem (hCN hc)))
  simpa only [inv_mul_cancel_right] using C.mul_mem hd hc

/-- A finite cyclic quotient costs one extra ambient normal generator. -/
theorem normal_generating_tuples_cyclic_extension
    {G Q : Type} [Group G] [Group Q] [Finite Q] [IsCyclic Q] {a : ℕ}
    (pi : G →* Q) (hpi : Function.Surjective pi)
    (hK : ∀ N : Subgroup pi.ker, N.Normal →
      ∃ x : Fin a → pi.ker, Subgroup.normalClosure (Set.range x) = N) :
    ∀ N : Subgroup G, N.Normal →
      ∃ x : Fin (a + 1) → G, Subgroup.normalClosure (Set.range x) = N := by
  apply normal_generating_tuples_extension pi hpi hK
  intro N hN
  letI : N.Normal := hN
  exact exists_normal_generating_tuple_of_normalGen_le N
    (CoprimeCyclicQuotientSocles.normalGen_le_one_of_isCyclic N)

/-- The resulting tuple controls the relative head of every original
normal subgroup. It is not a bound on a substituted quotient axis. -/
theorem primeRelativeHead_le_cyclic_extension
    (p : ℕ) [Fact p.Prime]
    {G Q : Type} [Group G] [Group Q] [Finite Q] [IsCyclic Q] {a : ℕ}
    (pi : G →* Q) (hpi : Function.Surjective pi)
    (hK : ∀ N : Subgroup pi.ker, N.Normal →
      ∃ x : Fin a → pi.ker, Subgroup.normalClosure (Set.range x) = N)
    (N : Subgroup G) [N.Normal] :
    Module.finrank (ZMod p) (primeRelativeCharacters p N) ≤ a + 1 := by
  obtain ⟨x, hx⟩ := normal_generating_tuples_cyclic_extension pi hpi hK N inferInstance
  exact primeRelativeHead_le_normal_generating_tuple p N x hx

end SymmetricSubgroupAsymptotics

end
