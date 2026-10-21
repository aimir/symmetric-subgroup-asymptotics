import SymmetricSubgroupAsymptotics.NaturalAlternatingChief
import SymmetricSubgroupAsymptotics.MarkedC4GeneratorNumbers
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! Uniform two-generation for the alternating family, independent of
CFSG. A full rotation and one adjacent swap generate the symmetric group.
In either parity an even nonidentity generator and its involution
commutator generate the alternating subgroup by the existing symbolic
normal-subgroup bridge. No permutation table or finite-degree cutoff is
used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGAlternatingGeneration

private theorem odd_pair_closure (k : ℕ) :
    ∃ a b : Equiv.Perm (Fin (2*k+5)),
      Subgroup.closure ({a,b} : Set (Equiv.Perm (Fin (2*k+5))))=
        alternatingGroup (Fin (2*k+5)) := by
  let g := finRotate (2*k+5)
  let s := Equiv.swap (naturalAlternatingSecond (2*k)) (naturalAlternatingLast (2*k))
  refine ⟨g,g⁻¹*s*g*s,?_⟩
  apply involutionCommutatorClosure_eq_alternating (by simp only [Nat.card_fin];omega) g s
    (Equiv.swap_inv _ _)
  · have hc := Equiv.Perm.closure_cycle_adjacent_swap
      (isCycle_finRotate_of_le (by omega : 2≤2*k+5))
      (support_finRotate_of_le (by omega : 2≤2*k+5)) (naturalAlternatingSecond (2*k))
    simpa only [g,s,naturalAlternating_rotation_second] using hc
  · apply Equiv.Perm.mem_alternatingGroup.mpr
    change Equiv.Perm.sign (finRotate (2*k+5))=1
    rw [sign_finRotate,show 2*k+5-1=2*(k+2) by omega,pow_mul]
    norm_num
  · exact (isCycle_finRotate_of_le (by omega : 2≤2*k+5)).ne_one

private theorem even_pair_closure (k : ℕ) :
    ∃ a b : Equiv.Perm (Fin (2*k+1+5)),
      Subgroup.closure ({a,b} : Set (Equiv.Perm (Fin (2*k+1+5))))=
        alternatingGroup (Fin (2*k+1+5)) := by
  let σ := finRotate (2*k+1+5)
  let s := Equiv.swap (naturalAlternatingSecond (2*k+1)) (naturalAlternatingLast (2*k+1))
  let g := σ*s
  have hs : s⁻¹=s := Equiv.swap_inv _ _
  have hsquare : s*s=1 := Equiv.swap_mul_self _ _
  refine ⟨g,g⁻¹*s*g*s,?_⟩
  apply involutionCommutatorClosure_eq_alternating (by simp only [Nat.card_fin];omega) g s hs
  · apply closure_pair_top_of_mul_right
    have hc := Equiv.Perm.closure_cycle_adjacent_swap
      (isCycle_finRotate_of_le (by omega : 2≤2*k+1+5))
      (support_finRotate_of_le (by omega : 2≤2*k+1+5)) (naturalAlternatingSecond (2*k+1))
    simpa only [g,mul_assoc,hsquare,mul_one,σ,s,naturalAlternating_rotation_second] using hc
  · apply Equiv.Perm.mem_alternatingGroup.mpr
    have hne : naturalAlternatingSecond (2*k+1)≠naturalAlternatingLast (2*k+1) := by
      intro he
      have hh := congrArg Fin.val he
      dsimp [naturalAlternatingSecond,naturalAlternatingLast] at hh
      omega
    change Equiv.Perm.sign (finRotate (2*k+1+5)*
      Equiv.swap (naturalAlternatingSecond (2*k+1)) (naturalAlternatingLast (2*k+1)))=1
    rw [map_mul,sign_finRotate,Equiv.Perm.sign_swap hne,
      show 2*k+1+5-1=2*(k+2)+1 by omega,pow_succ,pow_mul]
    norm_num
  · intro he
    have hsa : s (naturalAlternatingFirst (2*k+1))=naturalAlternatingFirst (2*k+1) := by
      have hab : naturalAlternatingFirst (2*k+1)≠naturalAlternatingSecond (2*k+1) := by
        intro h
        have hh := congrArg Fin.val h
        dsimp [naturalAlternatingFirst,naturalAlternatingSecond] at hh
        omega
      have hac : naturalAlternatingFirst (2*k+1)≠naturalAlternatingLast (2*k+1) := by
        intro h
        have hh := congrArg Fin.val h
        dsimp [naturalAlternatingFirst,naturalAlternatingLast] at hh
        omega
      simp [s,Equiv.swap_apply_def,hab,hac]
    have hval : g (naturalAlternatingFirst (2*k+1))=naturalAlternatingSecond (2*k+1) := by
      simpa only [g,Equiv.Perm.mul_apply,hsa,σ] using naturalAlternating_rotation_first (2*k+1)
    rw [he,Equiv.Perm.one_apply] at hval
    have hh := congrArg Fin.val hval
    dsimp [naturalAlternatingFirst,naturalAlternatingSecond] at hh
    omega

/-- Two actual even permutations generate the full alternating subgroup
in every degree at least five. -/
theorem exists_pair_closure (n : ℕ) (hn : 5≤n) :
    ∃ a b : Equiv.Perm (Fin n),
      Subgroup.closure ({a,b} : Set (Equiv.Perm (Fin n)))=alternatingGroup (Fin n) := by
  obtain ⟨k,hk|hk⟩ := Nat.even_or_odd' (n-5)
  · have he : n=2*k+5 := by omega
    subst n
    exact odd_pair_closure k
  · have he : n=2*k+1+5 := by omega
    subst n
    exact even_pair_closure k

/-- The generators belong to the alternating group itself, rather than
merely to its containing symmetric group. -/
theorem exists_generating_pair (n : ℕ) (hn : 5≤n) :
    ∃ a b : alternatingGroup (Fin n),
      Subgroup.closure ({a,b} : Set (alternatingGroup (Fin n)))=⊤ := by
  obtain ⟨a,b,hab⟩ := exists_pair_closure n hn
  have ha : a∈alternatingGroup (Fin n) := hab ▸ Subgroup.subset_closure (by simp)
  have hb : b∈alternatingGroup (Fin n) := hab ▸ Subgroup.subset_closure (by simp)
  let x : alternatingGroup (Fin n) := ⟨a,ha⟩
  let y : alternatingGroup (Fin n) := ⟨b,hb⟩
  refine ⟨x,y,?_⟩
  apply Subgroup.map_injective (alternatingGroup (Fin n)).subtype_injective
  rw [MonoidHom.map_closure,←MonoidHom.range_eq_map,Subgroup.range_subtype]
  simpa only [Set.image_insert_eq,Set.image_singleton] using hab

/-- A fixed-length generating tuple, useful for family-uniform consumers. -/
theorem exists_generating_tuple (n : ℕ) (hn : 5≤n) :
    ∃ a : Fin 2 → alternatingGroup (Fin n),Subgroup.closure (Set.range a)=⊤ := by
  obtain ⟨x,y,hxy⟩ := exists_generating_pair n hn
  refine ⟨![x,y],?_⟩
  have hr : Set.range (![x,y] : Fin 2 → alternatingGroup (Fin n))={x,y} := by
    ext z
    simp only [Set.mem_range,Set.mem_insert_iff,Set.mem_singleton_iff]
    constructor
    · rintro ⟨i,rfl⟩
      fin_cases i <;> simp
    · rintro (rfl|rfl)
      · exact ⟨0,rfl⟩
      · exact ⟨1,rfl⟩
  rw [hr]
  exact hxy

/-- Ordinary generation rank is at most two, with no family hypothesis. -/
theorem genRank_le_two (n : ℕ) (hn : 5≤n) :
    MarkedC4.genRank (alternatingGroup (Fin n))≤2 := by
  obtain ⟨a,ha⟩ := exists_generating_tuple n hn
  let S : Finset (alternatingGroup (Fin n)) := Finset.univ.image a
  have hs : (S : Set (alternatingGroup (Fin n)))=Set.range a := by
    ext x
    simp only [S,Finset.coe_image,Finset.coe_univ,Set.image_univ]
  have hgen : Subgroup.closure (S : Set (alternatingGroup (Fin n)))=⊤ := by rw [hs];exact ha
  exact (MarkedC4.genRank_le hgen).trans (Finset.card_image_le.trans (by simp))

end SymmetricSubgroupAsymptotics.CFSGAlternatingGeneration
