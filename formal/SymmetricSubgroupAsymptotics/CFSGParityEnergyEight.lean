import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! A small denominator-cleared root census bound: integer vectors in
eight coordinates, of energy eight and common coordinate parity, have
at most 512 possibilities. No exceptional root table is enumerated. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGParityEnergyEight

def Candidate := {y : Fin 8→ℤ // (∑i,y i^2)=8 ∧
  ∃b : Bool,∀i,y i%2=if b then 1 else 0}

theorem coordinate_bound (y : Fin 8→ℤ) (hy : (∑i,y i^2)=8) (i : Fin 8) :
    -2≤y i ∧ y i≤2 := by
  have hi := Finset.single_le_sum (fun j (_ : j∈(Finset.univ : Finset (Fin 8)))=>sq_nonneg (y j))
    (Finset.mem_univ i)
  rw [hy] at hi
  constructor
  · by_contra h
    have hn : y i≤ -3 := by omega
    nlinarith
  · by_contra h
    have hn : 3≤y i := by omega
    nlinarith

def oddPattern (b : Fin 8→Bool) : Fin 8→ℤ := fun i=>if b i then 1 else -1
def evenPattern (i j : Fin 8) (s t : Bool) : Fin 8→ℤ :=
  Pi.single i (if s then 2 else -2)+Pi.single j (if t then 2 else -2)

theorem odd_pattern_covers (y : Fin 8→ℤ) (hy : (∑i,y i^2)=8)
    (hp : ∀i,y i%2=1) : ∃b : Fin 8→Bool,oddPattern b=y := by
  classical
  refine ⟨fun i=>decide (y i=1),?_⟩
  funext i
  have hi := coordinate_bound y hy i
  have hm := hp i
  have hc : y i=1 ∨ y i= -1 := by omega
  rcases hc with h|h <;> simp [oddPattern,h]

theorem even_pattern_covers (y : Fin 8→ℤ) (hy : (∑i,y i^2)=8)
    (hp : ∀i,y i%2=0) :
    ∃i j : Fin 8,∃s t : Bool,evenPattern i j s t=y := by
  classical
  let S : Finset (Fin 8) := Finset.univ.filter (fun i=>y i≠0)
  have hc (i : Fin 8) : y i= -2 ∨ y i=0 ∨ y i=2 := by
    have hb := coordinate_bound y hy i
    have hm := hp i
    omega
  have hsquare (i : Fin 8) : y i^2=if i∈S then (4:ℤ) else 0 := by
    rcases hc i with h|h|h <;> simp [S,h]
  have hsum : (∑i,y i^2)=(S.card:ℤ)*4 := by
    simp only [hsquare,Finset.sum_ite]
    simp
  have hcardZ : (S.card:ℤ)=2 := by omega
  have hcard : S.card=2 := by exact_mod_cast hcardZ
  obtain ⟨i,j,hij,hS⟩ := Finset.card_eq_two.mp hcard
  have hi : y i≠0 := (Finset.mem_filter.mp (show i∈S by rw [hS];simp)).2
  have hj : y j≠0 := (Finset.mem_filter.mp (show j∈S by rw [hS];simp)).2
  have signed (k : Fin 8) (hk : y k≠0) : ∃s : Bool,y k=if s then 2 else -2 := by
    rcases hc k with h|h|h
    · exact ⟨false,h⟩
    · exact (hk h).elim
    · exact ⟨true,h⟩
  obtain ⟨s,hs⟩ := signed i hi
  obtain ⟨t,ht⟩ := signed j hj
  refine ⟨i,j,s,t,?_⟩
  funext k
  by_cases hki : k=i
  · subst k
    simpa [evenPattern,Pi.single_apply,hij,Ne.symm hij] using hs.symm
  by_cases hkj : k=j
  · subst k
    simpa [evenPattern,Pi.single_apply,hij,Ne.symm hij] using ht.symm
  have hk : y k=0 := by
    by_contra hk
    have hmem : k∈S := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hk⟩
    rw [hS] at hmem
    simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
    exact hmem.elim hki hkj
  simp [evenPattern,Pi.single_apply,Ne.symm hki,Ne.symm hkj,hk]

abbrev Code := (Fin 8→Bool)⊕(Fin 8×Fin 8×Bool×Bool)

def pattern : Code→(Fin 8→ℤ)
  | Sum.inl b=>oddPattern b
  | Sum.inr ⟨i,j,s,t⟩=>evenPattern i j s t

theorem pattern_covers (y : Candidate) : ∃c : Code,pattern c=y.val := by
  obtain ⟨b,hb⟩ := y.property.2
  cases b with
  | false=>
    obtain ⟨i,j,s,t,h⟩ := even_pattern_covers y.val y.property.1 hb
    exact ⟨Sum.inr ⟨i,j,s,t⟩,h⟩
  | true=>
    obtain ⟨b,h⟩ := odd_pattern_covers y.val y.property.1 hb
    exact ⟨Sum.inl b,h⟩

theorem candidate_card_le : Nat.card Candidate≤512 := by
  classical
  let enc : Candidate→Code := fun y=>Classical.choose (pattern_covers y)
  have hinj : Function.Injective enc := by
    intro y z he
    apply Subtype.ext
    have hh := congrArg pattern he
    exact (Classical.choose_spec (pattern_covers y)).symm.trans
      (hh.trans (Classical.choose_spec (pattern_covers z)))
  calc
    _≤Nat.card Code := Nat.card_le_card_of_injective enc hinj
    _=512 := by norm_num [Code,Nat.card_sum,Nat.card_fun,Nat.card_fin,Nat.card_prod,
      Nat.card_eq_fintype_card]

instance candidate_finite : Finite Candidate := by
  classical
  let enc : Candidate→Code := fun y=>Classical.choose (pattern_covers y)
  apply Finite.of_injective enc
  intro y z he
  apply Subtype.ext
  have hh := congrArg pattern he
  exact (Classical.choose_spec (pattern_covers y)).symm.trans
    (hh.trans (Classical.choose_spec (pattern_covers z)))

end SymmetricSubgroupAsymptotics.CFSGParityEnergyEight
