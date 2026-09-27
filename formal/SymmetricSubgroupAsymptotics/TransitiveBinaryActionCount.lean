import SymmetricSubgroupAsymptotics.TransitiveBinaryGenerators
import SymmetricSubgroupAsymptotics.BinarySylowCoverage
import SymmetricSubgroupAsymptotics.BinaryPermutationOrder

/-! Counting a finite family of actual permutation actions by tuples in
one chosen Sylow subgroup. Every tuple is obtained by original ambient
conjugation and generates the transported original subgroup. Equality of
tuples forces actual permutation conjugacy, so a conjugacy-separated
family injects into the tuple space. No abstract-isomorphism test or
normalizer identification is used. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics

/-- A tuple generating an actual subgroup generates precisely that same
subgroup after inclusion in its original ambient group. -/
theorem subgroup_generating_tuple_closure {G : Type*} [Group G]
    (H : Subgroup G) {d : ℕ} (g : Fin d → H)
    (hg : Subgroup.closure (Set.range g)=⊤) :
    Subgroup.closure (Set.range (fun j => (g j : G)))=H := by
  have h := congrArg (Subgroup.map H.subtype) hg
  simpa only [MonoidHom.map_closure,← Set.range_comp',Function.comp_def,
    ← MonoidHom.range_eq_map,Subgroup.range_subtype] using h

/-- Literal conjugation transports the original generating tuple and
its whole closure, not just the abstract group isomorphism type. -/
theorem conjugated_generating_tuple_closure {G : Type*} [Group G]
    (H : Subgroup G) {d : ℕ} (g : Fin d → H)
    (hg : Subgroup.closure (Set.range g)=⊤) (c : G) :
    Subgroup.closure (Set.range (fun j => MulAut.conj c (g j : G)))=
      MulAut.conj c • H := by
  have h := congrArg (Subgroup.map (MulAut.conj c).toMonoidHom)
    (subgroup_generating_tuple_closure H g hg)
  simpa only [MonoidHom.map_closure,← Set.range_comp',Function.comp_def,
    Subgroup.pointwise_smul_def] using h

/-- The only family separation assumption is injectivity modulo actual
ambient conjugacy. Source subgroups may repeat only when their labels
are equal. No transitivity is needed for this general tuple argument. -/
theorem pGroup_conjugacySeparated_family_card_le_tuple_power
    {G ι : Type*} [Group G] [Finite G] [Finite ι]
    (p : ℕ) [Fact p.Prime] (P : Sylow p G)
    (actions : ι → Subgroup G) (hgroup : ∀ i, IsPGroup p (actions i))
    (d : ℕ)
    (hgen : ∀ i, ∃ g : Fin d → actions i, Subgroup.closure (Set.range g)=⊤)
    (hsep : ∀ i j (c : G), MulAut.conj c • actions i=actions j → i=j) :
    Nat.card ι≤Nat.card (P : Subgroup G)^d := by
  classical
  let c (i : ι) : G :=
    (pGroup_conjugate_le_chosen_sylow P (actions i) (hgroup i)).choose
  have hc (i : ι) : MulAut.conj (c i) • actions i≤(P : Subgroup G) :=
    (pGroup_conjugate_le_chosen_sylow P (actions i) (hgroup i)).choose_spec
  let g (i : ι) : Fin d → actions i := (hgen i).choose
  have hg (i : ι) : Subgroup.closure (Set.range (g i))=⊤ := (hgen i).choose_spec
  let tuple (i : ι) : Fin d → (P : Subgroup G) := fun j =>
    ⟨MulAut.conj (c i) (g i j : G), hc i
      (Subgroup.smul_mem_pointwise_smul (g i j : G) (MulAut.conj (c i))
        (actions i) (g i j).property)⟩
  have hclosure (i : ι) :
      Subgroup.closure (Set.range (fun j => (tuple i j : G)))=
        MulAut.conj (c i) • actions i :=
    conjugated_generating_tuple_closure (actions i) (g i) (hg i) (c i)
  have hinj : Function.Injective tuple := by
    intro i j hij
    have he : MulAut.conj (c i) • actions i=MulAut.conj (c j) • actions j := by
      rw [← hclosure i,← hclosure j]
      exact congrArg (fun f : Fin d → (P : Subgroup G) =>
        Subgroup.closure (Set.range (fun t => (f t : G)))) hij
    apply hsep i j ((c j)⁻¹*c i)
    calc
      MulAut.conj ((c j)⁻¹*c i) • actions i =
          MulAut.conj ((c j)⁻¹) • (MulAut.conj (c i) • actions i) := by
        rw [map_mul,mul_smul]
      _ = MulAut.conj ((c j)⁻¹) • (MulAut.conj (c j) • actions j) :=
        congrArg (fun H : Subgroup G => MulAut.conj ((c j)⁻¹) • H) he
      _ = actions j := by
        rw [← mul_smul,← map_mul,inv_mul_cancel,map_one,one_smul]
  calc
    Nat.card ι≤Nat.card (Fin d → (P : Subgroup G)) :=
      Nat.card_le_card_of_injective tuple hinj
    _ = Nat.card (P : Subgroup G)^d := by rw [Nat.card_fun,Nat.card_fin]

/-- Every finite family of pairwise nonconjugate original transitive
binary actions of degree2^k is bounded by tuples of the proved cumulative
width in one actual Sylow subgroup of the SAME permutation group. -/
theorem transitiveBinary_action_family_card_le_cumulative
    {X : Type} [Finite X] {ι : Type*} [Finite ι]
    (k : ℕ) (P : Sylow 2 (Equiv.Perm X))
    (actions : ι → Subgroup (Equiv.Perm X))
    (htrans : ∀ i, MulAction.IsPretransitive (actions i) X)
    (hgroup : ∀ i, IsPGroup 2 (actions i)) (hdegree : Nat.card X=2^k)
    (hsep : ∀ i j (c : Equiv.Perm X),
      MulAut.conj c • actions i=actions j → i=j) :
    Nat.card ι≤Nat.card (P : Subgroup (Equiv.Perm X))^binaryCumulativeWidth k := by
  apply pGroup_conjugacySeparated_family_card_le_tuple_power 2 P actions hgroup
    (binaryCumulativeWidth k) ?_ hsep
  intro i
  letI : MulAction.IsPretransitive (actions i) X := htrans i
  exact transitiveBinary_exists_generating_tuple k (actions i) (hgroup i) hdegree

/-- The actual permutation Sylow order eliminates the chosen Sylow from
the numerical bound; the original conjugacy separation is unchanged. -/
theorem transitiveBinary_action_family_card_le_degree
    {X : Type} [Finite X] {ι : Type*} [Finite ι]
    (k : ℕ) (P : Sylow 2 (Equiv.Perm X))
    (actions : ι → Subgroup (Equiv.Perm X))
    (htrans : ∀ i, MulAction.IsPretransitive (actions i) X)
    (hgroup : ∀ i, IsPGroup 2 (actions i)) (hdegree : Nat.card X=2^k)
    (hsep : ∀ i j (c : Equiv.Perm X),
      MulAut.conj c • actions i=actions j → i=j) :
    Nat.card ι≤2^((2^k-1)*binaryCumulativeWidth k) := by
  have h := transitiveBinary_action_family_card_le_cumulative
    k P actions htrans hgroup hdegree hsep
  have hP : Nat.card (P : Subgroup (Equiv.Perm X))=2^(2^k-1) :=
    binary_sylow_permutation_card k hdegree P
  simpa only [hP,← pow_mul] using h

end SymmetricSubgroupAsymptotics
