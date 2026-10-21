import SymmetricSubgroupAsymptotics.CFSGTypeARootGeometryAction
import SymmetricSubgroupAsymptotics.CFSGProjectiveIncidence

/-! The incidence graph of original projective points and hyperplanes is
recovered intrinsically from distinct root groups with nontrivial
intersection. The actual automorphism permutation preserves this graph. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGTypeARootIncidenceGraph
open Matrix Module LinearMap Submodule CFSGTypeAProjectivePointRoots CFSGTypeAHyperplaneRoots
open CFSGTypeARootMembership CFSGTypeARootLabels CFSGTypeARootIncidence
open CFSGProjectiveIncidence CFSGTypeARootGeometryAction
variable {F n : Type*} [Field F] [Fintype n] [DecidableEq n]

theorem pointLabel_inf_ne_bot_eq (hn : 3≤Fintype.card n)
    (p q : Points (F:=F) (n:=n)) (h : pointLabel p ⊓ pointLabel q≠⊥) : p=q := by
  obtain ⟨x,hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h
  have hxval : (x : PSL (F:=F) (n:=n))≠1 := fun he => hx (Subtype.ext he)
  obtain ⟨g,hgx⟩ := x.property.1
  have hg : g.toAdd.val≠0 := by
    intro he
    have hz : g=1 := congrArg Multiplicative.ofAdd (Subtype.ext he)
    rw [hz,map_one] at hgx
    exact hxval hgx.symm
  have hmem : projection (transvectionSL g.toAdd.property)∈pointRoot q.rep := by
    change pointRootHom p.rep g∈pointRoot q.rep
    rw [hgx]
    exact x.property.2
  have hc := (pointRoot_mem_iff_centre hn g.toAdd.property hg p.rep_nonzero).mp hmem
  apply Projectivization.submodule_injective
  rw [Projectivization.submodule_eq,Projectivization.submodule_eq]
  exact hc

theorem hyperplaneLabel_inf_ne_bot_eq (hn : 3≤Fintype.card n)
    (f g : Hyperplanes (F:=F) (n:=n)) (h : hyperplaneLabel f ⊓ hyperplaneLabel g≠⊥) : f=g := by
  obtain ⟨x,hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h
  have hxval : (x : PSL (F:=F) (n:=n))≠1 := fun he => hx (Subtype.ext he)
  obtain ⟨v,hvx⟩ := x.property.1
  have hv : v.toAdd.val≠0 := by
    intro he
    have hz : v=1 := congrArg Multiplicative.ofAdd (Subtype.ext he)
    rw [hz,map_one] at hvx
    exact hxval hvx.symm
  have hmem : projection (transvectionSL v.toAdd.property)∈hyperplaneRoot g.rep := by
    change hyperplaneRootHom f.rep v∈hyperplaneRoot g.rep
    rw [hvx]
    exact x.property.2
  apply hyperplaneLabel_injective hn
  exact (hyperplaneRoot_eq_iff_axis hn f.rep_nonzero g.rep_nonzero).mpr
    ((hyperplaneRoot_mem_iff_axis hn v.toAdd.property f.rep_nonzero g.rep_nonzero hv).mp hmem)

abbrev graph := CFSGIncidenceOrientation.incidenceGraph (Incident (F:=F) (n:=n))

theorem graph_adj_iff_roots (hn : 3≤Fintype.card n) (x y : Vertex (F:=F) (n:=n)) :
    (graph (F:=F) (n:=n)).Adj x y ↔ x≠y ∧ rootLabel x ⊓ rootLabel y≠⊥ := by
  cases x with
  | inl p =>
    cases y with
    | inl q =>
      change False ↔ Sum.inl p≠Sum.inl q ∧ pointLabel p ⊓ pointLabel q≠⊥
      constructor
      · exact False.elim
      · rintro ⟨hne,h⟩
        exact hne (congrArg Sum.inl (pointLabel_inf_ne_bot_eq hn p q h))
    | inr f =>
      change Incident p f ↔ Sum.inl p≠Sum.inr f ∧ pointLabel p ⊓ hyperplaneLabel f≠⊥
      constructor
      · intro h
        exact ⟨Sum.inl_ne_inr,(labels_inf_ne_bot_iff hn p f).mpr h⟩
      · rintro ⟨_,h⟩
        exact (labels_inf_ne_bot_iff hn p f).mp h
  | inr f =>
    cases y with
    | inl p =>
      change Incident p f ↔ Sum.inr f≠Sum.inl p ∧ hyperplaneLabel f ⊓ pointLabel p≠⊥
      constructor
      · intro h
        refine ⟨Sum.inr_ne_inl,?_⟩
        simpa only [inf_comm] using (labels_inf_ne_bot_iff hn p f).mpr h
      · rintro ⟨_,h⟩
        apply (labels_inf_ne_bot_iff hn p f).mp
        simpa only [inf_comm] using h
    | inr g =>
      change False ↔ Sum.inr f≠Sum.inr g ∧ hyperplaneLabel f ⊓ hyperplaneLabel g≠⊥
      constructor
      · exact False.elim
      · rintro ⟨hne,h⟩
        exact hne (congrArg Sum.inr (hyperplaneLabel_inf_ne_bot_eq hn f g h))

section Automorphisms
variable [Finite F] {d : ℕ}

theorem rootPermutation_graph_iff (p : ℕ) [Fact p.Prime] [CharP F p] (hn : 3≤d)
    (a : MulAut (PSL (F:=F) (n:=Fin d))) (x y : Vertex (F:=F) (n:=Fin d)) :
    (graph (F:=F) (n:=Fin d)).Adj (rootPermutationHom p hn a x) (rootPermutationHom p hn a y) ↔
      (graph (F:=F) (n:=Fin d)).Adj x y := by
  have hdim : 3≤Fintype.card (Fin d) := by simpa using hn
  rw [graph_adj_iff_roots hdim,graph_adj_iff_roots hdim,
    rootLabel_rootPermutation,rootLabel_rootPermutation,
    ←Subgroup.map_inf _ _ _ a.injective]
  have hne : rootPermutationHom p hn a x≠rootPermutationHom p hn a y ↔ x≠y :=
    (rootPermutationHom p hn a).injective.ne_iff
  rw [hne]
  have hb : (rootLabel x ⊓ rootLabel y).map a.toMonoidHom≠⊥ ↔
      rootLabel x ⊓ rootLabel y≠⊥ := by
    constructor
    · intro h he
      rw [he,Subgroup.map_bot] at h
      exact h rfl
    · intro h he
      apply h
      exact a.mapSubgroup.injective (he.trans (Subgroup.map_bot _).symm)
  rw [hb]

def rootGraphEquiv (p : ℕ) [Fact p.Prime] [CharP F p] (hn : 3≤d)
    (a : MulAut (PSL (F:=F) (n:=Fin d))) :
    graph (F:=F) (n:=Fin d) ≃g graph (F:=F) (n:=Fin d) where
  toEquiv := rootPermutationHom p hn a
  map_rel_iff' := rootPermutation_graph_iff p hn a _ _

omit [Finite F] in
theorem graph_connected (hn : 3≤d) : (graph (F:=F) (n:=Fin d)).Connected := by
  letI : Nonempty (Fin d) := ⟨⟨0,by omega⟩⟩
  exact CFSGIncidenceOrientation.connected _ (common_hyperplane (by simpa using hn))
    (hyperplane_has_point (by simpa using (show 2≤d by omega)))

end Automorphisms
end SymmetricSubgroupAsymptotics.CFSGTypeARootIncidenceGraph
