import Mathlib.Logic.Function.Basic

/-! Coordinate edges and genuine rectangular coherence in a product
Hamming graph. Opposite edges of a nondegenerate rectangle have the
same coordinate direction; no building or automorphism theorem is an
input. The statements allow different types at different coordinates. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4HammingEdges
variable {I : Type*} {D : I → Type*}

def DirectionEdge (i : I) (x y : ∀ j, D j) : Prop :=
  x i ≠ y i ∧ ∀ j, j ≠ i → x j = y j

def ClosedAdjacent (x y : ∀ j, D j) : Prop :=
  ∀ i j, x i ≠ y i → x j ≠ y j → i = j

theorem directionEdge_index_eq {i j : I} {x y : ∀ j, D j}
    (h : DirectionEdge i x y) (hj : x j ≠ y j) : j = i := by
  by_contra hne
  exact hj (h.2 j hne)

theorem directionEdge_unique {i j : I} {x y : ∀ j, D j}
    (hi : DirectionEdge i x y) (hj : DirectionEdge j x y) : i = j :=
  directionEdge_index_eq hj hi.1

theorem directionEdge_symm {i : I} {x y : ∀ j, D j}
    (h : DirectionEdge i x y) : DirectionEdge i y x :=
  ⟨Ne.symm h.1, fun j hj => (h.2 j hj).symm⟩

theorem closedAdjacent_refl (x : ∀ j, D j) : ClosedAdjacent x x :=
  fun i j hi => False.elim (hi rfl)

theorem closedAdjacent_symm {x y : ∀ j, D j} (h : ClosedAdjacent x y) : ClosedAdjacent y x :=
  fun i j hi hj => h i j (Ne.symm hi) (Ne.symm hj)

theorem closedAdjacent_of_axis (i : I) {x y : ∀ j, D j}
    (h : ∀ j, j ≠ i → x j = y j) : ClosedAdjacent x y := by
  intro j k hj hk
  have hj' : j = i := by
    by_contra hne
    exact hj (h j hne)
  have hk' : k = i := by
    by_contra hne
    exact hk (h k hne)
  exact hj'.trans hk'.symm

theorem directionEdge_closed {i : I} {x y : ∀ j, D j}
    (h : DirectionEdge i x y) : ClosedAdjacent x y := closedAdjacent_of_axis i h.2

theorem closedAdjacent_eq_or_edge {x y : ∀ j, D j} (h : ClosedAdjacent x y) :
    x = y ∨ ∃ i, DirectionEdge i x y := by
  classical
  by_cases he : x = y
  · exact Or.inl he
  · have hn : ¬∀ i, x i = y i := fun hh => he (funext hh)
    obtain ⟨i, hi⟩ := not_forall.mp hn
    refine Or.inr ⟨i, hi, ?_⟩
    intro j hj
    by_contra hn'
    exact hj (h j i hn' hi)

theorem common_neighbors_on_axis {i : I} {a b x : ∀ j, D j}
    (hab : DirectionEdge i a b) (hxa : ClosedAdjacent x a) (hxb : ClosedAdjacent x b) :
    ∀ j, j ≠ i → x j = a j := by
  intro j hji
  by_contra hxj
  have hxi : x i = a i := by
    by_contra hni
    exact hji (hxa j i hxj hni)
  have hxjb : x j ≠ b j := by
    rw [← hab.2 j hji]
    exact hxj
  have hxib : x i ≠ b i := by
    rw [hxi]
    exact hab.1
  exact hji (hxb j i hxjb hxib)

theorem rectangle_opposite_directions {i j k l : I} {a b c d : ∀ j, D j}
    (hab : DirectionEdge i a b) (hac : DirectionEdge j a c)
    (hbd : DirectionEdge k b d) (hcd : DirectionEdge l c d)
    (hbc : ¬ClosedAdjacent b c) (hda : d ≠ a) : k = j ∧ l = i := by
  classical
  have hij : i ≠ j := by
    intro he
    apply hbc
    apply closedAdjacent_of_axis i
    intro t ht
    exact (hab.2 t ht).symm.trans (hac.2 t (by simpa only [← he] using ht))
  have hbic : b i ≠ c i := by
    rw [← hac.2 i hij]
    exact Ne.symm hab.1
  have hbjc : b j ≠ c j := by
    rw [← hab.2 j (Ne.symm hij)]
    exact hac.1
  have hkj : k = j := by
    by_contra hne
    have hbdj : b j = d j := hbd.2 j (Ne.symm hne)
    have hcdj : c j ≠ d j := by
      rw [← hbdj]
      exact Ne.symm hbjc
    have hjl : j = l := directionEdge_index_eq hcd hcdj
    have hcdi : c i = d i := hcd.2 i (by simpa only [← hjl] using hij)
    have hbdi : b i ≠ d i := by
      rw [← hcdi]
      exact hbic
    have hik : i = k := directionEdge_index_eq hbd hbdi
    apply hda
    funext t
    by_cases hti : t = i
    · subst t
      exact hcdi.symm.trans (hac.2 i hij).symm
    · exact (hbd.2 t (by simpa only [← hik] using hti)).symm.trans (hab.2 t hti).symm
  have hbdi : b i = d i := hbd.2 i (by simpa only [hkj] using hij)
  have hcdi : c i ≠ d i := by
    rw [← hbdi]
    exact Ne.symm hbic
  exact ⟨hkj, (directionEdge_index_eq hcd hcdi).symm⟩

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4HammingEdges
