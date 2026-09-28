import SymmetricSubgroupAsymptotics.GrowingQuotientHotKernel

/-!
# The trivial complete comparator

For a subsingleton target there is exactly one literal normal axis and one
epimorphism onto its quotient.  Hence the complete quotient weight is one on
every source.  Any threshold at least one has empty hot set, so this branch
enters the cold row directly and never divides by a comparator degree.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

variable {G R : Type*} [Group G] [Group R]

private theorem quotient_subsingleton_of_subsingleton [Subsingleton R]
    (N : Subgroup R) : Subsingleton (R ⧸ N) := by
  constructor
  intro x y
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective N x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective N y
  exact congrArg (QuotientGroup.mk' N) (Subsingleton.elim a b)

/-- A subsingleton target contributes exactly the trivial literal quotient
map, independently of the complete source. -/
theorem completeQuotientCount_eq_one_of_subsingleton
    [Finite G] [Finite R] [Subsingleton R] (J : Subgroup G) :
    completeQuotientCount (R := R) J = 1 := by
  rw [← completeQuotientMap_card]
  letI : Subsingleton (Subgroup R) :=
    Subgroup.subsingleton_iff.mpr inferInstance
  letI : Subsingleton {N : Subgroup R // N.Normal} :=
    ⟨fun N M => Subtype.ext (Subsingleton.elim N.1 M.1)⟩
  letI (N : {N : Subgroup R // N.Normal}) : Subsingleton (R ⧸ N.1) :=
    quotient_subsingleton_of_subsingleton N.1
  letI (N : {N : Subgroup R // N.Normal}) :
      Subsingleton (GroupEpimorphism J (R ⧸ N.1)) :=
    ⟨fun f g => Subtype.ext (MonoidHom.ext fun _ => Subsingleton.elim _ _)⟩
  letI : Subsingleton (CompleteQuotientMap J R) := by
    constructor
    rintro ⟨N, f⟩ ⟨M, g⟩
    have hNM : N = M := Subsingleton.elim _ _
    subst M
    have hfg : f = g := Subsingleton.elim _ _
    subst g
    rfl
  have hnonempty : Nonempty (CompleteQuotientMap J R) := by
    let N : {N : Subgroup R // N.Normal} := ⟨⊤, by infer_instance⟩
    let f : GroupEpimorphism J (R ⧸ N.1) :=
      ⟨1, fun y => ⟨1, Subsingleton.elim _ y⟩⟩
    exact ⟨⟨N, f⟩⟩
  exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, hnonempty⟩

theorem completeQuotientWeight_eq_one_of_subsingleton
    [Finite R] [Subsingleton R] {b : ℕ}
    (J : Subgroup (Equiv.Perm (Fin b))) :
    completeQuotientWeight (R := R) J = 1 := by
  unfold completeQuotientWeight
  exact_mod_cast completeQuotientCount_eq_one_of_subsingleton (R := R) J

/-- At a threshold at least one, the hot source set for a trivial comparator
is literally empty. -/
theorem completeQuotientWeight_hot_filter_empty_of_subsingleton
    [Finite R] [Subsingleton R] {b : ℕ} (t : ℝ) (ht : 1 ≤ t) :
    Finset.univ.filter
        (fun J : Subgroup (Equiv.Perm (Fin b)) =>
          t < completeQuotientWeight (R := R) J) = ∅ := by
  ext J
  simp [completeQuotientWeight_eq_one_of_subsingleton, not_lt_of_ge ht]

theorem growingQuotientThreshold_one_le {c : ℝ} (hc : 0 ≤ c) (b : ℕ) :
    1 ≤ growingQuotientThreshold c b := by
  unfold growingQuotientThreshold
  exact Real.one_le_rpow (by norm_num) (mul_nonneg hc (by positivity))

/-- The hot set is empty at every nonnegative growing threshold exponent. -/
theorem growingQuotient_hot_filter_empty_of_subsingleton
    [Finite R] [Subsingleton R] {c : ℝ} (hc : 0 ≤ c) (b : ℕ) :
    Finset.univ.filter
        (fun J : Subgroup (Equiv.Perm (Fin b)) =>
          growingQuotientThreshold c b < completeQuotientWeight (R := R) J) = ∅ :=
  completeQuotientWeight_hot_filter_empty_of_subsingleton
    (R := R) (growingQuotientThreshold c b)
      (growingQuotientThreshold_one_le hc b)

end SymmetricSubgroupAsymptotics

end
