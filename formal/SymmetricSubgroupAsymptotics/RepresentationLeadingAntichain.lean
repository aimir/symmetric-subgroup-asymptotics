import Mathlib.RepresentationTheory.Coinvariants
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Finset.Max
import Mathlib.Order.WellFounded
import Mathlib.Order.Antichain
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Leading labels of lifts of a coinvariant basis

The acted-on space below is the actual representation whose head is being
bounded. An injective coordinate map may come from an ordered ambient basis;
it need not identify this space with the whole ambient coordinate space.

The relation on full coordinate labels is separate from their total order.
In a fibre application it must include the same-fibre condition. The only
raising hypothesis explicitly supplies an actual group element. No group
transversal, p-group, or poset-width assertion is built into this lemma.

The minimization ranges over all independent quotient lift families of the
correct size. It does not fix the quotient basis: cancellation changes that
basis by an elementary transvection. The intrinsic-coinvariant corollary
uses coinvariants of the acted-on space itself, not ambient coinvariants.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.RepresentationLeadingAntichain

variable {k V W G I : Type*} [Field k]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  {n : ℕ}

/-- The greatest nonzero full coordinate label, in the specified total order. -/
def HasLeading (coordinates : V →ₗ[k] (Fin n → k)) (v : V) (a : Fin n) : Prop :=
  coordinates v a ≠ 0 ∧ ∀ b : Fin n, a < b → coordinates v b = 0

theorem exists_leading (coordinates : V →ₗ[k] (Fin n → k))
    (hinjective : Function.Injective coordinates) {v : V} (hv : v ≠ 0) :
    ∃ a, HasLeading coordinates v a := by
  classical
  have hsupport : ∃ a : Fin n, coordinates v a ≠ 0 := by
    by_contra! h
    apply hv
    apply hinjective
    ext a
    simpa only [map_zero, Pi.zero_apply] using h a
  let s : Finset (Fin n) := Finset.univ.filter (fun a => coordinates v a ≠ 0)
  have hs : s.Nonempty := by
    obtain ⟨a, ha⟩ := hsupport
    exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩⟩
  refine ⟨s.max' hs, (Finset.mem_filter.mp (s.max'_mem hs)).2, ?_⟩
  intro b hb
  by_contra hnonzero
  have hmem : b ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ b, hnonzero⟩
  exact (not_lt_of_ge (s.le_max' b hmem)) hb

/-- Cancelling equal leading coordinates strictly lowers the leading label
whenever the resulting vector is nonzero. The coefficient is explicit. -/
theorem cancel_leading (coordinates : V →ₗ[k] (Fin n → k))
    (hinjective : Function.Injective coordinates) {u v : V} {a : Fin n}
    (hu : HasLeading coordinates u a) (hv : HasLeading coordinates v a)
    (hnonzero : v - (coordinates v a / coordinates u a) • u ≠ 0) :
    ∃ b : Fin n, b < a ∧
      HasLeading coordinates (v - (coordinates v a / coordinates u a) • u) b := by
  let z := v - (coordinates v a / coordinates u a) • u
  have hzero : coordinates z a = 0 := by
    simp only [z, map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [div_mul_cancel₀ _ hu.1, sub_self]
  have habove : ∀ b : Fin n, a < b → coordinates z b = 0 := by
    intro b hb
    simp only [z, map_sub, map_smul, Pi.sub_apply, Pi.smul_apply,
      hu.2 b hb, hv.2 b hb, smul_zero, sub_self]
  obtain ⟨b, hb⟩ := exists_leading coordinates hinjective hnonzero
  refine ⟨b, ?_, hb⟩
  by_contra hlt
  rcases lt_or_eq_of_le (le_of_not_gt hlt) with hgt | heq
  · exact hb.1 (habove b hgt)
  · subst b
    exact hb.1 hzero

/-- Candidates vary both their vectors and the resulting quotient basis.
Full size will imply spanning; independence is the property preserved by
the elementary cancellation operation. -/
structure LiftFamily (coordinates : V →ₗ[k] (Fin n → k)) (q : V →ₗ[k] W)
    (I : Type*) where
  vector : I → V
  label : I → Fin n
  leading : ∀ i, HasLeading coordinates (vector i) (label i)
  independent : LinearIndependent k (fun i => q (vector i))

private theorem independent_cancel [DecidableEq I]
    (q : V →ₗ[k] W) (v : I → V)
    (hv : LinearIndependent k (fun i => q (v i)))
    {i j : I} (hij : i ≠ j) (u : V) (hu : q u = q (v i)) (c : k) :
    LinearIndependent k (fun t => q (Function.update v j (v j - c • u) t)) := by
  let coefficients : I → k := fun t => if t = j then -c else 0
  have hzero : coefficients i = 0 := by simp [coefficients, hij]
  have hli := (linearIndependent_add_smul_iff
    (v := fun t => q (v t)) (c := coefficients) (i := i) hzero).mpr hv
  have he : (fun t => q (Function.update v j (v j - c • u) t)) =
      (fun t => q (v t)) + (fun t => coefficients t • q (v i)) := by
    funext t
    by_cases ht : t = j
    · subst t
      simp [coefficients, map_sub, map_smul, hu, sub_eq_add_neg]
    · simp [coefficients, Function.update, ht]
  rw [he]
  exact hli

/-- For an actual trivial-action quotient, some basis admits lifts with
pairwise incomparable full leading labels. The initial basis supplies only
the dimension and a nonempty candidate class; it is not held fixed.

The raising property is an explicit premise about the actual action. -/
theorem exists_basis_lifts [Group G] [Fintype I]
    (ρ : Representation k G V)
    (coordinates : V →ₗ[k] (Fin n → k)) (hinjective : Function.Injective coordinates)
    (q : V →ₗ[k] W) (hsurjective : Function.Surjective q)
    (htrivial : ∀ g v, q (ρ g v) = q v)
    (initialBasis : Module.Basis I k W) (R : Fin n → Fin n → Prop)
    (hraising : ∀ (v : V) (a b : Fin n), HasLeading coordinates v a → R a b →
      ∃ g : G, HasLeading coordinates (ρ g v) b) :
    ∃ (basis : Module.Basis I k W) (v : I → V) (label : I → Fin n),
      (∀ i, q (v i) = basis i) ∧
      (∀ i, HasLeading coordinates (v i) (label i)) ∧
      Pairwise (fun i j => ¬ R (label i) (label j)) := by
  classical
  letI : FiniteDimensional k W := initialBasis.finiteDimensional_of_finite
  let first : I → V := fun i => (hsurjective (initialBasis i)).choose
  have hfirst : ∀ i, q (first i) = initialBasis i :=
    fun i => (hsurjective (initialBasis i)).choose_spec
  have hfirstIndependent : LinearIndependent k (fun i => q (first i)) := by
    simpa only [hfirst] using initialBasis.linearIndependent
  have hfirstNonzero : ∀ i, first i ≠ 0 := by
    intro i hi
    exact hfirstIndependent.ne_zero i (by rw [hi, map_zero])
  choose firstLabel hfirstLabel using
    (fun i => exists_leading coordinates hinjective (hfirstNonzero i))
  letI : Nonempty (LiftFamily coordinates q I) :=
    ⟨⟨first, firstLabel, hfirstLabel, hfirstIndependent⟩⟩
  let weight : LiftFamily coordinates q I → ℕ := fun f => ∑ i, (f.label i).val
  let f : LiftFamily coordinates q I := Function.argmin weight
  have hminimal (other : LiftFamily coordinates q I) : ¬ weight other < weight f :=
    Function.not_lt_argmin weight other
  have hincomparable : Pairwise (fun i j => ¬ R (f.label i) (f.label j)) := by
    intro i j hij hrelated
    obtain ⟨g, hg⟩ := hraising (f.vector i) (f.label i) (f.label j)
      (f.leading i) hrelated
    let c : k := coordinates (f.vector j) (f.label j) /
      coordinates (ρ g (f.vector i)) (f.label j)
    let changed : I → V := Function.update f.vector j (f.vector j - c • ρ g (f.vector i))
    have hindependent : LinearIndependent k (fun t => q (changed t)) :=
      independent_cancel q f.vector f.independent hij (ρ g (f.vector i))
        (htrivial g (f.vector i)) c
    have hnonzero : f.vector j - c • ρ g (f.vector i) ≠ 0 := by
      intro hz
      apply hindependent.ne_zero j
      simp only [changed, Function.update_self, hz, map_zero]
    obtain ⟨b, hb, hleading⟩ := cancel_leading coordinates hinjective hg
      (f.leading j) hnonzero
    let other : LiftFamily coordinates q I := {
      vector := changed
      label := Function.update f.label j b
      leading := by
        intro t
        by_cases ht : t = j
        · subst t
          simpa only [changed, Function.update_self] using hleading
        · simpa only [changed, Function.update_of_ne ht] using f.leading t
      independent := hindependent }
    apply hminimal other
    change (∑ t, (Function.update f.label j b t).val) < ∑ t, (f.label t).val
    apply Finset.sum_lt_sum
    · intro t _
      by_cases ht : t = j
      · subst t
        simpa only [Function.update_self] using hb.le
      · simp only [Function.update_of_ne ht, le_refl]
    · exact ⟨j, Finset.mem_univ j, by simpa only [Function.update_self] using hb⟩
  let basis : Module.Basis I k W :=
    basisOfLinearIndependentOfCardEqFinrank' (fun i => q (f.vector i)) f.independent
      (Module.finrank_eq_card_basis initialBasis).symm
  refine ⟨basis, f.vector, f.label, ?_, f.leading, hincomparable⟩
  intro i
  simp only [basis, coe_basisOfLinearIndependentOfCardEqFinrank']

/-- Reflexivity makes the full leading labels distinct as well as an
antichain. In particular equal full labels are handled by identity raising. -/
theorem labels_injective {label : I → Fin n} {R : Fin n → Fin n → Prop}
    (hreflexive : Reflexive R)
    (hpairwise : Pairwise (fun i j => ¬ R (label i) (label j))) :
    Function.Injective label := by
  intro i j heq
  by_contra hij
  apply hpairwise hij
  rw [heq]
  exact hreflexive _

theorem labels_antichain {label : I → Fin n} {R : Fin n → Fin n → Prop}
    (hpairwise : Pairwise (fun i j => ¬ R (label i) (label j))) :
    IsAntichain R (Set.range label) := by
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hne hrelated
  exact hpairwise (fun hij => hne (congrArg label hij)) hrelated

/-- The intrinsic coinvariant head of the actual acted-on space. For a
subrepresentation application, instantiate V with that subrepresentation;
the ambient representation's coinvariants are not used here. -/
theorem exists_coinvariant_basis_lifts [Group G] [FiniteDimensional k V]
    (ρ : Representation k G V)
    (coordinates : V →ₗ[k] (Fin n → k)) (hinjective : Function.Injective coordinates)
    (R : Fin n → Fin n → Prop)
    (hraising : ∀ (v : V) (a b : Fin n), HasLeading coordinates v a → R a b →
      ∃ g : G, HasLeading coordinates (ρ g v) b) :
    ∃ (basis : Module.Basis (Fin (Module.finrank k ρ.Coinvariants)) k ρ.Coinvariants)
      (v : Fin (Module.finrank k ρ.Coinvariants) → V)
      (label : Fin (Module.finrank k ρ.Coinvariants) → Fin n),
      (∀ i, Representation.Coinvariants.mk ρ (v i) = basis i) ∧
      (∀ i, HasLeading coordinates (v i) (label i)) ∧
      Pairwise (fun i j => ¬ R (label i) (label j)) :=
  exists_basis_lifts ρ coordinates hinjective (Representation.Coinvariants.mk ρ)
    (Representation.Coinvariants.mk_surjective ρ)
    (Representation.Coinvariants.mk_self_apply ρ)
    (Module.finBasis k ρ.Coinvariants) R hraising

end SymmetricSubgroupAsymptotics.RepresentationLeadingAntichain
