import SymmetricSubgroupAsymptotics.PGroupInducedHead
import Mathlib.Combinatorics.SetFamily.LYM

/-!
# Binary intrinsic heads of actual induced subrepresentations

The checked prime-independent ordered transversal and raising construction
is combined with Sperner's theorem for the Boolean grid. The finite group,
subgroup, fibre representation and injected domain are all the original
objects. The bounded space is the domain's own coinvariants, or equivalently
its invariant linear forms. No supplied module-capacity input, splitting,
regular subgroup, or ambient-coinvariant replacement is used.

This module does not assert an all-normal permutation-group rank bound,
a weighted menu-mass estimate, or physical family coverage.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics

open CoinducedLeadingCoordinates RepresentationLeadingAntichain

private def binaryPointSupport {t : ℕ} (a : Fin t → Fin 2) : Finset (Fin t) :=
  Finset.univ.filter (fun i => a i=1)

private theorem binaryPointSupport_subset_iff {t : ℕ} (a b : Fin t → Fin 2) :
    binaryPointSupport a ⊆ binaryPointSupport b ↔ a≤b := by
  constructor
  · intro h i
    by_cases ha : a i=1
    · have hi : i∈binaryPointSupport a := by
        simp only [binaryPointSupport,Finset.mem_filter,Finset.mem_univ,true_and,ha]
      have hb : b i=1 := (Finset.mem_filter.mp (h hi)).2
      exact le_of_eq (ha.trans hb.symm)
    · have hz : a i=0 := by have := (a i).isLt; omega
      rw [hz]
      exact Fin.zero_le _
  · intro h i hi
    simp only [binaryPointSupport,Finset.mem_filter,Finset.mem_univ,true_and] at hi ⊢
    have hab := h i
    have hb := (b i).isLt
    have ha : (a i).val=1 := congrArg Fin.val hi
    change (a i).val≤(b i).val at hab
    apply Fin.ext
    change (b i).val=1
    omega

/-- Actual Boolean-grid labels, with arbitrary finite fibre copies. The
separation condition forbids both comparable labels and duplicate labels
inside each fibre; the conclusion includes t=0. -/
theorem binaryGrid_fibre_antichain_card_le_width {ι κ : Type*}
    [Fintype ι] [Fintype κ] (t : ℕ) (fibre : ι → κ)
    (point : ι → Fin t → Fin 2)
    (hsep : ∀ i j, fibre i=fibre j → point i≤point j → i=j) :
    Fintype.card ι ≤ Fintype.card κ*t.choose (t/2) := by
  classical
  have hfibre (c : κ) : Fintype.card {i : ι // fibre i=c}≤t.choose (t/2) := by
    let f : {i : ι // fibre i=c} → Finset (Fin t) :=
      fun i => binaryPointSupport (point i.1)
    let A : Finset (Finset (Fin t)) := Finset.univ.image f
    have hinj : Function.Injective f := by
      intro i j hij
      apply Subtype.ext
      exact hsep i.1 j.1 (i.2.trans j.2.symm)
        ((binaryPointSupport_subset_iff _ _).mp (le_of_eq hij))
    have hA : IsAntichain (· ⊆ ·) (A : Set (Finset (Fin t))) := by
      intro a ha b hb hne hab
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
      have hij : i=j := by
        apply Subtype.ext
        exact hsep i.1 j.1 (i.2.trans j.2.symm)
          ((binaryPointSupport_subset_iff _ _).mp hab)
      exact hne (congrArg f hij)
    have hcard : A.card=Fintype.card {i : ι // fibre i=c} := by
      change (Finset.univ.image f).card=Fintype.card {i : ι // fibre i=c}
      rw [Finset.card_image_of_injective _ hinj,Finset.card_univ]
    rw [← hcard]
    simpa only [Fintype.card_fin] using hA.sperner
  calc
    Fintype.card ι = Fintype.card (Σ c : κ, {i : ι // fibre i=c}) :=
      (Fintype.card_congr (Equiv.sigmaFiberEquiv fibre)).symm
    _ = ∑ c : κ, Fintype.card {i : ι // fibre i=c} := Fintype.card_sigma
    _ ≤ ∑ _c : κ, t.choose (t/2) := Finset.sum_le_sum (fun c _ => hfibre c)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul]

variable {k G V U : Type} [Field k] [Group G] [Finite G]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  [AddCommGroup U] [Module k U]

/-- Any representation injected equivariantly into the original coinduced
module satisfies the intrinsic-head width bound. Every datum in the
transversal and raising argument is constructed from the actual 2-group. -/
theorem twoGroup_coinduced_injective_coinvariant_head_le
    (hG : IsPGroup 2 G) (H : Subgroup G) (ρ : Representation k H V)
    (t : ℕ) (hindex : H.index=2^t) (τ : Representation k G U)
    (φ : τ.IntertwiningMap (Representation.coind H.subtype ρ))
    (hinjective : Function.Injective φ) :
    Module.finrank k τ.Coinvariants ≤ Module.finrank k V * t.choose (t/2) := by
  classical
  obtain ⟨D⟩ := pGroup_orderedCosetTransversal hG H t hindex
  let E := D.finRows
  let b := Module.finBasis k V
  let C : U →ₗ[k] (Fin (2^t * Module.finrank k V) → k) :=
    (coordinates H ρ E.repr b).comp φ.toLinearMap
  have hfactor : ∀ x : G, ∃ h : G, h∈H ∧ ∃ a : Fin (2^t), x=h*E.repr a :=
    fun x => E.factor x (Subgroup.mem_top x)
  have hC : Function.Injective C :=
    (coordinates_injective H ρ E.repr b hfactor).comp hinjective
  letI : FiniteDimensional k U := FiniteDimensional.of_injective C hC
  obtain ⟨leading, hseparated⟩ :=
    coinvariant_labels_of_raising τ C hC
      (fullComparable (primeCosetFinComparable 2 t))
      (ThreeGroupHead.intertwiner_raising H ρ E.repr b hfactor
        (primeCosetFinComparable 2 t) E.unique E.triangular τ φ)
  let fibre : Fin (Module.finrank k τ.Coinvariants) → Fin (Module.finrank k V) :=
    fun i => (finProdFinEquiv.symm (leading i)).2
  let point : Fin (Module.finrank k τ.Coinvariants) → Fin t → Fin 2 :=
    fun i => primeCosetFinPoint 2 t (finProdFinEquiv.symm (leading i)).1
  have hsep : ∀ i j, fibre i=fibre j → point i≤point j → i=j := by
    intro i j hf hp
    by_contra hij
    apply hseparated hij
    exact ⟨hf, (primeCosetFinComparable_iff_point_le 2 t _ _).mpr hp⟩
  simpa only [Fintype.card_fin] using
    binaryGrid_fibre_antichain_card_le_width t fibre point hsep

/-- Invariant forms on the original domain of an actual injective
intertwiner are the dual of that domain's intrinsic coinvariants. -/
theorem twoGroup_coinduced_injective_head_le
    (hG : IsPGroup 2 G) (H : Subgroup G) (ρ : Representation k H V)
    (t : ℕ) (hindex : H.index=2^t) (τ : Representation k G U)
    (φ : τ.IntertwiningMap (Representation.coind H.subtype ρ))
    (hinjective : Function.Injective φ) :
    Module.finrank k (τ.IntertwiningMap (Representation.trivial k G k)) ≤
      Module.finrank k V * t.choose (t/2) := by
  letI : Fintype G := Fintype.ofFinite G
  letI : FiniteDimensional k U := FiniteDimensional.of_injective φ.toLinearMap hinjective
  rw [representationHead_finrank_eq_coinvariants]
  exact twoGroup_coinduced_injective_coinvariant_head_le hG H ρ t hindex τ φ hinjective

/-- Invariant forms on the original coinduced subrepresentation have the
same dimension as its intrinsic coinvariants. -/
theorem twoGroup_coinduced_subrepresentationHead_le
    (hG : IsPGroup 2 G) (H : Subgroup G) (ρ : Representation k H V)
    (t : ℕ) (hindex : H.index=2^t)
    (M : Subrepresentation (Representation.coind H.subtype ρ)) :
    Module.finrank k (M.toRepresentation.IntertwiningMap (Representation.trivial k G k)) ≤
      Module.finrank k V * t.choose (t/2) :=
  twoGroup_coinduced_injective_head_le (U := M.toSubmodule) hG H ρ t hindex
    M.toRepresentation (ThreeGroupHead.inclusion _ M) Subtype.val_injective

/-- The invariant head of every original induced subrepresentation. -/
theorem twoGroup_induced_subrepresentationHead_le
    (hG : IsPGroup 2 G) (H : Subgroup G) (ρ : Representation k H V)
    (t : ℕ) (hindex : H.index=2^t)
    (M : Subrepresentation (Representation.ind H.subtype ρ)) :
    Module.finrank k (M.toRepresentation.IntertwiningMap (Representation.trivial k G k)) ≤
      Module.finrank k V * t.choose (t/2) := by
  let e := inducedElementCoinducedEquiv H ρ
  exact twoGroup_coinduced_injective_head_le (U := M.toSubmodule) hG H ρ t hindex
    M.toRepresentation (e.toIntertwiningMap.comp (ThreeGroupHead.inclusion _ M))
    (e.toLinearEquiv.injective.comp Subtype.val_injective)

/-- Exact prime-character dimension on an abstract original domain;
specializing the domain later avoids nested-subtype quotient elaboration. -/
theorem twoGroup_coinduced_injective_characterHead_le
    {q : ℕ} [Fact q.Prime] {G₀ V₀ U₀ : Type} [Group G₀] [Finite G₀]
    [AddCommGroup V₀] [Module (ZMod q) V₀] [FiniteDimensional (ZMod q) V₀]
    [AddCommGroup U₀] [Module (ZMod q) U₀]
    (hG : IsPGroup 2 G₀) (H : Subgroup G₀) (ρ : Representation (ZMod q) H V₀)
    (t : ℕ) (hindex : H.index=2^t) (τ : Representation (ZMod q) G₀ U₀)
    (φ : τ.IntertwiningMap (Representation.coind H.subtype ρ))
    (hinjective : Function.Injective φ) :
    Module.finrank (ZMod q) (primeActionCharacters q (representationGroupAction τ)) ≤
      Module.finrank (ZMod q) V₀ * t.choose (t/2) := by
  letI : Fintype G₀ := Fintype.ofFinite G₀
  letI : FiniteDimensional (ZMod q) U₀ :=
    FiniteDimensional.of_injective φ.toLinearMap hinjective
  rw [representationCharacterHead_finrank_eq_coinvariants]
  exact twoGroup_coinduced_injective_coinvariant_head_le hG H ρ t hindex τ φ hinjective

/-- Prime-valued invariant characters of every exact original induced
subrepresentation, without a regular-subgroup or splitting hypothesis. -/
theorem twoGroup_induced_subrepresentationCharacterHead_le
    {q : ℕ} [Fact q.Prime] {G₀ V₀ : Type} [Group G₀] [Finite G₀]
    [AddCommGroup V₀] [Module (ZMod q) V₀] [FiniteDimensional (ZMod q) V₀]
    (hG : IsPGroup 2 G₀) (H : Subgroup G₀) (ρ : Representation (ZMod q) H V₀)
    (t : ℕ) (hindex : H.index=2^t)
    (M : Subrepresentation (Representation.ind H.subtype ρ)) :
    Module.finrank (ZMod q)
      (primeActionCharacters (A := G₀) (G := Multiplicative M.toSubmodule) q
        (representationGroupAction (p := q) (G := G₀) (V := M.toSubmodule)
          M.toRepresentation)) ≤
        Module.finrank (ZMod q) V₀ * t.choose (t/2) := by
  let e := inducedElementCoinducedEquiv H ρ
  exact twoGroup_coinduced_injective_characterHead_le (U₀ := M.toSubmodule) hG H ρ t hindex
    M.toRepresentation (e.toIntertwiningMap.comp (ThreeGroupHead.inclusion _ M))
    (e.toLinearEquiv.injective.comp Subtype.val_injective)

end SymmetricSubgroupAsymptotics
