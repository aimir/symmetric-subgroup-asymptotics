import SymmetricSubgroupAsymptotics.PrimeCosetGridCoordinates
import SymmetricSubgroupAsymptotics.TernaryGridWidth
import SymmetricSubgroupAsymptotics.RepresentationCoinvariantHead
import SymmetricSubgroupAsymptotics.InducedElementHead

/-!
# Intrinsic heads of actual induced subrepresentations of finite 3-groups

The actual subgroup chain supplies the triangular transversal. The actual
coinduced functions retain the original fibre representation. An injective
intertwiner transports coordinates to the original acted-on space, so the
minimization always uses that space's own coinvariants. For induction the
intertwiner is the standard finite-index induction/coinduction equivalence
composed with the actual subrepresentation inclusion.

There is no supplied transversal, raising premise, splitting, regular
subgroup, faithful replacement, or ambient-coinvariant substitution in the
final group-theoretic endpoints.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics

open CoinducedLeadingCoordinates RepresentationLeadingAntichain

namespace ThreeGroupHead

variable {k G V U : Type} [Field k] [Group G]
  [AddCommGroup V] [Module k V] [AddCommGroup U] [Module k U]
  {N d : ℕ}

/-- The original subrepresentation inclusion is an actual intertwiner. -/
def inclusion (τ : Representation k G U) (M : Subrepresentation τ) :
    M.toRepresentation.IntertwiningMap τ where
  toLinearMap := M.toSubmodule.subtype
  isIntertwining' g := by ext v; rfl

/-- Restrict the coordinate raising proof along an actual injective
intertwiner. The new vectors remain in the original domain representation. -/
theorem intertwiner_raising
    (H : Subgroup G) (ρ : Representation k H V)
    (T : Fin N → G) (basis : Module.Basis (Fin d) k V)
    (hfactor : ∀ x : G, ∃ h : G, h∈H ∧ ∃ a : Fin N, x=h*T a)
    (comparable : Fin N → Fin N → Prop)
    (hunique : ∀ a b, T a*(T b)⁻¹∈H → a=b)
    (htriangular : CosetTriangular H T (· < ·) comparable)
    (τ : Representation k G U)
    (φ : τ.IntertwiningMap (Representation.coind H.subtype ρ))
    (v : U) (a b : Fin (N*d))
    (hleading : HasLeading ((coordinates H ρ T basis).comp φ.toLinearMap) v a)
    (hrelated : fullComparable comparable a b) :
    ∃ g : G, HasLeading ((coordinates H ρ T basis).comp φ.toLinearMap) (τ g v) b := by
  obtain ⟨⟨a,i⟩, rfl⟩ := finProdFinEquiv.surjective a
  obtain ⟨⟨b,j⟩, rfl⟩ := finProdFinEquiv.surjective b
  simp only [fullComparable, Equiv.symm_apply_apply] at hrelated
  obtain ⟨hij, hab⟩ := hrelated
  subst j
  refine ⟨raisingElement T a b, ?_⟩
  change HasLeading (coordinates H ρ T basis) (φ (τ (raisingElement T a b) v))
    (label b i)
  rw [Representation.IntertwiningMap.isIntertwining]
  exact raises_leading H ρ T basis hfactor comparable hunique htriangular hleading hab

end ThreeGroupHead

variable {k G V U : Type} [Field k] [Group G] [Finite G]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  [AddCommGroup U] [Module k U]

set_option maxHeartbeats 1000000 in
/-- Any representation injected equivariantly into the original coinduced
module satisfies the intrinsic-head width bound. Every datum in the
transversal and raising argument is constructed from the actual 3-group. -/
theorem threeGroup_coinduced_injective_coinvariant_head_le
    (hG : IsPGroup 3 G) (H : Subgroup G) (ρ : Representation k H V)
    (t : ℕ) (hindex : H.index=3^t) (τ : Representation k G U)
    (φ : τ.IntertwiningMap (Representation.coind H.subtype ρ))
    (hinjective : Function.Injective φ) :
    Module.finrank k τ.Coinvariants ≤ Module.finrank k V * ternaryLocalWidth t := by
  classical
  obtain ⟨D⟩ := pGroup_orderedCosetTransversal hG H t hindex
  let E := D.finRows
  let b := Module.finBasis k V
  let C : U →ₗ[k] (Fin (3^t * Module.finrank k V) → k) :=
    (coordinates H ρ E.repr b).comp φ.toLinearMap
  have hfactor : ∀ x : G, ∃ h : G, h∈H ∧ ∃ a : Fin (3^t), x=h*E.repr a :=
    fun x => E.factor x (Subgroup.mem_top x)
  have hC : Function.Injective C :=
    (coordinates_injective H ρ E.repr b hfactor).comp hinjective
  letI : FiniteDimensional k U := FiniteDimensional.of_injective C hC
  obtain ⟨leading, hseparated⟩ :=
    coinvariant_labels_of_raising τ C hC
      (fullComparable (primeCosetFinComparable 3 t))
      (ThreeGroupHead.intertwiner_raising H ρ E.repr b hfactor
        (primeCosetFinComparable 3 t) E.unique E.triangular τ φ)
  let fibre : Fin (Module.finrank k τ.Coinvariants) → Fin (Module.finrank k V) :=
    fun i => (finProdFinEquiv.symm (leading i)).2
  let point : Fin (Module.finrank k τ.Coinvariants) → Fin t → Fin 3 :=
    fun i => primeCosetFinPoint 3 t (finProdFinEquiv.symm (leading i)).1
  have hsep : ∀ i j, fibre i=fibre j → point i≤point j → i=j := by
    intro i j hf hp
    by_contra hij
    apply hseparated hij
    exact ⟨hf, (primeCosetFinComparable_iff_point_le 3 t _ _).mpr hp⟩
  simpa only [Fintype.card_fin] using
    ternaryGrid_fibre_antichain_card_le_width t fibre point hsep

/-- Invariant forms on the original domain of an actual injective
intertwiner are the dual of that domain's intrinsic coinvariants. -/
theorem threeGroup_coinduced_injective_head_le
    (hG : IsPGroup 3 G) (H : Subgroup G) (ρ : Representation k H V)
    (t : ℕ) (hindex : H.index=3^t) (τ : Representation k G U)
    (φ : τ.IntertwiningMap (Representation.coind H.subtype ρ))
    (hinjective : Function.Injective φ) :
    Module.finrank k (τ.IntertwiningMap (Representation.trivial k G k)) ≤
      Module.finrank k V * ternaryLocalWidth t := by
  letI : Fintype G := Fintype.ofFinite G
  letI : FiniteDimensional k U := FiniteDimensional.of_injective φ.toLinearMap hinjective
  rw [representationHead_finrank_eq_coinvariants]
  exact threeGroup_coinduced_injective_coinvariant_head_le hG H ρ t hindex τ φ hinjective

/-- Invariant forms on the original coinduced subrepresentation have the
same dimension as its intrinsic coinvariants. -/
theorem threeGroup_coinduced_subrepresentationHead_le
    (hG : IsPGroup 3 G) (H : Subgroup G) (ρ : Representation k H V)
    (t : ℕ) (hindex : H.index=3^t)
    (M : Subrepresentation (Representation.coind H.subtype ρ)) :
    Module.finrank k (M.toRepresentation.IntertwiningMap (Representation.trivial k G k)) ≤
      Module.finrank k V * ternaryLocalWidth t :=
  threeGroup_coinduced_injective_head_le (U := M.toSubmodule) hG H ρ t hindex
    M.toRepresentation (ThreeGroupHead.inclusion _ M) Subtype.val_injective

/-- The invariant head of every original induced subrepresentation. -/
theorem threeGroup_induced_subrepresentationHead_le
    (hG : IsPGroup 3 G) (H : Subgroup G) (ρ : Representation k H V)
    (t : ℕ) (hindex : H.index=3^t)
    (M : Subrepresentation (Representation.ind H.subtype ρ)) :
    Module.finrank k (M.toRepresentation.IntertwiningMap (Representation.trivial k G k)) ≤
      Module.finrank k V * ternaryLocalWidth t := by
  let e := inducedElementCoinducedEquiv H ρ
  exact threeGroup_coinduced_injective_head_le (U := M.toSubmodule) hG H ρ t hindex
    M.toRepresentation (e.toIntertwiningMap.comp (ThreeGroupHead.inclusion _ M))
    (e.toLinearEquiv.injective.comp Subtype.val_injective)

/-- Exact prime-character dimension on an abstract original domain;
specializing the domain later avoids nested-subtype quotient elaboration. -/
theorem threeGroup_coinduced_injective_characterHead_le
    {q : ℕ} [Fact q.Prime] {G₀ V₀ U₀ : Type} [Group G₀] [Finite G₀]
    [AddCommGroup V₀] [Module (ZMod q) V₀] [FiniteDimensional (ZMod q) V₀]
    [AddCommGroup U₀] [Module (ZMod q) U₀]
    (hG : IsPGroup 3 G₀) (H : Subgroup G₀) (ρ : Representation (ZMod q) H V₀)
    (t : ℕ) (hindex : H.index=3^t) (τ : Representation (ZMod q) G₀ U₀)
    (φ : τ.IntertwiningMap (Representation.coind H.subtype ρ))
    (hinjective : Function.Injective φ) :
    Module.finrank (ZMod q) (primeActionCharacters q (representationGroupAction τ)) ≤
      Module.finrank (ZMod q) V₀ * ternaryLocalWidth t := by
  letI : Fintype G₀ := Fintype.ofFinite G₀
  letI : FiniteDimensional (ZMod q) U₀ :=
    FiniteDimensional.of_injective φ.toLinearMap hinjective
  rw [representationCharacterHead_finrank_eq_coinvariants]
  exact threeGroup_coinduced_injective_coinvariant_head_le hG H ρ t hindex τ φ hinjective

/-- Prime-valued invariant characters of every exact original induced
subrepresentation, without a regular-subgroup or splitting hypothesis. -/
theorem threeGroup_induced_subrepresentationCharacterHead_le
    {q : ℕ} [Fact q.Prime] {G₀ V₀ : Type} [Group G₀] [Finite G₀]
    [AddCommGroup V₀] [Module (ZMod q) V₀] [FiniteDimensional (ZMod q) V₀]
    (hG : IsPGroup 3 G₀) (H : Subgroup G₀) (ρ : Representation (ZMod q) H V₀)
    (t : ℕ) (hindex : H.index=3^t)
    (M : Subrepresentation (Representation.ind H.subtype ρ)) :
    Module.finrank (ZMod q)
      (primeActionCharacters (A := G₀) (G := Multiplicative M.toSubmodule) q
        (representationGroupAction (p := q) (G := G₀) (V := M.toSubmodule)
          M.toRepresentation)) ≤
        Module.finrank (ZMod q) V₀ * ternaryLocalWidth t := by
  let e := inducedElementCoinducedEquiv H ρ
  exact threeGroup_coinduced_injective_characterHead_le (U₀ := M.toSubmodule) hG H ρ t hindex
    M.toRepresentation (e.toIntertwiningMap.comp (ThreeGroupHead.inclusion _ M))
    (e.toLinearEquiv.injective.comp Subtype.val_injective)

end SymmetricSubgroupAsymptotics
