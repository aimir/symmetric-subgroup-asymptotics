import SymmetricSubgroupAsymptotics.OriginalMinimalBlock
import Mathlib.Data.Finite.Card
import Mathlib.Data.Finset.Basic

/-! Degree induction on actual faithful transitive actions. The primitive
head and chosen-chief-weight bounds, and the scalar compatibility, remain
explicit inputs. The imprimitive step constructs its original block map
and recurses on the literal faithful top range with the original normal
image. A finite set of degrees can instead use an explicit bound for all
original actions at those degrees. No unrestricted all-action bound or
classification is an input. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

/-- The primitive relative-head input concerns each original normal
subgroup in its actual finite faithful primitive ambient action. -/
def PrimitiveTernaryHeadBound (f : ℕ → ℕ) : Prop :=
  ∀ (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [MulAction.IsPreprimitive G X] [Nontrivial X],
    ∀ (N : Subgroup G) [N.Normal],
      Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) ≤ f (Nat.card X)

/-- Primitive inputs are needed only outside the finite bypass set. -/
def PrimitiveTernaryHeadBoundOutside (f : ℕ → ℕ) (F : Finset ℕ) : Prop :=
  ∀ (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [MulAction.IsPreprimitive G X] [Nontrivial X],
    Nat.card X ∉ F → ∀ (N : Subgroup G) [N.Normal],
      Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) ≤ f (Nat.card X)

/-- Each bypass degree requires the bound for every original finite
faithful transitive action and every original normal subgroup. A finite
catalogue must be connected to this contract by actual action coverage. -/
def FiniteDegreeTernaryHeadBound (f : ℕ → ℕ) (F : Finset ℕ) : Prop :=
  ∀ (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [MulAction.IsPretransitive G X] [Nonempty X],
    Nat.card X ∈ F → ∀ (N : Subgroup G) [N.Normal],
      Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) ≤ f (Nat.card X)

/-- A chosen actual chief series suffices. The input does not identify
its ternary weight with the valuation of the group order. -/
def PrimitiveTernaryChiefWeightBound (g : ℕ → ℕ) : Prop :=
  ∀ (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [MulAction.IsPreprimitive G X] [Nontrivial X],
    ∃ c : ActualChiefSeries G, actualChiefSeriesTernaryWeight c ≤ g (Nat.card X)

/-- A faithful action on a subsingleton point set has a trivial ambient
group, so every original relative prime head is zero. -/
theorem primeRelativeHead_subsingleton_action (p : ℕ) [Fact p.Prime]
    {A Ω : Type} [Group A] [MulAction A Ω] [FaithfulSMul A Ω]
    [Subsingleton Ω] (N : Subgroup A) [N.Normal] :
    Module.finrank (ZMod p) (primeRelativeCharacters p N) = 0 := by
  letI : Subsingleton A := ⟨fun a b =>
    eq_of_smul_eq_smul (α := Ω) (fun _ => Subsingleton.elim _ _)⟩
  exact Module.finrank_zero_of_subsingleton

/-- Finite-degree bounds bypass both primitive classification and scalar
recurrence at those original degrees. Outside the bypass set, actual
minimal blocks and strictly smaller faithful top ranges prove the bound
by degree induction. Degree one outside the set is proved directly. -/
theorem transitiveTernaryHead_bound_with_finite_bypass
    (f g : ℕ → ℕ) (F : Finset ℕ)
    (hFinite : FiniteDegreeTernaryHeadBound f F)
    (hPrimitive : PrimitiveTernaryHeadBoundOutside f F)
    (hChief : PrimitiveTernaryChiefWeightBound g)
    (hScalar : ∀ r s : ℕ, 2 ≤ r → 2 ≤ s → r * s ∉ F →
      g r * ternaryIndexWidth s + f s ≤ f (r * s))
    {A Ω : Type} [Group A] [Finite A] [Finite Ω] [MulAction A Ω]
    [FaithfulSMul A Ω] [MulAction.IsPretransitive A Ω] [Nonempty Ω]
    (N : Subgroup A) [N.Normal] :
    Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) ≤ f (Nat.card Ω) := by
  classical
  have hind : ∀ n : ℕ,
      ∀ (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
        [FaithfulSMul G X] [MulAction.IsPretransitive G X] [Nonempty X],
        Nat.card X = n → ∀ (M : Subgroup G) [M.Normal],
          Module.finrank (ZMod 3) (primeRelativeCharacters 3 M) ≤ f n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro G X _ _ _ _ _ _ _ hcard M _
      by_cases hnF : n ∈ F
      · have hxF : Nat.card X ∈ F := by simpa only [hcard] using hnF
        simpa only [hcard] using hFinite G X hxF M
      have hxF : Nat.card X ∉ F := by simpa only [hcard] using hnF
      rcases subsingleton_or_nontrivial X with hsmall | hlarge
      · letI : Subsingleton X := hsmall
        rw [primeRelativeHead_subsingleton_action (Ω := X) 3 M]
        exact Nat.zero_le _
      · letI : Nontrivial X := hlarge
        by_cases hp : MulAction.IsPreprimitive G X
        · letI : MulAction.IsPreprimitive G X := hp
          simpa only [hcard] using hPrimitive G X hxF M
        · let x₀ : X := Classical.choice inferInstance
          let D : OriginalMinimalBlock (A := G) x₀ :=
            Classical.choice (originalMinimalBlock_nonempty x₀ hp)
          letI : MulAction.IsPreprimitive D.Component D.Fibre := D.component_preprimitive
          letI : Nontrivial D.Fibre :=
            Finite.one_lt_card_iff_nontrivial.mp D.degrees_ge_two.1
          letI : Finite D.Component :=
            Finite.of_surjective
              (originalBlockFibreAction D.map D.map_equivariant D.base).rangeRestrict
              (originalBlockFibreAction D.map D.map_equivariant D.base).rangeRestrict_surjective
          obtain ⟨c, hc⟩ := hChief D.Component D.Fibre
          letI : MulAction.IsPretransitive D.Top D.Points := D.top_pretransitive
          letI : FaithfulSMul D.Top D.Points := D.top_faithful
          letI : Finite D.Top := D.top_finite
          letI : Nonempty D.Points := ⟨D.base⟩
          have hs : Nat.card D.Points < n := by
            simpa only [hcard] using D.degrees_lt.2
          have ht := ih (Nat.card D.Points) hs D.Top D.Points rfl
            (originalNormalRange D.topMap M)
          calc
            Module.finrank (ZMod 3) (primeRelativeCharacters 3 M) ≤
                actualChiefSeriesTernaryWeight c * ternaryIndexWidth (Nat.card D.Points) +
                  Module.finrank (ZMod 3)
                    (primeRelativeCharacters 3 (originalNormalRange D.topMap M)) :=
              D.head_bound_nat M c
            _ ≤ g (Nat.card D.Fibre) * ternaryIndexWidth (Nat.card D.Points) +
                f (Nat.card D.Points) := add_le_add (Nat.mul_le_mul_right _ hc) ht
            _ ≤ f (Nat.card D.Fibre * Nat.card D.Points) :=
              hScalar _ _ D.degrees_ge_two.1 D.degrees_ge_two.2
                (by simpa only [D.degree_product, hcard] using hnF)
            _ = f n := congrArg f (D.degree_product.trans hcard)
  exact hind (Nat.card Ω) A Ω rfl N

/-- The universal scalar version is the empty-bypass specialization.
No condition on f(1) is needed. -/
theorem transitiveTernaryHead_bound_of_primitive
    (f g : ℕ → ℕ) (hPrimitive : PrimitiveTernaryHeadBound f)
    (hChief : PrimitiveTernaryChiefWeightBound g)
    (hScalar : ∀ r s : ℕ, 2 ≤ r → 2 ≤ s →
      g r * ternaryIndexWidth s + f s ≤ f (r * s))
    {A Ω : Type} [Group A] [Finite A] [Finite Ω] [MulAction A Ω]
    [FaithfulSMul A Ω] [MulAction.IsPretransitive A Ω] [Nonempty Ω]
    (N : Subgroup A) [N.Normal] :
    Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) ≤ f (Nat.card Ω) := by
  apply transitiveTernaryHead_bound_with_finite_bypass f g ∅ ?_ ?_ hChief ?_ N
  · intro G X _ _ _ _ _ _ _ hdegree
    exact False.elim (Finset.notMem_empty _ hdegree)
  · intro G X _ _ _ _ _ _ _ _ M _
    exact hPrimitive G X M
  · intro r s hr hs _
    exact hScalar r s hr hs

end SymmetricSubgroupAsymptotics
