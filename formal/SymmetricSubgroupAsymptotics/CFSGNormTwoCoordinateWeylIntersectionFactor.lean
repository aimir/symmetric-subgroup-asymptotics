import SymmetricSubgroupAsymptotics.CFSGFiniteDisjointSubgroupFactor
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNegativeRootContainment
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootSupportCardinality
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveCardinality
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootWeylAction
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOppositeIntersection

/-! Actual U factors uniquely into its intersections with the inverse
Weyl conjugates of U and U-. The proof counts independent literal root
parameters in the two subgroups and uses their proved disjointness.
No normality, special root order, or new collecting premise is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateWeylIntersectionFactor
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckPositivePGroup
open CFSGNormTwoCoordinateRootHeightQuotient CFSGNormTwoCoordinatePositiveRootGenerators
open CFSGNormTwoCoordinateRootSubgroup CFSGNormTwoCoordinateSelectedRootElement
open CFSGNormTwoCoordinateRootSupportCardinality CFSGNormTwoCoordinatePositiveCardinality
open CFSGNormTwoCoordinateRootWeylAction CFSGNormTwoCoordinateNegativeRootContainment
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckOppositeIntersection
open CFSGNormTwoCoordinateHeight CFSGIntegralNormTwoSigns
open CFSGSerreQuadraticWeylWord
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀ i, A i i = 2)
    (hs : A.transpose = A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀ i j, i ≠ j → A i j ≤ 0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀

def wordSignPart (K : Type) [Field K] (w : List (Fin r)) (neg : Bool) :
    Subgroup (PositiveGroup A hd hs hp ho K) :=
  (rootGroup A hs hp b₀ s₀ K neg).comap
    ((MulAut.conj (canonicalWord D K w)).toMonoidHom.comp
      (PositiveGroup A hd hs hp ho K).subtype)

theorem wordSignPart_inf (K : Type) [Field K] (w : List (Fin r)) :
    wordSignPart A hd hs hp ho K w false ⊓ wordSignPart A hd hs hp ho K w true = ⊥ := by
  apply le_antisymm _ bot_le
  intro u hu
  have hh : (MulAut.conj (canonicalWord D K w)) u.val ∈
      rootGroup A hs hp b₀ s₀ K false ⊓ rootGroup A hs hp b₀ s₀ K true := hu
  rw [positive_inf_negative A hs hp b₀ s₀ coordinateHeight
    (simple_height A hd hs hp ho) K, Subgroup.mem_bot] at hh
  apply Subgroup.mem_bot.mpr
  apply Subtype.ext
  apply (MulAut.conj (canonicalWord D K w)).injective
  change (MulAut.conj (canonicalWord D K w)) u.val =
    (MulAut.conj (canonicalWord D K w)) (1 : (Matrix ((b₀).support ⊕ Roots A)
      ((b₀).support ⊕ Roots A) K)ˣ)
  rw [map_one]
  exact hh

private theorem parameter_mem_part (K : Type) [Field K] (w : List (Fin r))
    (neg : Bool) (k : PositiveRoot A)
    (hk : rootSubgroup A hd hs hp ho K (wordRoot A hs hp b₀ s₀ w k.val) ≤
      rootGroup A hs hp b₀ s₀ K neg) (a : Multiplicative K) :
    positiveRootParameterHom A hd hs hp ho K k.val k.property a ∈
      wordSignPart A hd hs hp ho K w neg := by
  change (MulAut.conj (canonicalWord D K w))
    (selectedRootElement A hd hs hp ho K k.val a.toAdd) ∈ rootGroup A hs hp b₀ s₀ K neg
  apply hk
  rw [← rootSubgroup_map_word A hd hs hp ho K w k.val]
  exact ⟨selectedRootElement A hd hs hp ho K k.val a.toAdd,
    selectedRootElement_mem A hd hs hp ho K k.val a.toAdd, rfl⟩

theorem word_parts_product_bijective (K : Type) [Field K] [Finite K] (w : List (Fin r)) :
    Function.Bijective
      (fun z : wordSignPart A hd hs hp ho K w false × wordSignPart A hd hs hp ho K w true =>
        (z.1.val : PositiveGroup A hd hs hp ho K) * z.2.val) := by
  let P : PositiveRoot A → Prop := fun k => ∀ i, 0 ≤ (wordRoot A hs hp b₀ s₀ w k.val).val i
  let S : Finset (PositiveRoot A) := Finset.univ.filter P
  let T : Finset (PositiveRoot A) := Finset.univ.filter (fun k => ¬ P k)
  have hS : Nat.card K ^ S.card ≤ Nat.card (wordSignPart A hd hs hp ho K w false) := by
    apply root_support_card_le A hd hs hp ho K S
    intro k a
    have hk : P k.val := (Finset.mem_filter.mp k.property).2
    exact parameter_mem_part A hd hs hp ho K w false k.val
      (positive_root_subgroup_le A hd hs hp ho K _ hk) a
  have hT : Nat.card K ^ T.card ≤ Nat.card (wordSignPart A hd hs hp ho K w true) := by
    apply root_support_card_le A hd hs hp ho K T
    intro k a
    have hk : ¬ P k.val := (Finset.mem_filter.mp k.property).2
    have hneg : ∀ i, (wordRoot A hs hp b₀ s₀ w k.val.val).val i ≤ 0 := by
      exact (norm_two_coordinates_one_sign A hs hp (fun i => by rw [hd i]; exact even_two)
        ho _ (wordRoot A hs hp b₀ s₀ w k.val.val).property).resolve_left hk
    exact parameter_mem_part A hd hs hp ho K w true k.val
      (negative_root_subgroup_le A hd hs hp ho K _ hneg) a
  have hsum : S.card + T.card = Nat.card (PositiveRoot A) := by
    simpa only [S, T, Finset.card_univ, Nat.card_eq_fintype_card] using
      Finset.card_filter_add_card_filter_not (s := Finset.univ) P
  apply CFSGFiniteDisjointSubgroupFactor.product_bijective _ _ (wordSignPart_inf A hd hs hp ho K w)
  calc
    Nat.card (PositiveGroup A hd hs hp ho K) = Nat.card K ^ (S.card + T.card) := by
      rw [positive_card A hd hs hp ho K, hsum]
    _ = Nat.card K ^ S.card * Nat.card K ^ T.card := pow_add _ _ _
    _ ≤ _ := Nat.mul_le_mul hS hT

theorem exists_word_sign_factors (K : Type) [Field K] [Finite K]
    (w : List (Fin r)) (u : PositiveGroup A hd hs hp ho K) :
    ∃! z : wordSignPart A hd hs hp ho K w false × wordSignPart A hd hs hp ho K w true,
      (z.1.val : PositiveGroup A hd hs hp ho K) * z.2.val = u :=
  (word_parts_product_bijective A hd hs hp ho K w).existsUnique u

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateWeylIntersectionFactor
