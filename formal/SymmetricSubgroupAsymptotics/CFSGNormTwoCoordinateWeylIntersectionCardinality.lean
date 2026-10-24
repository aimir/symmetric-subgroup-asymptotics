import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateWeylIntersectionFactor

/-! Exact cardinality and root-support recognition of the actual two
Weyl sign intersections. The existing unique product factorization and
independent supported root parameters give both upper and lower bounds.
No normality or collecting order is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateWeylIntersectionCardinality
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckPositivePGroup
open CFSGNormTwoCoordinateRootHeightQuotient CFSGNormTwoCoordinatePositiveRootGenerators
open CFSGNormTwoCoordinateRootSubgroup CFSGNormTwoCoordinateSelectedRootElement
open CFSGNormTwoCoordinateRootSupportCardinality CFSGNormTwoCoordinatePositiveCardinality
open CFSGNormTwoCoordinateRootWeylAction CFSGNormTwoCoordinateNegativeRootContainment
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoCoordinateWeylIntersectionFactor
open CFSGSerreQuadraticWeylWord CFSGIntegralNormTwoSigns
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀

def signRoots (w : List (Fin r)) (neg : Bool) : Finset (PositiveRoot A) :=
  Finset.univ.filter (fun k=>if neg then ¬∀i,0≤(wordRoot A hs hp b₀ s₀ w k.val).val i
    else ∀i,0≤(wordRoot A hs hp b₀ s₀ w k.val).val i)

theorem parameter_mem_part (K : Type) [Field K] (w : List (Fin r)) (neg : Bool)
    (k : signRoots A hd hs hp ho w neg) (a : Multiplicative K) :
    positiveRootParameterHom A hd hs hp ho K k.val.val k.val.property a∈
      wordSignPart A hd hs hp ho K w neg := by
  have hr : rootSubgroup A hd hs hp ho K (wordRoot A hs hp b₀ s₀ w k.val.val)≤
      rootGroup A hs hp b₀ s₀ K neg := by
    cases neg with
    | false =>
      have hk : ∀i,0≤(wordRoot A hs hp b₀ s₀ w k.val.val).val i := by
        simpa only [signRoots,Bool.false_eq_true,if_false,Finset.mem_filter,
          Finset.mem_univ,true_and] using k.property
      exact positive_root_subgroup_le A hd hs hp ho K _ hk
    | true =>
      have hk : ¬∀i,0≤(wordRoot A hs hp b₀ s₀ w k.val.val).val i := by
        simpa only [signRoots,if_true,Finset.mem_filter,Finset.mem_univ,true_and] using k.property
      have hn := (norm_two_coordinates_one_sign A hs hp
        (fun i=>by rw [hd i];exact even_two) ho _
        (wordRoot A hs hp b₀ s₀ w k.val.val).property).resolve_left hk
      exact negative_root_subgroup_le A hd hs hp ho K _ hn
  change (MulAut.conj (canonicalWord D K w))
    (selectedRootElement A hd hs hp ho K k.val.val a.toAdd)∈rootGroup A hs hp b₀ s₀ K neg
  apply hr
  rw [←rootSubgroup_map_word A hd hs hp ho K w k.val.val]
  exact ⟨selectedRootElement A hd hs hp ho K k.val.val a.toAdd,
    selectedRootElement_mem A hd hs hp ho K k.val.val a.toAdd,rfl⟩

private theorem support_lower (K : Type) [Field K] [Finite K]
    (w : List (Fin r)) (neg : Bool) :
    Nat.card K^(signRoots A hd hs hp ho w neg).card≤
      Nat.card (wordSignPart A hd hs hp ho K w neg) :=
  root_support_card_le A hd hs hp ho K (signRoots A hd hs hp ho w neg)
    (wordSignPart A hd hs hp ho K w neg)
    (fun k a=>parameter_mem_part A hd hs hp ho K w neg k a)

theorem wordSignPart_card (K : Type) [Field K] [Finite K]
    (w : List (Fin r)) (neg : Bool) :
    Nat.card (wordSignPart A hd hs hp ho K w neg)=
      Nat.card K^(signRoots A hd hs hp ho w neg).card := by
  let S := signRoots A hd hs hp ho w false
  let T := signRoots A hd hs hp ho w true
  have hsum : S.card+T.card=Nat.card (PositiveRoot A) := by
    simpa only [S,T,signRoots,Bool.false_eq_true,if_false,if_true,
      Finset.card_univ,Nat.card_eq_fintype_card] using
      (Finset.card_filter_add_card_filter_not (s:=Finset.univ)
        (fun k : PositiveRoot A=>∀i,0≤(wordRoot A hs hp b₀ s₀ w k.val).val i))
  have he := Nat.card_congr (Equiv.ofBijective _
    (word_parts_product_bijective A hd hs hp ho K w))
  have hprod : Nat.card (wordSignPart A hd hs hp ho K w false)*
      Nat.card (wordSignPart A hd hs hp ho K w true)=Nat.card K^S.card*Nat.card K^T.card := by
    rw [Nat.card_prod,positive_card A hd hs hp ho K,←hsum,pow_add] at he
    exact he
  have hslo := support_lower A hd hs hp ho K w false
  have htlo := support_lower A hd hs hp ho K w true
  have hq : 0<Nat.card K := Nat.card_pos
  have hsupp : Nat.card (wordSignPart A hd hs hp ho K w false)≤Nat.card K^S.card := by
    apply le_of_mul_le_mul_right (a:=Nat.card K^T.card) ?_ (pow_pos hq _)
    exact (Nat.mul_le_mul_left _ htlo).trans (le_of_eq hprod)
  have htupp : Nat.card (wordSignPart A hd hs hp ho K w true)≤Nat.card K^T.card := by
    apply le_of_mul_le_mul_left (a:=Nat.card K^S.card) ?_ (pow_pos hq _)
    exact (Nat.mul_le_mul_right _ hslo).trans (le_of_eq hprod)
  cases neg with
  | false => exact le_antisymm hsupp hslo
  | true => exact le_antisymm htupp htlo

def signRootGroup (K : Type) [Field K] (w : List (Fin r)) (neg : Bool) :
    Subgroup (PositiveGroup A hd hs hp ho K) :=
  Subgroup.closure {u | ∃k : signRoots A hd hs hp ho w neg,∃a : Multiplicative K,
    positiveRootParameterHom A hd hs hp ho K k.val.val k.val.property a=u}

theorem signRootGroup_eq_part (K : Type) [Field K] [Finite K]
    (w : List (Fin r)) (neg : Bool) :
    signRootGroup A hd hs hp ho K w neg=wordSignPart A hd hs hp ho K w neg := by
  have hle : signRootGroup A hd hs hp ho K w neg≤wordSignPart A hd hs hp ho K w neg := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨k,a,rfl⟩
    exact parameter_mem_part A hd hs hp ho K w neg k a
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [wordSignPart_card A hd hs hp ho K w neg]
  apply root_support_card_le A hd hs hp ho K (signRoots A hd hs hp ho w neg)
  intro k a
  exact Subgroup.subset_closure ⟨k,a,rfl⟩

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateWeylIntersectionCardinality
