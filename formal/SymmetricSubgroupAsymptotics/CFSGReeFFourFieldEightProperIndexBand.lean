import SymmetricSubgroupAsymptotics.CFSGReeFFourFieldEightPrimeIndex
import SymmetricSubgroupAsymptotics.CFSGReeFFourWeightedFixedOrderUpper
import SymmetricSubgroupAsymptotics.PrimitivePrimeCycleCardinalityBand
import SymmetricSubgroupAsymptotics.SmallIndexPrimitiveCosetAction
import SymmetricSubgroupAsymptotics.SimpleLeastIndexCompositionChart

/-! The selected actual period109 survives the original central quotient.
For each actual proper K of index below218, the existing109 index floor
makes K maximal. Its SAME faithful primitive coset action therefore pays
the prime-cycle tuple bound. We infer no whole-group order formula and
no prime11 exclusion. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourFieldEightProperIndexBand
open CFSGReeFFourFieldParameters CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourFixedAmbientHom CFSGReeFFourPerfectProjection
open CFSGReeFFourFixedBorelCardinality CFSGReeFFourFieldEightPrimePeriod
open CFSGReeFFourFieldEightFixedSelectedWord CFSGReeFFourFieldEightSelectedAction
open CFSGReeFFourFieldEightPrimeIndex

private instance fixedFinite : Finite (originalModelFixed 1) :=
  Finite.of_injective (fixedAmbientHom 1) (fixedAmbientHom_injective 1)
private instance originalFinite : Finite (CFSG.Models.ReeF4 1) :=
  Finite.of_surjective (fixedToOriginal 1 (by omega))
    (fixedToOriginal_surjective 1 (by omega))

/-- The selected period is used only through its already checked
return/nonreturn theorems and the actual prime-to109 quotient kernel. -/
theorem prime_oneOhNine_dvd_original_card :
    109 ∣ Nat.card (CFSG.Models.ReeF4 1) := by
  letI : MulAction (originalModelFixed 1) (Fin 26 → Field 1) :=
    MulAction.ofEndHom fixedVectorAction
  have hB : ¬109 ∣ Nat.card (fixedBorel 1) := by
    rw [fixedBorel_card]
    norm_num
  have hG : 109 ∣ Nat.card (originalModelFixed 1) := by
    apply PrimePeriodSimpleQuotientIndex.prime_dvd_card_of_point_period
      109 (by decide +kernel) selectedElement selectedVector
    · change fixedLinearAction (selectedElement^109) selectedVector = selectedVector
      exact selectedElement_period
    · change fixedLinearAction selectedElement selectedVector ≠ selectedVector
      exact selectedElement_moved
  exact PrimePeriodSimpleQuotientIndex.prime_dvd_card_quotient_of_kernel_le
    109 (by decide +kernel) (fixedToOriginal 1 (by omega))
    (fixedToOriginal_surjective 1 (by omega)) (fixedBorel 1)
    quotient_kernel_le_borel hB hG

/-- Every original proper-index value below218 is in fact below120. -/
theorem proper_index_lt_oneTwenty_of_lt_twoEighteen
    [IsSimpleGroup (CFSG.Models.ReeF4 1)]
    (K : Subgroup (CFSG.Models.ReeF4 1)) (hK : K ≠ ⊤)
    (hsmall : K.index < 218) : K.index < 120 := by
  classical
  letI : Fintype (CFSG.Models.ReeF4 1 ⧸ K) := Fintype.ofFinite _
  letI : MulAction.IsPreprimitive (CFSG.Models.ReeF4 1)
      (CFSG.Models.ReeF4 1 ⧸ K) :=
    SmallIndexPrimitiveCosetAction.coset_isPreprimitive_of_index_lt_twice
      109 (fun L hL => CFSGReeFFourFieldEightPrimeIndex.proper_index_le L hL)
      K hK (by omega)
  let f := MulAction.toPermHom (CFSG.Models.ReeF4 1) (CFSG.Models.ReeF4 1 ⧸ K)
  have hf : Function.Injective f :=
    PrimitiveSocleRawStructure.simple_cosetAction_injective K hK
  let P : Subgroup (Equiv.Perm (CFSG.Models.ReeF4 1 ⧸ K)) := f.range
  let q : CFSG.Models.ReeF4 1 →* P := f.rangeRestrict
  let points : (CFSG.Models.ReeF4 1 ⧸ K) →ₑ[q] (CFSG.Models.ReeF4 1 ⧸ K) :=
    { toFun := id, map_smul' := by intros; rfl }
  have hP : MulAction.IsPreprimitive P (CFSG.Models.ReeF4 1 ⧸ K) :=
    MulAction.IsPreprimitive.of_surjective (f:=points) Function.surjective_id
  have hq : Function.Bijective q :=
    ⟨fun _ _ h => hf (congrArg Subtype.val h), f.rangeRestrict_surjective⟩
  have hcard : Nat.card P = Nat.card (CFSG.Models.ReeF4 1) :=
    (Nat.card_congr (Equiv.ofBijective q hq)).symm
  have hp : 109 ∣ Nat.card P := by rw [hcard]; exact prime_oneOhNine_dvd_original_card
  letI : Fact (Nat.Prime 109) := ⟨by decide +kernel⟩
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G:=P) 109 hp
  have ha' : orderOf (a : Equiv.Perm (CFSG.Models.ReeF4 1 ⧸ K)) = 109 :=
    (orderOf_injective P.subtype Subtype.val_injective a).trans ha
  have hupper : Nat.card P ≤ 8^26 := by
    rw [hcard]
    exact CFSGReeFFourWeightedFixedOrderUpper.original_ree_order_le 1
  have hdegree := PrimitivePrimeCycleCardinalityBand.degree_lt_oneTwenty_of_order_oneOhNine
    P hP a.val a.property ha'
    (by simpa only [←K.index_eq_card] using hsmall) hupper
  simpa only [←K.index_eq_card] using hdegree

/-- This disjunction retains the SAME original K; no index is discarded. -/
theorem proper_index_short_band_or_large
    [IsSimpleGroup (CFSG.Models.ReeF4 1)]
    (K : Subgroup (CFSG.Models.ReeF4 1)) (hK : K ≠ ⊤) :
    (109 ≤ K.index ∧ K.index < 120) ∨ 218 ≤ K.index := by
  by_cases h : K.index < 218
  · exact Or.inl ⟨CFSGReeFFourFieldEightPrimeIndex.proper_index_le K hK,
      proper_index_lt_oneTwenty_of_lt_twoEighteen K hK h⟩
  · exact Or.inr (Nat.le_of_not_gt h)

end SymmetricSubgroupAsymptotics.CFSGReeFFourFieldEightProperIndexBand
