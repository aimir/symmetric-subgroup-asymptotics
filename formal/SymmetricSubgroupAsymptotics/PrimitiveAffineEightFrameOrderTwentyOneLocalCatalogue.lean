import Mathlib.GroupTheory.Sylow
import SymmetricSubgroupAsymptotics.FiniteSurjectiveKernelTransport
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameLocalRowCatalogue

/-!
# The order-twenty-one local dispatcher for an eight-frame row

The selected top-21 pilot has point stabilizer order `21` and its emitted
local row has target order `3`.  Every eligible structural local quotient
is therefore another quotient of order `3`.  Both kernels are the unique
normal Sylow-seven subgroup, so the first isomorphism theorem supplies the
exact target equivalence required by the kernel-checked row catalogue.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- Every order-seven subgroup of an order-twenty-one group is normal. -/
theorem subgroup_normal_of_card_seven_of_group_card_twentyOne
    {H : Type*} [Group H] [Finite H]
    (K : Subgroup H) (hH : Nat.card H = 21) (hK : Nat.card K = 7) :
    K.Normal := by
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hKp : IsPGroup 7 K := IsPGroup.of_card (by
    rw [hK]
    exact (pow_one 7).symm)
  have hKindex : K.index = 3 := by
    have hcard := K.card_mul_index
    rw [hK, hH] at hcard
    omega
  have hKnot : ¬ 7 ∣ K.index := by
    rw [hKindex]
    norm_num
  let PK : Sylow 7 H := hKp.toSylow hKnot
  have hdiv : Nat.card (Sylow 7 H) ∣ 3 := by
    have hdiv₀ := Sylow.card_dvd_index PK
    change Nat.card (Sylow 7 H) ∣ K.index at hdiv₀
    rwa [hKindex] at hdiv₀
  have hpos : 0 < Nat.card (Sylow 7 H) := Nat.card_pos
  have hle : Nat.card (Sylow 7 H) ≤ 3 :=
    Nat.le_of_dvd (by norm_num) hdiv
  have hmod := card_sylow_modEq_one 7 H
  change Nat.card (Sylow 7 H) % 7 = 1 % 7 at hmod
  have hone : Nat.card (Sylow 7 H) = 1 := by omega
  letI : Subsingleton (Sylow 7 H) :=
    (Nat.card_eq_one_iff_unique.mp hone).1
  change (PK : Subgroup H).Normal
  exact Sylow.normal_of_subsingleton PK

/-- A normal subgroup of order seven in a group of order twenty one is the
unique Sylow-seven subgroup.  Hence any two such normal subgroups agree. -/
theorem normalSubgroup_eq_of_card_seven_of_group_card_twentyOne
    {H : Type*} [Group H] [Finite H]
    (K L : Subgroup H) [K.Normal] [L.Normal]
    (hH : Nat.card H = 21)
    (hK : Nat.card K = 7) (hL : Nat.card L = 7) : K = L := by
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hKp : IsPGroup 7 K := IsPGroup.of_card (by
    rw [hK]
    exact (pow_one 7).symm)
  have hLp : IsPGroup 7 L := IsPGroup.of_card (by
    rw [hL]
    exact (pow_one 7).symm)
  have hKindex : K.index = 3 := by
    have hcard := K.card_mul_index
    rw [hK, hH] at hcard
    omega
  have hLindex : L.index = 3 := by
    have hcard := L.card_mul_index
    rw [hL, hH] at hcard
    omega
  have hKnot : ¬ 7 ∣ K.index := by
    rw [hKindex]
    norm_num
  have hLnot : ¬ 7 ∣ L.index := by
    rw [hLindex]
    norm_num
  let PK : Sylow 7 H := hKp.toSylow hKnot
  let PL : Sylow 7 H := hLp.toSylow hLnot
  letI : (PK : Subgroup H).Normal := by
    change K.Normal
    infer_instance
  letI : Unique (Sylow 7 H) := Sylow.unique_of_normal PK inferInstance
  calc
    K = (PK : Subgroup H) := rfl
    _ = (PL : Subgroup H) := congrArg Sylow.toSubgroup (Subsingleton.elim PK PL)
    _ = L := rfl

/-- The kernel of an onto order-three quotient of an order-twenty-one group
has order seven. -/
theorem surjectiveHom_kernel_card_seven_of_twentyOne_to_three
    {H L : Type*} [Group H] [Finite H] [Group L] [Finite L]
    (f : H →* L) (hf : Function.Surjective f)
    (hH : Nat.card H = 21) (hL : Nat.card L = 3) :
    Nat.card f.ker = 7 := by
  have hcard := f.ker.card_mul_index
  rw [Subgroup.index_ker, f.range_eq_top_of_surjective hf,
    Nat.card_congr Subgroup.topEquiv.toEquiv, hH, hL] at hcard
  omega

namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeEightLiteralLocalRowCatalogue

/-- A transitive group of order `168` on eight points has point stabilizer
of order `21`. -/
theorem stabilizer_card_twentyOne_of_card_oneSixtyEight
    (T : Subgroup (Equiv.Perm (Fin 8)))
    [MulAction.IsPretransitive T (Fin 8)]
    (hT : Nat.card T = 168) :
    Nat.card (MulAction.stabilizer T (0 : Fin 8)) = 21 := by
  have hindex : (MulAction.stabilizer T (0 : Fin 8)).index = 8 := by
    simpa only [Nat.card_fin] using
      MulAction.index_stabilizer_of_transitive T (0 : Fin 8)
  have hcard := (MulAction.stabilizer T (0 : Fin 8)).card_mul_index
  rw [hindex, hT] at hcard
  omega

/-- For the selected order-168 top the emitted local row is determined by
the literal normal order-seven kernel.  No executable target group or local
image table is required: the canonical quotient is the checked target. -/
noncomputable def localRowOfOrderSevenKernel
    (T : Subgroup (Equiv.Perm (Fin 8)))
    [MulAction.IsPretransitive T (Fin 8)]
    (N : Subgroup (MulAction.stabilizer T (0 : Fin 8)))
    (hT : Nat.card T = 168)
    (hN : Nat.card N = 7) :
    DegreeEightLiteralLocalRow T := by
  have hsource := stabilizer_card_twentyOne_of_card_oneSixtyEight T hT
  letI : N.Normal :=
    subgroup_normal_of_card_seven_of_group_card_twentyOne N hsource hN
  exact DegreeEightLiteralLocalRow.ofOrderSevenKernelInOrderTwentyOne T N
    hsource hN

/-- An order-`168` transitive top supplies its order-three local row without
any generated local target or kernel data.  Choose a Sylow-seven subgroup
of the order-`21` point stabilizer.  Its order and normality follow from the
two group orders, and its canonical quotient has order three.

This is useful for the selected row-28 importer: the finite certificate has
to bind the literal top and the induced module, but no second Cayley table
or handwritten stabilizer-kernel comparison survives at the Lean boundary. -/
noncomputable def canonicalLocalRowOfOrderOneSixtyEight
    (T : Subgroup (Equiv.Perm (Fin 8)))
    [MulAction.IsPretransitive T (Fin 8)]
    (hT : Nat.card T = 168) :
    {R : DegreeEightLiteralLocalRow T //
      Nat.card R.ModelLocalGroup = 3} := by
  let H := MulAction.stabilizer T (0 : Fin 8)
  have hH : Nat.card H = 21 :=
    stabilizer_card_twentyOne_of_card_oneSixtyEight T hT
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let K : Sylow 7 H := default
  have hK : Nat.card K = 7 := by
    rw [Sylow.card_eq_multiplicity, hH]
    have hf : Nat.factorization 21 7 = 1 := by
      native_decide
    rw [hf]
    norm_num
  letI : (K : Subgroup H).Normal :=
    subgroup_normal_of_card_seven_of_group_card_twentyOne K hH hK
  have hquotient : Nat.card (H ⧸ (K : Subgroup H)) = 3 := by
    have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (K : Subgroup H)
    rw [hH, hK] at hmul
    omega
  let R := DegreeEightLiteralLocalRow.ofNormalKernel T (K : Subgroup H)
    (Or.inl hquotient)
  exact ⟨R, hquotient⟩

/-- The singleton local catalogue used by the selected top-21 row.  The
source-card and stored-target-card equalities are finite certificate facts;
all quotient comparison after those facts is proved here generically. -/
noncomputable def singletonOfOrderTwentyOne
    (T : Subgroup (Equiv.Perm (Fin 8)))
    (R : DegreeEightLiteralLocalRow T)
    (hsource : Nat.card (MulAction.stabilizer T (0 : Fin 8)) = 21)
    (htarget : Nat.card R.ModelLocalGroup = 3) :
    DegreeEightLiteralLocalRowCatalogue T where
  Row := Unit
  row _ := R
  complete := by
    intro L _ _ f hf hcard
    have hL : Nat.card L = 3 := by
      rcases hcard with h3 | h6
      · exact h3
      · exfalso
        have hdvd : Nat.card L ∣
            Nat.card (MulAction.stabilizer T (0 : Fin 8)) :=
          Subgroup.card_dvd_of_surjective f hf
        rw [h6, hsource] at hdvd
        norm_num at hdvd
    have hfker : Nat.card f.ker = 7 :=
      surjectiveHom_kernel_card_seven_of_twentyOne_to_three
        f hf hsource hL
    have hRker : Nat.card R.literalLocalMap.ker = 7 :=
      surjectiveHom_kernel_card_seven_of_twentyOne_to_three
        R.literalLocalMap R.literalLocalMap_surjective hsource htarget
    have hkernels : f.ker = R.literalLocalMap.ker :=
      normalSubgroup_eq_of_card_seven_of_group_card_twentyOne
        f.ker R.literalLocalMap.ker hsource hfker hRker
    refine ⟨(), surjectiveTargetEquivOfKernelEq f R.literalLocalMap
      hf R.literalLocalMap_surjective hkernels, ?_⟩
    exact surjectiveTargetEquivOfKernelEq_comp f R.literalLocalMap
      hf R.literalLocalMap_surjective hkernels

/-- Version of the singleton constructor in the form supplied by the
selected top certificate: transitivity and total order `168`. -/
noncomputable def singletonOfOrderOneSixtyEight
    (T : Subgroup (Equiv.Perm (Fin 8)))
    [MulAction.IsPretransitive T (Fin 8)]
    (R : DegreeEightLiteralLocalRow T)
    (hsource : Nat.card T = 168)
    (htarget : Nat.card R.ModelLocalGroup = 3) :
    DegreeEightLiteralLocalRowCatalogue T :=
  singletonOfOrderTwentyOne T R
    (stabilizer_card_twentyOne_of_card_oneSixtyEight T hsource) htarget

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

/-- Select the exact stored local row after the actual top has matched the
order-168 literal model.  The point-stabilizer order and kernel equality are
derived, rather than accepted from the catalogue tag. -/
noncomputable def selectActualOrderOneSixtyEight
    {ModelGroup : Type} [Group ModelGroup] [Finite ModelGroup]
    (topMatch : DegreeFourZeroCoreEightLiteralTopMatch
      block ModelGroup)
    (R : DegreeEightLiteralLocalRow topMatch.literalAction)
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥)
    (hmodel : Nat.card ModelGroup = 168)
    (htarget : Nat.card R.ModelLocalGroup = 3) :
    DegreeFourZeroCoreEightPointedLocalMatch
      block P topMatch hr hD (0 : Fin 8) := by
  letI : MulAction.IsPretransitive topMatch.literalAction (Fin 8) :=
    DegreeFourZeroCoreEightLiteralTopMatch.literalAction_pretransitive
      (block := block) topMatch
  have hliteral : Nat.card topMatch.literalAction = 168 := by
    rw [Nat.card_congr topMatch.actionModelEquiv.toEquiv]
    exact hmodel
  let C := singletonOfOrderOneSixtyEight topMatch.literalAction R
    hliteral htarget
  exact (selectActual block P topMatch C hr hD).2

/-- The canonical Sylow-seven row gives the pointed local comparison for an
order-`168` literal top.  This removes the local-row fields from the selected
finite-frame certificate altogether. -/
noncomputable def selectActualCanonicalOrderOneSixtyEight
    {ModelGroup : Type} [Group ModelGroup] [Finite ModelGroup]
    (topMatch : DegreeFourZeroCoreEightLiteralTopMatch
      block ModelGroup)
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥)
    (hmodel : Nat.card ModelGroup = 168) :
    DegreeFourZeroCoreEightPointedLocalMatch
      block P topMatch hr hD (0 : Fin 8) := by
  letI : MulAction.IsPretransitive topMatch.literalAction (Fin 8) :=
    DegreeFourZeroCoreEightLiteralTopMatch.literalAction_pretransitive
      (block := block) topMatch
  have hliteral : Nat.card topMatch.literalAction = 168 := by
    rw [Nat.card_congr topMatch.actionModelEquiv.toEquiv]
    exact hmodel
  obtain ⟨R, hR⟩ := canonicalLocalRowOfOrderOneSixtyEight
    topMatch.literalAction hliteral
  exact selectActualOrderOneSixtyEight block P topMatch R hr hD hmodel hR

end DegreeEightLiteralLocalRowCatalogue
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
