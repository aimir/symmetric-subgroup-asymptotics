import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow29StabilizerGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameLocalRowCatalogue
import SymmetricSubgroupAsymptotics.FiniteSurjectiveKernelTransport
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Selected eight-frame row 29: exact literal local catalogue

The literal point stabilizer has order `42`.  Its displayed two generators
generate the whole stabilizer.  The stored local map is the unique order-three
quotient up to target automorphism.  A separately checked cyclic-six quotient
has kernel of order seven; uniqueness of the Sylow-seven subgroup then rules
out every noncommutative quotient of order six.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical commutatorElement

namespace SymmetricSubgroupAsymptotics

/-- Any two order-seven subgroups of an order-forty-two group agree. -/
theorem subgroup_eq_of_card_seven_of_group_card_fortyTwo
    {H : Type*} [Group H] [Finite H]
    (K L : Subgroup H)
    (hH : Nat.card H = 42)
    (hK : Nat.card K = 7) (hL : Nat.card L = 7) : K = L := by
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hKp : IsPGroup 7 K := IsPGroup.of_card (by
    rw [hK]
    exact (pow_one 7).symm)
  have hLp : IsPGroup 7 L := IsPGroup.of_card (by
    rw [hL]
    exact (pow_one 7).symm)
  have hKindex : K.index = 6 := by
    have hcard := K.card_mul_index
    rw [hK, hH] at hcard
    omega
  have hLindex : L.index = 6 := by
    have hcard := L.card_mul_index
    rw [hL, hH] at hcard
    omega
  have hKnot : ¬ 7 ∣ K.index := by rw [hKindex]; norm_num
  have hLnot : ¬ 7 ∣ L.index := by rw [hLindex]; norm_num
  let PK : Sylow 7 H := hKp.toSylow hKnot
  let PL : Sylow 7 H := hLp.toSylow hLnot
  have hdiv : Nat.card (Sylow 7 H) ∣ 6 := by
    have hdiv₀ := Sylow.card_dvd_index PK
    change Nat.card (Sylow 7 H) ∣ K.index at hdiv₀
    rwa [hKindex] at hdiv₀
  have hpos : 0 < Nat.card (Sylow 7 H) := Nat.card_pos
  have hle : Nat.card (Sylow 7 H) ≤ 6 :=
    Nat.le_of_dvd (by norm_num) hdiv
  have hmod := card_sylow_modEq_one 7 H
  change Nat.card (Sylow 7 H) % 7 = 1 % 7 at hmod
  have hone : Nat.card (Sylow 7 H) = 1 := by omega
  letI : Subsingleton (Sylow 7 H) :=
    (Nat.card_eq_one_iff_unique.mp hone).1
  calc
    K = (PK : Subgroup H) := rfl
    _ = (PL : Subgroup H) := congrArg Sylow.toSubgroup (Subsingleton.elim PK PL)
    _ = L := rfl

namespace PrimitiveAffineEightFrameRow29LiteralLocalRow

open PrimitiveAffineEightFrameRow29InducedBinding
open PrimitiveAffineEightFrameRow29StabilizerGenerators

local instance sourceGroup : Group Source :=
  PrimitiveAffineEightFrameRow29TopCertificate.group

local instance inStabilizerDecidable (i : Fin 336) :
    Decidable (PrimitiveAffineEightFrameRow29InducedBinding.inStabilizer i) := by
  unfold PrimitiveAffineEightFrameRow29InducedBinding.inStabilizer
  infer_instance

local instance sourceStabilizerMembership (x : Source) :
    Decidable (x ∈ sourceStabilizer) := by
  change Decidable (PrimitiveAffineEightFrameRow29InducedBinding.inStabilizer x.index)
  infer_instance

abbrev LiteralAction : Subgroup (Equiv.Perm (Fin 8)) :=
  Subgroup.closure
    (Set.range PrimitiveAffineEightFrameRow29TopCertificate.generators)

private theorem inStabilizer_iff_fixes_zero : ∀ s : Source,
    PrimitiveAffineEightFrameRow29InducedBinding.inStabilizer s.index ↔
      ((((PrimitiveAffineEightFrameRow29TopCertificate.originalEquiv s :
        LiteralAction) : Equiv.Perm (Fin 8))) (0 : Fin 8) = 0) := by
  simp only [PrimitiveAffineEightFrameRow29TopCertificate.originalEquiv_apply]
  native_decide +revert

def sourceStabilizerEquivLiteral :
    sourceStabilizer ≃*
      MulAction.stabilizer LiteralAction (0 : Fin 8) where
  toFun s := ⟨PrimitiveAffineEightFrameRow29TopCertificate.originalEquiv s.1,
    (inStabilizer_iff_fixes_zero s.1).mp s.2⟩
  invFun t :=
    ⟨PrimitiveAffineEightFrameRow29TopCertificate.originalEquiv.symm t.1,
      (inStabilizer_iff_fixes_zero
        (PrimitiveAffineEightFrameRow29TopCertificate.originalEquiv.symm t.1)).mpr
        (by
          rw [PrimitiveAffineEightFrameRow29TopCertificate.originalEquiv.apply_symm_apply]
          exact t.2)⟩
  left_inv s := by
    apply Subtype.ext
    exact PrimitiveAffineEightFrameRow29TopCertificate.originalEquiv.symm_apply_apply s.1
  right_inv t := by
    apply Subtype.ext
    exact PrimitiveAffineEightFrameRow29TopCertificate.originalEquiv.apply_symm_apply t.1
  map_mul' s t := by
    apply Subtype.ext
    exact PrimitiveAffineEightFrameRow29TopCertificate.originalEquiv.map_mul s.1 t.1

def literalLocalMap :
    MulAction.stabilizer LiteralAction (0 : Fin 8) →*
      PrimitiveAffineEightFrameRow29InducedBinding.LocalTarget :=
  sourceLocalMap.comp sourceStabilizerEquivLiteral.symm.toMonoidHom

theorem literalLocalMap_surjective : Function.Surjective literalLocalMap :=
  sourceLocalMap_surjective.comp sourceStabilizerEquivLiteral.symm.surjective

noncomputable def literalLocalRow :
    Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightLiteralLocalRow
      LiteralAction where
  ModelLocalGroup := PrimitiveAffineEightFrameRow29InducedBinding.LocalTarget
  literalLocalMap := literalLocalMap
  literalLocalMap_surjective := literalLocalMap_surjective
  local_card := Or.inl PrimitiveAffineEightFrameRow29InducedBinding.localTarget_card

private abbrev C6 := Multiplicative (ZMod 6)

private def cyclicSixExponent (h : sourceStabilizer) : ZMod 6 :=
  match h.1.index.val with
  | 0 => 0
  | 2 => 1
  | 8 => 2
  | 18 => 0
  | 24 => 3
  | 29 => 0
  | 32 => 5
  | 45 => 1
  | 55 => 1
  | 59 => 4
  | 64 => 1
  | 67 => 0
  | 70 => 5
  | 72 => 1
  | 75 => 5
  | 103 => 2
  | 118 => 2
  | 122 => 2
  | 129 => 2
  | 131 => 1
  | 133 => 0
  | 134 => 2
  | 136 => 0
  | 137 => 5
  | 140 => 5
  | 142 => 4
  | 148 => 2
  | 150 => 5
  | 153 => 4
  | 155 => 4
  | 186 => 4
  | 198 => 3
  | 222 => 3
  | 226 => 3
  | 229 => 3
  | 233 => 1
  | 234 => 3
  | 236 => 5
  | 239 => 3
  | 240 => 0
  | 244 => 4
  | 255 => 4
  | _ => 0

private def cyclicSixMap : sourceStabilizer →* C6 where
  toFun h := Multiplicative.ofAdd (cyclicSixExponent h)
  map_one' := by native_decide
  map_mul' := by native_decide

private theorem cyclicSixMap_surjective : Function.Surjective cyclicSixMap := by
  native_decide

private theorem cyclicSixKernel_card : Nat.card cyclicSixMap.ker = 7 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  native_decide

private theorem commutator_le_cyclicSixKernel :
    commutator sourceStabilizer ≤ cyclicSixMap.ker :=
  Abelianization.commutator_subset_ker cyclicSixMap

private def a : sourceStabilizer := generators 0
private def b : sourceStabilizer := generators 1

private theorem b_sq : b ^ 2 = 1 := by native_decide
private theorem sourceLocalMap_a_ne_one : sourceLocalMap a ≠ 1 := by native_decide
private theorem sourceLocalMap_b : sourceLocalMap b = 1 := by native_decide

private theorem map_b_eq_one
    {L : Type*} [Group L] [Finite L]
    (f : sourceStabilizer →* L) (hL : Nat.card L = 3) : f b = 1 := by
  have htwo : (f b) ^ 2 = 1 := by
    rw [← map_pow, b_sq, map_one]
  have hthree : (f b) ^ 3 = 1 := by
    simpa only [hL] using (pow_card_eq_one' (G := L) (x := f b))
  have hstep : (f b) ^ 2 * f b = 1 := by
    simpa only [pow_succ] using hthree
  simpa only [htwo, one_mul] using hstep

private theorem map_a_ne_one_of_surjective
    {L : Type*} [Group L] [Finite L]
    (f : sourceStabilizer →* L) (hf : Function.Surjective f)
    (hL : Nat.card L = 3) : f a ≠ 1 := by
  haveI : Nontrivial L :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega : 1 < Nat.card L)
  intro ha
  have hb : f b = 1 := map_b_eq_one f hL
  have hfOne : f = 1 := by
    apply MonoidHom.eq_of_eqOn_dense generators_full
    rintro _ ⟨j, rfl⟩
    fin_cases j
    · exact ha
    · exact hb
  obtain ⟨z, hz⟩ := exists_ne (1 : L)
  obtain ⟨x, rfl⟩ := hf z
  exact hz (by rw [hfOne]; rfl)

/-- Every onto order-three map from the literal stabilizer is the recorded
map after a unique target relabelling on the displayed generator. -/
private noncomputable def sourceOrderThreeEquiv
    (L : Type) [Group L] [Finite L]
    (f : sourceStabilizer →* L) (hf : Function.Surjective f)
    (hL : Nat.card L = 3) :
    ∃ e : L ≃* LocalTarget, e.toMonoidHom.comp f = sourceLocalMap := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hfa : f a ≠ 1 := map_a_ne_one_of_surjective f hf hL
  have hsa : sourceLocalMap a ≠ 1 := sourceLocalMap_a_ne_one
  have hfgen : ∀ x : L, x ∈ Subgroup.zpowers (f a) := by
    intro x
    exact mem_zpowers_of_prime_card hL hfa
  have hsgen : ∀ x : LocalTarget, x ∈ Subgroup.zpowers (sourceLocalMap a) := by
    intro x
    exact mem_zpowers_of_prime_card localTarget_card hsa
  let eL : Multiplicative (ZMod 3) ≃* L :=
    zmodMulEquivOfGenerator hfgen hL
  let eS : Multiplicative (ZMod 3) ≃* LocalTarget :=
    zmodMulEquivOfGenerator hsgen localTarget_card
  let e : L ≃* LocalTarget := eL.symm.trans eS
  refine ⟨e, ?_⟩
  apply MonoidHom.eq_of_eqOn_dense generators_full
  rintro _ ⟨j, rfl⟩
  fin_cases j
  · change e (f a) = sourceLocalMap a
    simp [e, eL, eS]
  · change e (f b) = sourceLocalMap b
    rw [map_b_eq_one f hL, sourceLocalMap_b, map_one]

private theorem source_no_noncomm_order_six_quotient
    (L : Type) [Group L] [Finite L]
    (f : sourceStabilizer →* L) (hf : Function.Surjective f)
    (hL : Nat.card L = 6) (hnoncomm : ¬ IsMulCommutative L) : False := by
  have hfker : Nat.card f.ker = 7 := by
    have hcard := f.ker.card_mul_index
    rw [Subgroup.index_ker, f.range_eq_top_of_surjective hf,
      Nat.card_congr Subgroup.topEquiv.toEquiv, sourceStabilizer_card, hL] at hcard
    omega
  have hkernels : f.ker = cyclicSixMap.ker :=
    subgroup_eq_of_card_seven_of_group_card_fortyTwo
      f.ker cyclicSixMap.ker sourceStabilizer_card hfker cyclicSixKernel_card
  have hcomm : commutator sourceStabilizer ≤ f.ker := by
    rw [hkernels]
    exact commutator_le_cyclicSixKernel
  have hmul : ∀ x y : L, x * y = y * x := by
    intro x y
    obtain ⟨u, rfl⟩ := hf x
    obtain ⟨v, rfl⟩ := hf y
    rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement]
    exact MonoidHom.mem_ker.mp
      (hcomm (Subgroup.commutator_mem_commutator
        (Subgroup.mem_top u) (Subgroup.mem_top v)))
  exact hnoncomm ⟨⟨hmul⟩⟩

noncomputable def literalLocalCatalogue :
    Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightLiteralLocalRowCatalogue
      LiteralAction where
  Row := Unit
  row _ := literalLocalRow
  complete := by
    intro L _ _ f hf hcard
    let fs : sourceStabilizer →* L :=
      f.comp sourceStabilizerEquivLiteral.toMonoidHom
    have hfs : Function.Surjective fs :=
      hf.comp sourceStabilizerEquivLiteral.surjective
    rcases hcard with h3 | ⟨h6, hnoncomm⟩
    · obtain ⟨e, he⟩ := sourceOrderThreeEquiv L fs hfs h3
      refine ⟨(), e, ?_⟩
      ext x
      have hx := DFunLike.congr_fun he (sourceStabilizerEquivLiteral.symm x)
      simpa [fs, literalLocalMap] using hx
    · exact False.elim
        (source_no_noncomm_order_six_quotient L fs hfs h6 hnoncomm)

end PrimitiveAffineEightFrameRow29LiteralLocalRow
end SymmetricSubgroupAsymptotics

end
