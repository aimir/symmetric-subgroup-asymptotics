import Mathlib.GroupTheory.SpecificGroups.Cyclic
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow4InducedBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow5InducedBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow6InducedBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow7InducedBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameLocalRowCatalogue
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameOrderSixLocalCatalogue

/-!
# The four local rows above the common order-288 eight-point top

Rows 4--7 of the eight-frame certificate have the same literal top.  Its
point stabilizer has order 36 and has four quotients of order three.  This
file puts the four emitted quotient maps on one literal stabilizer and proves
that they exhaust every eligible local quotient.  Thus the four finite rows
are selected by the actual local map rather than by an external row label.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace PrimitiveAffineEightFrameRows4To7LocalCatalogue

namespace R4
open PrimitiveAffineEightFrameRow4InducedBinding

local instance sourceGroup : Group Source :=
  PrimitiveAffineEightFrameRow4TopCertificate.group

local instance inStabilizerDecidable (i : Fin 288) :
    Decidable (inStabilizer i) := by
  unfold inStabilizer
  infer_instance

local instance sourceStabilizerMembership (s : Source) :
    Decidable (s ∈ sourceStabilizer) :=
  inStabilizerDecidable s.index

/-- The common literal order-288 top. -/
abbrev LiteralAction : Subgroup (Equiv.Perm (Fin 8)) :=
  Subgroup.closure
    (Set.range PrimitiveAffineEightFrameRow4TopCertificate.generators)

private theorem inStabilizer_iff_fixes_zero : ∀ s : Source,
    inStabilizer s.index ↔
      ((((PrimitiveAffineEightFrameRow4TopCertificate.originalEquiv s :
        LiteralAction) : Equiv.Perm (Fin 8))) (0 : Fin 8) = 0) := by
  simp only [PrimitiveAffineEightFrameRow4TopCertificate.originalEquiv_apply]
  native_decide +revert

/-- The emitted Cayley stabilizer is exactly the stabilizer of zero in the
common literal top. -/
def sourceStabilizerEquivLiteral :
    sourceStabilizer ≃*
      MulAction.stabilizer LiteralAction (0 : Fin 8) where
  toFun s := ⟨PrimitiveAffineEightFrameRow4TopCertificate.originalEquiv s.1,
    (inStabilizer_iff_fixes_zero s.1).mp s.2⟩
  invFun t :=
    ⟨PrimitiveAffineEightFrameRow4TopCertificate.originalEquiv.symm t.1,
      (inStabilizer_iff_fixes_zero
        (PrimitiveAffineEightFrameRow4TopCertificate.originalEquiv.symm t.1)).mpr
        (by
          rw [PrimitiveAffineEightFrameRow4TopCertificate.originalEquiv.apply_symm_apply]
          exact t.2)⟩
  left_inv s := by
    apply Subtype.ext
    exact PrimitiveAffineEightFrameRow4TopCertificate.originalEquiv.symm_apply_apply s.1
  right_inv t := by
    apply Subtype.ext
    exact PrimitiveAffineEightFrameRow4TopCertificate.originalEquiv.apply_symm_apply t.1
  map_mul' s t := by
    apply Subtype.ext
    exact PrimitiveAffineEightFrameRow4TopCertificate.originalEquiv.map_mul s.1 t.1

end R4

abbrev LiteralAction := R4.LiteralAction
abbrev LiteralStabilizer := MulAction.stabilizer LiteralAction (0 : Fin 8)

/-- Public name for the common source-to-literal stabilizer equivalence. -/
abbrev sourceStabilizerEquivLiteral := R4.sourceStabilizerEquivLiteral

local instance row4SourceGroup : Group
    PrimitiveAffineEightFrameRow4InducedBinding.Source :=
  PrimitiveAffineEightFrameRow4TopCertificate.group

/-- The four Schreier emitters use the same Cayley table and the same
stabilizer predicate.  These identity equivalences expose that fact without
identifying any of their four quotient maps. -/
def sourceStabilizerEquivRow5 :
    PrimitiveAffineEightFrameRow4InducedBinding.sourceStabilizer ≃*
      PrimitiveAffineEightFrameRow5InducedBinding.sourceStabilizer where
  toFun x := ⟨x.1, by simpa [PrimitiveAffineEightFrameRow4InducedBinding.inStabilizer,
    PrimitiveAffineEightFrameRow5InducedBinding.inStabilizer] using x.2⟩
  invFun x := ⟨x.1, by simpa [PrimitiveAffineEightFrameRow4InducedBinding.inStabilizer,
    PrimitiveAffineEightFrameRow5InducedBinding.inStabilizer] using x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

def sourceStabilizerEquivRow6 :
    PrimitiveAffineEightFrameRow4InducedBinding.sourceStabilizer ≃*
      PrimitiveAffineEightFrameRow6InducedBinding.sourceStabilizer where
  toFun x := ⟨x.1, by simpa [PrimitiveAffineEightFrameRow4InducedBinding.inStabilizer,
    PrimitiveAffineEightFrameRow6InducedBinding.inStabilizer] using x.2⟩
  invFun x := ⟨x.1, by simpa [PrimitiveAffineEightFrameRow4InducedBinding.inStabilizer,
    PrimitiveAffineEightFrameRow6InducedBinding.inStabilizer] using x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

def sourceStabilizerEquivRow7 :
    PrimitiveAffineEightFrameRow4InducedBinding.sourceStabilizer ≃*
      PrimitiveAffineEightFrameRow7InducedBinding.sourceStabilizer where
  toFun x := ⟨x.1, by simpa [PrimitiveAffineEightFrameRow4InducedBinding.inStabilizer,
    PrimitiveAffineEightFrameRow7InducedBinding.inStabilizer] using x.2⟩
  invFun x := ⟨x.1, by simpa [PrimitiveAffineEightFrameRow4InducedBinding.inStabilizer,
    PrimitiveAffineEightFrameRow7InducedBinding.inStabilizer] using x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

def sourceMap4 :
    PrimitiveAffineEightFrameRow4InducedBinding.sourceStabilizer →*
      PrimitiveAffineEightFrameRow4InducedBinding.LocalTarget :=
  PrimitiveAffineEightFrameRow4InducedBinding.sourceLocalMap

def sourceMap5 :
    PrimitiveAffineEightFrameRow4InducedBinding.sourceStabilizer →*
      PrimitiveAffineEightFrameRow5InducedBinding.LocalTarget :=
  PrimitiveAffineEightFrameRow5InducedBinding.sourceLocalMap.comp
    sourceStabilizerEquivRow5.toMonoidHom

def sourceMap6 :
    PrimitiveAffineEightFrameRow4InducedBinding.sourceStabilizer →*
      PrimitiveAffineEightFrameRow6InducedBinding.LocalTarget :=
  PrimitiveAffineEightFrameRow6InducedBinding.sourceLocalMap.comp
    sourceStabilizerEquivRow6.toMonoidHom

def sourceMap7 :
    PrimitiveAffineEightFrameRow4InducedBinding.sourceStabilizer →*
      PrimitiveAffineEightFrameRow7InducedBinding.LocalTarget :=
  PrimitiveAffineEightFrameRow7InducedBinding.sourceLocalMap.comp
    sourceStabilizerEquivRow7.toMonoidHom

def literalMap4 : LiteralStabilizer →*
    PrimitiveAffineEightFrameRow4InducedBinding.LocalTarget :=
  sourceMap4.comp R4.sourceStabilizerEquivLiteral.symm.toMonoidHom

def literalMap5 : LiteralStabilizer →*
    PrimitiveAffineEightFrameRow5InducedBinding.LocalTarget :=
  sourceMap5.comp R4.sourceStabilizerEquivLiteral.symm.toMonoidHom

def literalMap6 : LiteralStabilizer →*
    PrimitiveAffineEightFrameRow6InducedBinding.LocalTarget :=
  sourceMap6.comp R4.sourceStabilizerEquivLiteral.symm.toMonoidHom

def literalMap7 : LiteralStabilizer →*
    PrimitiveAffineEightFrameRow7InducedBinding.LocalTarget :=
  sourceMap7.comp R4.sourceStabilizerEquivLiteral.symm.toMonoidHom

theorem literalMap4_surjective : Function.Surjective literalMap4 :=
  PrimitiveAffineEightFrameRow4InducedBinding.sourceLocalMap_surjective.comp
    R4.sourceStabilizerEquivLiteral.symm.surjective

theorem literalMap5_surjective : Function.Surjective literalMap5 :=
  PrimitiveAffineEightFrameRow5InducedBinding.sourceLocalMap_surjective.comp
    (sourceStabilizerEquivRow5.surjective.comp
      R4.sourceStabilizerEquivLiteral.symm.surjective)

theorem literalMap6_surjective : Function.Surjective literalMap6 :=
  PrimitiveAffineEightFrameRow6InducedBinding.sourceLocalMap_surjective.comp
    (sourceStabilizerEquivRow6.surjective.comp
      R4.sourceStabilizerEquivLiteral.symm.surjective)

theorem literalMap7_surjective : Function.Surjective literalMap7 :=
  PrimitiveAffineEightFrameRow7InducedBinding.sourceLocalMap_surjective.comp
    (sourceStabilizerEquivRow7.surjective.comp
      R4.sourceStabilizerEquivLiteral.symm.surjective)

noncomputable def row4 : DegreeEightLiteralLocalRow LiteralAction where
  ModelLocalGroup := PrimitiveAffineEightFrameRow4InducedBinding.LocalTarget
  literalLocalMap := literalMap4
  literalLocalMap_surjective := literalMap4_surjective
  local_card := Or.inl PrimitiveAffineEightFrameRow4InducedBinding.localTarget_card

noncomputable def row5 : DegreeEightLiteralLocalRow LiteralAction where
  ModelLocalGroup := PrimitiveAffineEightFrameRow5InducedBinding.LocalTarget
  literalLocalMap := literalMap5
  literalLocalMap_surjective := literalMap5_surjective
  local_card := Or.inl PrimitiveAffineEightFrameRow5InducedBinding.localTarget_card

noncomputable def row6 : DegreeEightLiteralLocalRow LiteralAction where
  ModelLocalGroup := PrimitiveAffineEightFrameRow6InducedBinding.LocalTarget
  literalLocalMap := literalMap6
  literalLocalMap_surjective := literalMap6_surjective
  local_card := Or.inl PrimitiveAffineEightFrameRow6InducedBinding.localTarget_card

noncomputable def row7 : DegreeEightLiteralLocalRow LiteralAction where
  ModelLocalGroup := PrimitiveAffineEightFrameRow7InducedBinding.LocalTarget
  literalLocalMap := literalMap7
  literalLocalMap_surjective := literalMap7_surjective
  local_card := Or.inl PrimitiveAffineEightFrameRow7InducedBinding.localTarget_card

abbrev SourceStabilizer :=
  PrimitiveAffineEightFrameRow4InducedBinding.sourceStabilizer

local instance sourceStabilizerMembership
    (x : PrimitiveAffineEightFrameRow4InducedBinding.Source) :
    Decidable (x ∈ SourceStabilizer) := by
  change Decidable
    (PrimitiveAffineEightFrameRow4InducedBinding.inStabilizer x.index)
  unfold PrimitiveAffineEightFrameRow4InducedBinding.inStabilizer
  infer_instance

local instance sourceStabilizerFintype : Fintype SourceStabilizer := by
  infer_instance

/-- The four displayed generators of the common point stabilizer.  They are
the first four top generators; the last three move point zero. -/
def stabilizerGenerator (j : Fin 4) : SourceStabilizer :=
  ⟨PrimitiveAffineEightFrameRow4TopCertificate.ambient (Fin.castAdd 3 j),
    by fin_cases j <;> native_decide +revert⟩

private def stabilizerWords : Array (List (Fin 4)) := #[
    [],[0],[1],[2],[3],[],[],[],[0,0],[0,1],[0,2],[0,3],
    [],[],[],[1,2],[1,3],[],[],[],[2,0],[2,3],[],[],
    [],[3,3],[],[],[],[],[],[],[],[0,0,1],[0,0,2],[0,0,3],
    [],[],[],[0,1,3],[],[],[],[0,2,0],[0,2,3],[],[],[],
    [0,3,3],[],[],[],[],[],[],[],[1,2,3],[],[],[],
    [1,3,3],[],[],[],[],[],[],[],[2,0,3],[],[],[],
    [2,3,3],[],[],[],[],[],[],[],[],[],[],[],
    [],[],[],[],[0,0,1,3],[],[],[],[0,0,2,3],[],[],[],
    [0,0,3,3],[],[],[],[],[],[],[],[0,1,3,3],[],[],[],
    [],[],[],[],[0,2,0,3],[],[],[],[0,2,3,3],[],[],[],
    [],[],[],[],[],[],[],[],[],[],[],[],
    [1,2,3,3],[],[],[],[],[],[],[],[],[],[],[],
    [],[],[],[],[2,0,3,3],[],[],[],[],[],[],[],
    [],[],[],[],[],[],[],[],[],[],[],[0,0,1,3,3],
    [],[],[],[],[],[],[],[0,0,2,3,3],[],[],[],[],
    [],[],[],[],[],[],[],[],[],[],[],[],
    [],[],[],[],[],[],[],[0,2,0,3,3],[],[],[],[],
    [],[],[],[],[],[],[],[],[],[],[],[],
    [],[],[],[],[],[],[],[],[],[],[],[],
    [],[],[],[],[],[],[],[],[],[],[],[],
    [],[],[],[],[],[],[],[],[],[],[],[],
    [],[],[],[],[],[],[],[],[],[],[],[],
    [],[],[],[],[],[],[],[],[],[],[],[],
    [],[],[],[],[],[],[],[],[],[],[],[]
  ]

private def stabilizerWord (x : SourceStabilizer) : List (Fin 4) :=
  stabilizerWords[x.1.index.val]!

private theorem stabilizerWord_prod (x : SourceStabilizer) :
    ((stabilizerWord x).map stabilizerGenerator).prod = x := by
  native_decide +revert

/-- Equality of homomorphisms out of the common stabilizer is checked on the
four literal stabilizer generators. -/
theorem hom_ext_stabilizerGenerator
    {M : Type*} [Group M] (f g : SourceStabilizer →* M)
    (h : ∀ j, f (stabilizerGenerator j) = g (stabilizerGenerator j)) :
    f = g := by
  ext x
  rw [← stabilizerWord_prod x]
  induction stabilizerWord x with
  | nil => simp
  | cons j js ih => simp [h j, ih]

private theorem stabilizerGenerator_one_sq :
    stabilizerGenerator (1 : Fin 4) ^ 2 = 1 := by native_decide

private theorem stabilizerGenerator_two_sq :
    stabilizerGenerator (2 : Fin 4) ^ 2 = 1 := by native_decide

private theorem order_two_image_eq_one_of_card_three
    {L : Type*} [Group L] [Finite L]
    (hL : Nat.card L = 3) {x : L} (hx : x ^ 2 = 1) : x = 1 := by
  have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx
  have h3 : orderOf x ∣ 3 := by
    simpa only [hL] using orderOf_dvd_natCard x
  have h1 : orderOf x = 1 := by
    have hd : orderOf x ∣ Nat.gcd 2 3 := Nat.dvd_gcd h2 h3
    have hgcd : Nat.gcd 2 3 = 1 := by decide
    rw [hgcd] at hd
    exact Nat.dvd_one.mp hd
  exact orderOf_eq_one_iff.mp h1

private theorem map_generator_one_eq_one
    {L : Type*} [Group L] [Finite L]
    (f : SourceStabilizer →* L) (hL : Nat.card L = 3) :
    f (stabilizerGenerator (1 : Fin 4)) = 1 := by
  apply order_two_image_eq_one_of_card_three hL
  rw [← map_pow, stabilizerGenerator_one_sq, map_one]

private theorem map_generator_two_eq_one
    {L : Type*} [Group L] [Finite L]
    (f : SourceStabilizer →* L) (hL : Nat.card L = 3) :
    f (stabilizerGenerator (2 : Fin 4)) = 1 := by
  apply order_two_image_eq_one_of_card_three hL
  rw [← map_pow, stabilizerGenerator_two_sq, map_one]

/-- Every element of a three-element group is `1`, a chosen nonidentity
element, or its inverse. -/
private theorem eq_one_or_eq_or_eq_inv_of_card_three
    {L : Type*} [Group L] [Finite L]
    (hL : Nat.card L = 3) {a : L} (ha : a ≠ 1) (b : L) :
    b = 1 ∨ b = a ∨ b = a⁻¹ := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let e : Multiplicative (ZMod 3) ≃* L :=
    zmodMulEquivOfGenerator
      (fun x ↦ (zpowers_eq_top_of_prime_card hL ha).ge (Subgroup.mem_top x)) hL
  have hx : ∀ x : Multiplicative (ZMod 3),
      x = 1 ∨ x = Multiplicative.ofAdd 1 ∨
        x = (Multiplicative.ofAdd 1)⁻¹ := by
    rintro ⟨x⟩
    interval_cases x
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (by rfl))
  rcases hx (e.symm b) with h | h | h
  · left
    calc
      b = e (e.symm b) := (e.apply_symm_apply b).symm
      _ = e 1 := congrArg e h
      _ = 1 := map_one e
  · right; left
    calc
      b = e (e.symm b) := (e.apply_symm_apply b).symm
      _ = e (Multiplicative.ofAdd 1) := congrArg e h
      _ = a := zmodMulEquivOfGenerator_apply_ofAdd_one _ _
  · right; right
    calc
      b = e (e.symm b) := (e.apply_symm_apply b).symm
      _ = e ((Multiplicative.ofAdd 1)⁻¹) := congrArg e h
      _ = a⁻¹ := by
        rw [map_inv, zmodMulEquivOfGenerator_apply_ofAdd_one]

/-- The unique equivalence between two three-element cyclic groups which
sends the displayed generator to the displayed generator. -/
noncomputable def alignOrderThreeGenerators
    {L R : Type*} [Group L] [Finite L] [Group R] [Finite R]
    (hL : Nat.card L = 3) (hR : Nat.card R = 3)
    (a : L) (ha : a ≠ 1) (c : R) (hc : c ≠ 1) : L ≃* R := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact (zmodMulEquivOfGenerator
      (fun x ↦ (zpowers_eq_top_of_prime_card hL ha).ge (Subgroup.mem_top x)) hL).symm.trans
    (zmodMulEquivOfGenerator
      (fun x ↦ (zpowers_eq_top_of_prime_card hR hc).ge (Subgroup.mem_top x)) hR)

@[simp] theorem alignOrderThreeGenerators_apply
    {L R : Type*} [Group L] [Finite L] [Group R] [Finite R]
    (hL : Nat.card L = 3) (hR : Nat.card R = 3)
    (a : L) (ha : a ≠ 1) (c : R) (hc : c ≠ 1) :
    alignOrderThreeGenerators hL hR a ha c hc a = c := by
  simp [alignOrderThreeGenerators]

private theorem sourceMap4_generator_values :
    sourceMap4 (stabilizerGenerator 0) ≠ 1 ∧
    sourceMap4 (stabilizerGenerator 1) = 1 ∧
    sourceMap4 (stabilizerGenerator 2) = 1 ∧
    sourceMap4 (stabilizerGenerator 3) =
      sourceMap4 (stabilizerGenerator 0) := by native_decide

private theorem sourceMap5_generator_values :
    sourceMap5 (stabilizerGenerator 0) ≠ 1 ∧
    sourceMap5 (stabilizerGenerator 1) = 1 ∧
    sourceMap5 (stabilizerGenerator 2) = 1 ∧
    sourceMap5 (stabilizerGenerator 3) =
      (sourceMap5 (stabilizerGenerator 0))⁻¹ := by native_decide

private theorem sourceMap6_generator_values :
    sourceMap6 (stabilizerGenerator 0) ≠ 1 ∧
    sourceMap6 (stabilizerGenerator 1) = 1 ∧
    sourceMap6 (stabilizerGenerator 2) = 1 ∧
    sourceMap6 (stabilizerGenerator 3) = 1 := by native_decide

private theorem sourceMap7_generator_values :
    sourceMap7 (stabilizerGenerator 0) = 1 ∧
    sourceMap7 (stabilizerGenerator 1) = 1 ∧
    sourceMap7 (stabilizerGenerator 2) = 1 ∧
    sourceMap7 (stabilizerGenerator 3) ≠ 1 := by native_decide

/-- The normal Klein four subgroup in the `A4` factor of the common point
stabilizer. -/
def kleinFour : Subgroup SourceStabilizer where
  carrier := {x | x.1.index.val = 0 ∨ x.1.index.val = 2 ∨
    x.1.index.val = 3 ∨ x.1.index.val = 15}
  one_mem' := by native_decide
  mul_mem' := by native_decide +revert
  inv_mem' := by native_decide +revert

local instance kleinFourMembership (x : SourceStabilizer) :
    Decidable (x ∈ kleinFour) := by
  change Decidable (x.1.index.val = 0 ∨ x.1.index.val = 2 ∨
    x.1.index.val = 3 ∨ x.1.index.val = 15)
  infer_instance

local instance kleinFourNormal : kleinFour.Normal where
  conj_mem := by native_decide +revert

private theorem kleinFour_card : Nat.card kleinFour = 4 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  native_decide +revert

private theorem no_surjective_order_six_quotient
    {L : Type*} [Group L] [Finite L]
    (f : SourceStabilizer →* L) (hf : Function.Surjective f)
    (hL : Nat.card L = 6) (hnoncomm : ¬ IsMulCommutative L) : False := by
  let M := kleinFour.map f
  letI : M.Normal := Subgroup.Normal.map kleinFourNormal f hf
  have hMfour : Nat.card M ∣ 4 := by
    simpa only [M, kleinFour_card] using Subgroup.card_map_dvd kleinFour f
  have hMsix : Nat.card M ∣ 6 := by
    simpa only [hL] using M.card_subgroup_dvd_card
  have hMtwo : Nat.card M ∣ 2 := by
    simpa using Nat.dvd_gcd hMfour hMsix
  have hM : Nat.card M = 1 ∨ Nat.card M = 2 :=
    (Nat.dvd_prime (by norm_num)).mp hMtwo
  rcases hM with hMone | hMtwo
  · have hMbot : M = ⊥ := (Subgroup.card_eq_one).mp hMone
    have hle : kleinFour ≤ f.ker :=
      (Subgroup.map_eq_bot_iff kleinFour).mp hMbot
    have hkernel : Nat.card f.ker = 6 := by
      have hcard := f.ker.card_mul_index
      rw [Subgroup.index_ker, f.range_eq_top_of_surjective hf,
        Nat.card_congr Subgroup.topEquiv.toEquiv,
        PrimitiveAffineEightFrameRow4InducedBinding.sourceStabilizer_card,
        hL] at hcard
      omega
    have hdvd : 4 ∣ 6 := by
      rw [← kleinFour_card, ← hkernel]
      exact Subgroup.card_dvd_of_le hle
    norm_num at hdvd
  · have hcenter : M ≤ Subgroup.center L :=
      DegreeEightLiteralLocalRowCatalogue.normal_card_two_le_center M hMtwo
    let q : L →* L ⧸ M := QuotientGroup.mk' M
    have hquot : Nat.card (L ⧸ M) = 3 := by
      have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup M
      rw [hL, hMtwo] at hcard
      omega
    letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    letI : IsCyclic (L ⧸ M) := isCyclic_of_prime_card hquot
    apply hnoncomm
    exact ⟨⟨commutative_of_cyclic_center_quotient q (by
      simpa only [q, QuotientGroup.ker_mk'] using hcenter)⟩⟩

private theorem sourceMap_complete
    {L : Type*} [Group L] [Finite L]
    (f : SourceStabilizer →* L) (hf : Function.Surjective f)
    (hL : Nat.card L = 3) :
    (∃ e : L ≃* PrimitiveAffineEightFrameRow4InducedBinding.LocalTarget,
      e.toMonoidHom.comp f = sourceMap4) ∨
    (∃ e : L ≃* PrimitiveAffineEightFrameRow5InducedBinding.LocalTarget,
      e.toMonoidHom.comp f = sourceMap5) ∨
    (∃ e : L ≃* PrimitiveAffineEightFrameRow6InducedBinding.LocalTarget,
      e.toMonoidHom.comp f = sourceMap6) ∨
    (∃ e : L ≃* PrimitiveAffineEightFrameRow7InducedBinding.LocalTarget,
      e.toMonoidHom.comp f = sourceMap7) := by
  let s0 := stabilizerGenerator (0 : Fin 4)
  let s3 := stabilizerGenerator (3 : Fin 4)
  let a := f s0
  let b := f s3
  have h1 := map_generator_one_eq_one f hL
  have h2 := map_generator_two_eq_one f hL
  have hab : a ≠ 1 ∨ b ≠ 1 := by
    by_contra hab
    push_neg at hab
    rcases hab with ⟨ha, hb⟩
    have hfone : f = 1 := by
      apply hom_ext_stabilizerGenerator
      intro j
      fin_cases j
      · simpa only [a] using ha
      · simpa only [h1, MonoidHom.one_apply]
      · simpa only [h2, MonoidHom.one_apply]
      · simpa only [b] using hb
    have hsub : Subsingleton L := ⟨fun x y ↦ by
      obtain ⟨u, rfl⟩ := hf x
      obtain ⟨v, rfl⟩ := hf y
      rw [hfone]
      simp⟩
    have hcardle : Nat.card L ≤ 1 :=
      Finite.card_le_one_iff_subsingleton.mpr hsub
    omega
  by_cases ha : a ≠ 1
  · rcases eq_one_or_eq_or_eq_inv_of_card_three hL ha b with
      hb1 | hba | hbinv
    · rcases sourceMap6_generator_values with ⟨hc, hc1, hc2, hc3⟩
      let e := alignOrderThreeGenerators hL
        PrimitiveAffineEightFrameRow6InducedBinding.localTarget_card
        a ha (sourceMap6 s0) hc
      right; right; left
      refine ⟨e, ?_⟩
      apply hom_ext_stabilizerGenerator
      intro j
      fin_cases j
      · change e a = sourceMap6 s0
        simpa only [e] using alignOrderThreeGenerators_apply hL
          PrimitiveAffineEightFrameRow6InducedBinding.localTarget_card
          a ha (sourceMap6 s0) hc
      · change e (f (stabilizerGenerator 1)) =
          sourceMap6 (stabilizerGenerator 1)
        rw [h1, hc1, map_one]
      · change e (f (stabilizerGenerator 2)) =
          sourceMap6 (stabilizerGenerator 2)
        rw [h2, hc2, map_one]
      · change e b = sourceMap6 s3
        rw [hb1, hc3, map_one]
    · rcases sourceMap4_generator_values with ⟨hc, hc1, hc2, hc3⟩
      let e := alignOrderThreeGenerators hL
        PrimitiveAffineEightFrameRow4InducedBinding.localTarget_card
        a ha (sourceMap4 s0) hc
      left
      refine ⟨e, ?_⟩
      apply hom_ext_stabilizerGenerator
      intro j
      fin_cases j
      · change e a = sourceMap4 s0
        simpa only [e] using alignOrderThreeGenerators_apply hL
          PrimitiveAffineEightFrameRow4InducedBinding.localTarget_card
          a ha (sourceMap4 s0) hc
      · change e (f (stabilizerGenerator 1)) =
          sourceMap4 (stabilizerGenerator 1)
        rw [h1, hc1, map_one]
      · change e (f (stabilizerGenerator 2)) =
          sourceMap4 (stabilizerGenerator 2)
        rw [h2, hc2, map_one]
      · change e b = sourceMap4 s3
        rw [hba, hc3]
        simpa only [e] using alignOrderThreeGenerators_apply hL
          PrimitiveAffineEightFrameRow4InducedBinding.localTarget_card
          a ha (sourceMap4 s0) hc
    · rcases sourceMap5_generator_values with ⟨hc, hc1, hc2, hc3⟩
      let e := alignOrderThreeGenerators hL
        PrimitiveAffineEightFrameRow5InducedBinding.localTarget_card
        a ha (sourceMap5 s0) hc
      right; left
      refine ⟨e, ?_⟩
      apply hom_ext_stabilizerGenerator
      intro j
      fin_cases j
      · change e a = sourceMap5 s0
        simpa only [e] using alignOrderThreeGenerators_apply hL
          PrimitiveAffineEightFrameRow5InducedBinding.localTarget_card
          a ha (sourceMap5 s0) hc
      · change e (f (stabilizerGenerator 1)) =
          sourceMap5 (stabilizerGenerator 1)
        rw [h1, hc1, map_one]
      · change e (f (stabilizerGenerator 2)) =
          sourceMap5 (stabilizerGenerator 2)
        rw [h2, hc2, map_one]
      · change e b = sourceMap5 s3
        rw [hbinv, hc3, map_inv]
        simpa only [e] using congrArg Inv.inv
          (alignOrderThreeGenerators_apply hL
            PrimitiveAffineEightFrameRow5InducedBinding.localTarget_card
            a ha (sourceMap5 s0) hc)
  · have hb : b ≠ 1 := hab.resolve_left ha
    have ha1 : a = 1 := not_ne_iff.mp ha
    rcases sourceMap7_generator_values with ⟨hc0, hc1, hc2, hc⟩
    let e := alignOrderThreeGenerators hL
      PrimitiveAffineEightFrameRow7InducedBinding.localTarget_card
      b hb (sourceMap7 s3) hc
    right; right; right
    refine ⟨e, ?_⟩
    apply hom_ext_stabilizerGenerator
    intro j
    fin_cases j
    · change e a = sourceMap7 s0
      rw [ha1, hc0, map_one]
    · change e (f (stabilizerGenerator 1)) =
        sourceMap7 (stabilizerGenerator 1)
      rw [h1, hc1, map_one]
    · change e (f (stabilizerGenerator 2)) =
        sourceMap7 (stabilizerGenerator 2)
      rw [h2, hc2, map_one]
    · change e b = sourceMap7 s3
      simpa only [e] using alignOrderThreeGenerators_apply hL
        PrimitiveAffineEightFrameRow7InducedBinding.localTarget_card
        b hb (sourceMap7 s3) hc

/-- The four rows indexed in their dataset order. -/
noncomputable def row (j : Fin 4) : DegreeEightLiteralLocalRow LiteralAction :=
  match j with
  | ⟨0, _⟩ => row4
  | ⟨1, _⟩ => row5
  | ⟨2, _⟩ => row6
  | ⟨3, _⟩ => row7

@[simp] theorem row_zero : row 0 = row4 := rfl

@[simp] theorem row_one : row 1 = row5 := rfl

@[simp] theorem row_two : row 2 = row6 := rfl

@[simp] theorem row_three : row 3 = row7 := rfl

/-- Complete local-row catalogue for the common order-288 top. -/
noncomputable def literalLocalCatalogue :
    DegreeEightLiteralLocalRowCatalogue LiteralAction where
  Row := Fin 4
  row := row
  complete := by
    intro L _ _ f hf hcard
    let f0 : SourceStabilizer →* L :=
      f.comp R4.sourceStabilizerEquivLiteral.toMonoidHom
    have hf0 : Function.Surjective f0 :=
      hf.comp R4.sourceStabilizerEquivLiteral.surjective
    rcases hcard with hL | ⟨hL, hnoncomm⟩
    · rcases sourceMap_complete f0 hf0 hL with h4 | h5 | h6 | h7
      · obtain ⟨e, he⟩ := h4
        refine ⟨0, e, ?_⟩
        ext x
        simp only [row_zero]
        change e (f x) = sourceMap4 (R4.sourceStabilizerEquivLiteral.symm x)
        have hx := DFunLike.congr_fun he (R4.sourceStabilizerEquivLiteral.symm x)
        change e (f (R4.sourceStabilizerEquivLiteral
          (R4.sourceStabilizerEquivLiteral.symm x))) =
            sourceMap4 (R4.sourceStabilizerEquivLiteral.symm x) at hx
        simpa only [R4.sourceStabilizerEquivLiteral.apply_symm_apply] using hx
      · obtain ⟨e, he⟩ := h5
        refine ⟨1, e, ?_⟩
        ext x
        simp only [row_one]
        change e (f x) = sourceMap5 (R4.sourceStabilizerEquivLiteral.symm x)
        have hx := DFunLike.congr_fun he (R4.sourceStabilizerEquivLiteral.symm x)
        change e (f (R4.sourceStabilizerEquivLiteral
          (R4.sourceStabilizerEquivLiteral.symm x))) =
            sourceMap5 (R4.sourceStabilizerEquivLiteral.symm x) at hx
        simpa only [R4.sourceStabilizerEquivLiteral.apply_symm_apply] using hx
      · obtain ⟨e, he⟩ := h6
        refine ⟨2, e, ?_⟩
        ext x
        simp only [row_two]
        change e (f x) = sourceMap6 (R4.sourceStabilizerEquivLiteral.symm x)
        have hx := DFunLike.congr_fun he (R4.sourceStabilizerEquivLiteral.symm x)
        change e (f (R4.sourceStabilizerEquivLiteral
          (R4.sourceStabilizerEquivLiteral.symm x))) =
            sourceMap6 (R4.sourceStabilizerEquivLiteral.symm x) at hx
        simpa only [R4.sourceStabilizerEquivLiteral.apply_symm_apply] using hx
      · obtain ⟨e, he⟩ := h7
        refine ⟨3, e, ?_⟩
        ext x
        simp only [row_three]
        change e (f x) = sourceMap7 (R4.sourceStabilizerEquivLiteral.symm x)
        have hx := DFunLike.congr_fun he (R4.sourceStabilizerEquivLiteral.symm x)
        change e (f (R4.sourceStabilizerEquivLiteral
          (R4.sourceStabilizerEquivLiteral.symm x))) =
            sourceMap7 (R4.sourceStabilizerEquivLiteral.symm x) at hx
        simpa only [R4.sourceStabilizerEquivLiteral.apply_symm_apply] using hx
    · exact False.elim (no_surjective_order_six_quotient f0 hf0 hL hnoncomm)

/-- Build a literal top match from any of the four emitted Cayley models of
the common permutation action. -/
def literalTopMatchFor
    {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    {ModelGroup : Type} [Group ModelGroup]
    (actionModelEquiv : LiteralAction ≃* ModelGroup)
    (pointEquiv : block.Points ≃ Fin 8)
    (conjugator : Equiv.Perm (Fin 8))
    (hconjugated :
      MulAut.conj conjugator • relabelSubgroup pointEquiv block.Top =
        LiteralAction) :
    DegreeFourZeroCoreEightLiteralTopMatch block ModelGroup where
  literalAction := LiteralAction
  actionModelEquiv := actionModelEquiv
  pointEquiv := pointEquiv
  conjugator := conjugator
  conjugated := hconjugated

/-- Row-four specialization of the common literal top match. -/
abbrev literalTopMatch
    {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (pointEquiv : block.Points ≃ Fin 8)
    (conjugator : Equiv.Perm (Fin 8))
    (hconjugated :
      MulAut.conj conjugator • relabelSubgroup pointEquiv block.Top =
        LiteralAction) :=
  literalTopMatchFor block
    PrimitiveAffineEightFrameRow4TopCertificate.originalEquiv.symm
    pointEquiv conjugator hconjugated

/-- A selected actual local map with its target fixed to one of the four
generated rows.  Keeping the row in the type lets the downstream induced
module construction reduce by cases without any casts between the four
distinct emitted target types. -/
class ExactActualMatch
    {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
    {ModelGroup : Type} [Group ModelGroup]
    (actionModelEquiv : LiteralAction ≃* ModelGroup)
    (pointEquiv : block.Points ≃ Fin 8)
    (conjugator : Equiv.Perm (Fin 8))
    (hconjugated :
      MulAut.conj conjugator • relabelSubgroup pointEquiv block.Top =
        LiteralAction)
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥)
    (j : Fin 4) : Type where
  targetEquiv : LocalQuotient block P ≃* (row j).ModelLocalGroup
  compatible : targetEquiv.toMonoidHom.comp
      (DegreeFourZeroCoreEightLiteralTopMatch.transportedLocalMap
        (block := block) (P := P)
        (literalTopMatchFor block actionModelEquiv pointEquiv conjugator
          hconjugated)
        hr hD (0 : Fin 8)) =
    (row j).literalLocalMap

/-- Apply the complete four-row catalogue while retaining the chosen row
as a dependent index. -/
noncomputable def selectExactActual
    {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
    {ModelGroup : Type} [Group ModelGroup]
    (actionModelEquiv : LiteralAction ≃* ModelGroup)
    (pointEquiv : block.Points ≃ Fin 8)
    (conjugator : Equiv.Perm (Fin 8))
    (hconjugated :
      MulAut.conj conjugator • relabelSubgroup pointEquiv block.Top =
        LiteralAction)
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥) :
    Σ j : Fin 4, ExactActualMatch block P actionModelEquiv pointEquiv
      conjugator hconjugated hr hD j := by
  let topMatch := literalTopMatchFor block actionModelEquiv pointEquiv
    conjugator hconjugated
  let f := DegreeFourZeroCoreEightLiteralTopMatch.transportedLocalMap
    (block := block) (P := P) topMatch hr hD (0 : Fin 8)
  have hf : Function.Surjective f :=
    DegreeFourZeroCoreEightLiteralTopMatch.transportedLocalMap_surjective
      (block := block) (P := P) topMatch hr hD (0 : Fin 8)
  have hcard : Nat.card (LocalQuotient block P) = 3 ∨
      (Nat.card (LocalQuotient block P) = 6 ∧
        ¬ IsMulCommutative (LocalQuotient block P)) := by
    rcases degreeFourZeroCoreTopStabilizerLocalTarget_card block P hr with
      h3 | h6
    · exact Or.inl h3
    · refine Or.inr ⟨h6, ?_⟩
      let C0 := chart block P
      letI : Fact P.p.Prime := C0.primeFact
      have hp : P.p = 2 := degreeFour_profilePrime_eq_two block P hr
      have hV : Module.finrank (ZMod P.p) C0.V = 2 := by
        change C0.d = 2
        exact (degreeFour_translationDimension block P hr).2
      exact not_isMulCommutative_of_faithful_binary_plane_card_six_at
        hp (binaryAffineLocalLinearRepresentation block P).ρ h6 hV
        (binaryAffineLocalLinearRepresentation_injective block P)
  let hselected := literalLocalCatalogue.complete
    (LocalQuotient block P) f hf hcard
  let j : Fin 4 := Classical.choose hselected
  let e : LocalQuotient block P ≃* (row j).ModelLocalGroup :=
    Classical.choose (Classical.choose_spec hselected)
  have he : e.toMonoidHom.comp f = (row j).literalLocalMap :=
    Classical.choose_spec (Classical.choose_spec hselected)
  exact ⟨j, ⟨e, he⟩⟩

end PrimitiveAffineEightFrameRows4To7LocalCatalogue
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
