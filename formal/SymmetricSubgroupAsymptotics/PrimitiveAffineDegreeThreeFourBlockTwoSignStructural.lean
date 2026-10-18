import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockTwoSignSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeSixS3WreathGroup
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoQuotientEnvelopeTransport
import SymmetricSubgroupAsymptotics.FiniteGroupPaddedGenerators

/-!
# Structural ingredients for the two-sign four-block source

This file contains two parts of the two-sign construction which do not
depend on identifying the particular invariant ternary sections.

* The complete normal menu is split exactly into the bottom axis, the
  interval above a fixed normal subgroup E, and the remaining literal
  proper axes.
* The comparator (S₃ ≀ C₂) × C₂² is given its faithful disjoint action on
  6 + 2 + 2 = 10 points.

The later instantiation may group the proper axes further by their
intersection with the ternary layer.  The theorem here is deliberately
literal and uses no normal-subgroup census.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

attribute [-instance] originalNormalFintype

private abbrev NormalAxis (G : Type*) [Group G] :=
  {N : Subgroup G // N.Normal}

/-- Literal normal axes which do not contain E. -/
abbrev TwoSignBelowAxis {G : Type*} [Group G] (E : Subgroup G) :=
  {N : NormalAxis G // ¬ E ≤ N.1}

/-- Literal nonbottom normal axes which do not contain E. -/
abbrev TwoSignProperAxis {G : Type*} [Group G] (E : Subgroup G) :=
  {N : TwoSignBelowAxis E // N.1.1 ≠ ⊥}

/-- The underlying original normal axis of a proper stratum. -/
def twoSignProperAxis
    {G : Type*} [Group G] {E : Subgroup G}
    (N : TwoSignProperAxis E) : NormalAxis G :=
  N.1.1

/-- Exact all-normal stratification at an arbitrary normal subgroup E.

The interval above E injects into the normal menu of G / E.  Below E, the
unique possible bottom axis gives Epi(J,G).  Every remaining literal axis
is bounded by the complete quotient menu of its own quotient. -/
theorem completeQuotientWeight_le_twoSign_strata
    {G : Type*} [Group G] [Finite G]
    (E : Subgroup G) [E.Normal]
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) :
    completeQuotientWeight (R := G) J ≤
      (Nat.card (GroupEpimorphism J G) : ℝ) +
        completeQuotientWeight (R := G ⧸ E) J +
        ∑ N : TwoSignProperAxis E,
          Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.bundledNormalQuotientWeight
            (twoSignProperAxis N) J := by
  let Q : NormalAxis G → Prop := fun N ↦ E ≤ N.1
  let f : NormalAxis G → ℝ := fun N ↦
    Nat.card (GroupEpimorphism J (G ⧸ N.1))
  have hsplit := Fintype.sum_subtype_add_sum_subtype Q f
  have habove :
      (∑ N : {N : NormalAxis G // Q N}, f N.1) ≤
        completeQuotientWeight (R := G ⧸ E) J := by
    exact normalAxisAbove_epimorphism_sum_le_completeQuotientWeight E J
  let B := TwoSignBelowAxis E
  let fB : B → ℝ := fun N ↦ f N.1
  let P : B → Prop := fun N ↦ N.1.1 = ⊥
  have hsplitBelow := Fintype.sum_subtype_add_sum_subtype P fB
  have hbottomPoint : ∀ N : {N : B // P N},
      fB N.1 = (Nat.card (GroupEpimorphism J G) : ℝ) := by
    intro N
    haveI : N.1.1.1.Normal := N.1.1.2
    dsimp only [fB, f, P]
    exact_mod_cast fusionGroupEpimorphism_card_congr (MulEquiv.refl J)
      ((QuotientGroup.quotientMulEquivOfEq N.2).trans
        QuotientGroup.quotientBot)
  have hbottomCard : Nat.card {N : B // P N} ≤ 1 := by
    rw [Finite.card_le_one_iff_subsingleton]
    constructor
    intro N M
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact N.2.trans M.2.symm
  have hbottom :
      (∑ N : {N : B // P N}, fB N.1) ≤
        (Nat.card (GroupEpimorphism J G) : ℝ) := by
    calc
      (∑ N : {N : B // P N}, fB N.1) =
          (Nat.card {N : B // P N} : ℝ) *
            (Nat.card (GroupEpimorphism J G) : ℝ) := by
        simp_rw [hbottomPoint]
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
          ← Nat.card_eq_fintype_card]
      _ ≤ 1 * (Nat.card (GroupEpimorphism J G) : ℝ) := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast hbottomCard
        · exact Nat.cast_nonneg _
      _ = _ := one_mul _
  have hproperPoint : ∀ N : {N : B // ¬ P N},
      fB N.1 ≤
        Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.bundledNormalQuotientWeight
          (twoSignProperAxis N) J := by
    intro N
    let M : NormalAxis (G ⧸ N.1.1.1) := ⟨⊥, inferInstance⟩
    have haxis := card_groupEpimorphism_le_completeQuotientWeight J M
      (QuotientGroup.quotientBot (G := G ⧸ N.1.1.1)).symm
    simpa only [fB, f, twoSignProperAxis,
      Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.bundledNormalQuotientWeight]
      using haxis
  have hproper :
      (∑ N : {N : B // ¬ P N}, fB N.1) ≤
        ∑ N : TwoSignProperAxis E,
          Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.bundledNormalQuotientWeight
            (twoSignProperAxis N) J := by
    apply Finset.sum_le_sum
    intro N _
    exact hproperPoint N
  have hbelow :
      (∑ N : {N : NormalAxis G // ¬ Q N}, f N.1) ≤
        (Nat.card (GroupEpimorphism J G) : ℝ) +
          ∑ N : TwoSignProperAxis E,
            Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.bundledNormalQuotientWeight
              (twoSignProperAxis N) J := by
    change (∑ N : B, fB N) ≤ _
    rw [hsplitBelow.symm]
    exact add_le_add hbottom hproper
  change (↑(∑ N : NormalAxis G,
    Nat.card (GroupEpimorphism J (G ⧸ N.1))) : ℝ) ≤ _
  rw [Nat.cast_sum]
  change (∑ N : NormalAxis G, f N) ≤ _
  rw [hsplit.symm]
  calc
    (∑ N : {N : NormalAxis G // Q N}, f N.1) +
        ∑ N : {N : NormalAxis G // ¬ Q N}, f N.1 ≤
      completeQuotientWeight (R := G ⧸ E) J +
        ((Nat.card (GroupEpimorphism J G) : ℝ) +
          ∑ N : TwoSignProperAxis E,
            Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.bundledNormalQuotientWeight
              (twoSignProperAxis N) J) :=
      add_le_add habove hbelow
    _ = _ := by ring

/-- The literal proper axes form a subtype of the full normal menu.  For a
group of order at most `2^12`, their number is therefore at most `2^144`.
This avoids enumerating the proper ternary sections. -/
theorem twoSignProperAxis_card_le_two_pow_144
    {G : Type*} [Group G] [Finite G]
    (E : Subgroup G) (hG : Nat.card G ≤ 2 ^ 12) :
    Nat.card (TwoSignProperAxis E) ≤ 2 ^ 144 := by
  have hinjective : Function.Injective
      (fun N : TwoSignProperAxis E ↦ (N.1.1 : NormalAxis G)) := by
    intro N M h
    apply Subtype.ext
    apply Subtype.ext
    exact h
  calc
    Nat.card (TwoSignProperAxis E) ≤ Nat.card (NormalAxis G) :=
      Nat.card_le_card_of_injective _ hinjective
    _ ≤ 2 ^ (12 * 12) := normalSubgroup_card_le_two_pow_sq 12 hG
    _ = 2 ^ 144 := by norm_num

/-- Uniform numerical budget for the whole two-sign source.  A possible
rank-two bottom, the signed top, and every proper ternary section all fit
simultaneously under the historical `2^384` coefficient. -/
theorem twoSign_uniform_mainCoefficient_le
    {G : Type*} [Group G] [Finite G]
    (E : Subgroup G) (hG : Nat.card G ≤ 2 ^ 12) :
    (2 : ℝ) ^ (200 : ℕ) + (2 : ℝ) ^ (128 : ℕ) +
        ∑ _N : TwoSignProperAxis E, (2 : ℝ) ^ (200 : ℕ) ≤
      (2 : ℝ) ^ (384 : ℝ) := by
  have hcard := twoSignProperAxis_card_le_two_pow_144 E hG
  have hcardReal : (Nat.card (TwoSignProperAxis E) : ℝ) ≤
      (2 : ℝ) ^ (144 : ℕ) := by
    exact_mod_cast hcard
  have hsections :
      (∑ _N : TwoSignProperAxis E, (2 : ℝ) ^ (200 : ℕ)) ≤
        (2 : ℝ) ^ (344 : ℕ) := by
    calc
      (∑ _N : TwoSignProperAxis E, (2 : ℝ) ^ (200 : ℕ)) =
          (Nat.card (TwoSignProperAxis E) : ℝ) *
            (2 : ℝ) ^ (200 : ℕ) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
          Fintype.card_eq_nat_card]
      _ ≤ (2 : ℝ) ^ (144 : ℕ) * (2 : ℝ) ^ (200 : ℕ) := by
        exact mul_le_mul_of_nonneg_right hcardReal (by positivity)
      _ = (2 : ℝ) ^ (344 : ℕ) := by rw [← pow_add]
  have h200 : (2 : ℝ) ^ (200 : ℕ) ≤ (2 : ℝ) ^ (344 : ℕ) :=
    pow_le_pow_right₀ (by norm_num) (by norm_num)
  have h128 : (2 : ℝ) ^ (128 : ℕ) ≤ (2 : ℝ) ^ (344 : ℕ) :=
    pow_le_pow_right₀ (by norm_num) (by norm_num)
  calc
    (2 : ℝ) ^ (200 : ℕ) + (2 : ℝ) ^ (128 : ℕ) +
        ∑ _N : TwoSignProperAxis E, (2 : ℝ) ^ (200 : ℕ) ≤
      (2 : ℝ) ^ (200 : ℕ) + (2 : ℝ) ^ (128 : ℕ) +
        (2 : ℝ) ^ (344 : ℕ) :=
      add_le_add (le_refl _) hsections
    _ ≤ (2 : ℝ) ^ (344 : ℕ) + (2 : ℝ) ^ (344 : ℕ) +
        (2 : ℝ) ^ (344 : ℕ) :=
      add_le_add (add_le_add h200 h128) (le_refl _)
    _ = 3 * (2 : ℝ) ^ (344 : ℕ) := by ring
    _ ≤ 4 * (2 : ℝ) ^ (344 : ℕ) := by
      exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    _ = (2 : ℝ) ^ (346 : ℕ) := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, ← pow_add]
    _ ≤ (2 : ℝ) ^ (384 : ℕ) :=
      pow_le_pow_right₀ (by norm_num) (by norm_num)
    _ = (2 : ℝ) ^ (384 : ℝ) := (Real.rpow_natCast 2 384).symm

/-- Pull a normal axis back along a surjective group map. -/
private def normalAxisComap
    {G H : Type*} [Group G] [Group H]
    (pi : G →* H) :
    NormalAxis H → NormalAxis G :=
  fun M ↦ ⟨M.1.comap pi, Subgroup.Normal.comap M.2 pi⟩

private theorem normalAxisComap_injective
    {G H : Type*} [Group G] [Group H]
    (pi : G →* H) (hpi : Function.Surjective pi) :
    Function.Injective (normalAxisComap pi) := by
  intro M N h
  apply Subtype.ext
  have hcomap : M.1.comap pi = N.1.comap pi :=
    congrArg (fun K : NormalAxis G ↦ K.1) h
  have hmap := congrArg (Subgroup.map pi) hcomap
  calc
    M.1 = Subgroup.map pi (M.1.comap pi) :=
      (Subgroup.map_comap_eq_self_of_surjective hpi M.1).symm
    _ = Subgroup.map pi (N.1.comap pi) := hmap
    _ = N.1 := Subgroup.map_comap_eq_self_of_surjective hpi N.1

/-- The quotient by a pulled-back axis is the corresponding target
quotient. -/
private def quotientComapEquiv
    {G H : Type*} [Group G] [Group H]
    (pi : G →* H) (hpi : Function.Surjective pi)
    (M : NormalAxis H) :
    G ⧸ M.1.comap pi ≃* H ⧸ M.1 := by
  letI : (M.1.comap pi).Normal := Subgroup.Normal.comap M.2 pi
  letI : (Subgroup.map pi (M.1.comap pi)).Normal :=
    Subgroup.Normal.map (Subgroup.Normal.comap M.2 pi) pi hpi
  have hker : pi.ker ≤ M.1.comap pi := by
    intro x hx
    change pi x ∈ M.1
    rw [(MonoidHom.mem_ker).mp hx]
    exact M.1.one_mem
  have hmap : Subgroup.map pi (M.1.comap pi) = M.1 :=
    Subgroup.map_comap_eq_self_of_surjective hpi M.1
  exact
    (quotientEquivOfKerLe pi hpi (M.1.comap pi) hker).trans
      (QuotientGroup.quotientMulEquivOfEq hmap)

/-- Complete quotient weight is monotone under taking a quotient target.
Every literal normal axis of the target pulls back injectively, and its
quotient group is unchanged. -/
theorem completeQuotientWeight_le_of_surjective
    {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (pi : G →* H) (hpi : Function.Surjective pi)
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) :
    completeQuotientWeight (R := H) J ≤
      completeQuotientWeight (R := G) J := by
  let kappa : NormalAxis H → NormalAxis G := normalAxisComap pi
  let f : NormalAxis G → ℝ := fun N ↦
    Nat.card (GroupEpimorphism J (G ⧸ N.1))
  have hkappa : Function.Injective kappa :=
    normalAxisComap_injective pi hpi
  have htransport : ∀ M : NormalAxis H,
      (Nat.card (GroupEpimorphism J (H ⧸ M.1)) : ℝ) =
        f (kappa M) := by
    intro M
    dsimp only [f, kappa, normalAxisComap]
    exact_mod_cast fusionGroupEpimorphism_card_congr (MulEquiv.refl J)
      (quotientComapEquiv pi hpi M).symm
  unfold completeQuotientWeight completeQuotientCount
  rw [Nat.cast_sum, Nat.cast_sum]
  calc
    (∑ M : NormalAxis H,
        (Nat.card (GroupEpimorphism J (H ⧸ M.1)) : ℝ)) =
        ∑ M : NormalAxis H, f (kappa M) :=
      Finset.sum_congr rfl (fun M _ ↦ htransport M)
    _ = ∑ N ∈ Finset.univ.image kappa, f N := by
      rw [Finset.sum_image (fun M _ N _ h ↦ hkappa h)]
    _ ≤ ∑ N : NormalAxis G, f N :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun N _ _ ↦ Nat.cast_nonneg _)

namespace DegreeThreeFourBlockTwoSignComparator

private abbrev S3 := Equiv.Perm (Fin 3)
private abbrev C2 := Multiplicative (ZMod 2)

/-- The natural imprimitive action of S₃ ≀ C₂ on two triples. -/
def wreathPointEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6 :=
  finSumFinEquiv

def wreathAction : DegreeSixS3Wreath.G →* Equiv.Perm (Fin 6) :=
  wreathPointEquiv.permCongrHom.toMonoidHom.comp
    (C2Wreath.action (MonoidHom.id S3))

theorem wreathAction_injective : Function.Injective wreathAction :=
  wreathPointEquiv.permCongrHom.injective.comp
    (C2Wreath.action_injective (MonoidHom.id S3) Function.injective_id)

/-- Append one disjoint regular binary orbit to a permutation action. -/
def appendC2PointEquiv (n : ℕ) :
    Fin n ⊕ (Fin 1 ⊕ Fin 1) ≃ Fin (n + 2) :=
  (Equiv.sumCongr (Equiv.refl (Fin n)) finSumFinEquiv).trans
    finSumFinEquiv

def appendC2Action {G : Type*} [Group G] {n : ℕ}
    (rho : G →* Equiv.Perm (Fin n)) :
    G × C2 →* Equiv.Perm (Fin (n + 2)) :=
  (appendC2PointEquiv n).permCongrHom.toMonoidHom.comp
    ((Equiv.Perm.sumCongrHom (Fin n) (Fin 1 ⊕ Fin 1)).comp
      (rho.prodMap (C2Wreath.blockSwap (Fin 1))))

theorem appendC2Action_injective
    {G : Type*} [Group G] {n : ℕ}
    (rho : G →* Equiv.Perm (Fin n))
    (hrho : Function.Injective rho) :
    Function.Injective (appendC2Action rho) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hsum : (Equiv.Perm.sumCongrHom (Fin n) (Fin 1 ⊕ Fin 1))
      ((rho.prodMap (C2Wreath.blockSwap (Fin 1))) x) = 1 := by
    apply (appendC2PointEquiv n).permCongrHom.injective
    rw [map_one]
    exact hx
  have hpair := Equiv.Perm.sumCongrHom_injective
    (hsum.trans (map_one _).symm)
  have hleft : rho x.1 = 1 := congrArg Prod.fst hpair
  have hright : C2Wreath.blockSwap (Fin 1) x.2 = 1 :=
    congrArg Prod.snd hpair
  apply Prod.ext
  · exact hrho (hleft.trans (map_one rho).symm)
  · rcases C2Wreath.cases x.2 with h | h
    · exact h
    · exfalso
      rw [h, C2Wreath.blockSwap] at hright
      simp only [MonoidHom.coe_mk, OneHom.coe_mk, C2Wreath.gen_ne_one,
        if_false] at hright
      have hpoint := congrArg
        (fun sigma : Equiv.Perm (Fin 1 ⊕ Fin 1) ↦ sigma (Sum.inl 0)) hright
      simp at hpoint

/-- Abstract group underlying the fixed degree-ten comparator. -/
abbrev QStarGroup := (DegreeSixS3Wreath.G × C2) × C2

/-- Faithful action of (S₃ ≀ C₂) × C₂² on ten points. -/
def qStarAction : QStarGroup →* Equiv.Perm (Fin 10) := by
  simpa only [show 6 + 2 = 8 by omega, show 8 + 2 = 10 by omega] using
    appendC2Action (appendC2Action wreathAction)

theorem qStarAction_injective : Function.Injective qStarAction := by
  simpa only [qStarAction] using
    appendC2Action_injective (appendC2Action wreathAction)
      (appendC2Action_injective wreathAction wreathAction_injective)

/-- The literal faithful degree-ten comparator subgroup. -/
abbrev QStar : Subgroup (Equiv.Perm (Fin 10)) :=
  qStarAction.range

/-- Identification of the abstract product with the literal comparator. -/
def qStarEquiv : QStarGroup ≃* QStar :=
  MonoidHom.ofInjective qStarAction_injective

/-- The top-only quotient D₈ × C₂² of the fixed comparator. -/
def qStarToD8C2C2 :
    QStarGroup →* ((DegreeSixS3Wreath.D8 × C2) × C2) :=
  (DegreeSixS3Wreath.projection.prodMap (MonoidHom.id C2)).prodMap
    (MonoidHom.id C2)

theorem qStarToD8C2C2_surjective :
    Function.Surjective qStarToD8C2C2 := by
  rintro ⟨⟨d, c₁⟩, c₂⟩
  obtain ⟨g, rfl⟩ := DegreeSixS3Wreath.projection_surjective d
  exact ⟨⟨⟨g, c₁⟩, c₂⟩, rfl⟩

/-- Forget the last auxiliary binary factor. -/
def qStarToWreathC2 : QStarGroup →* (DegreeSixS3Wreath.G × C2) :=
  MonoidHom.fst (DegreeSixS3Wreath.G × C2) C2

theorem qStarToWreathC2_surjective :
    Function.Surjective qStarToWreathC2 :=
  Prod.fst_surjective

/-- Forget both auxiliary binary factors. -/
def qStarToWreath : QStarGroup →* DegreeSixS3Wreath.G :=
  (MonoidHom.fst DegreeSixS3Wreath.G C2).comp qStarToWreathC2

theorem qStarToWreath_surjective :
    Function.Surjective qStarToWreath :=
  Prod.fst_surjective.comp Prod.fst_surjective

/-- Any quotient of the abstract comparator product has its complete
normal menu included in the one fixed literal degree-ten comparator. -/
theorem completeQuotientWeight_le_qStar_of_surjective
    {A : Type*} [Group A] [Finite A]
    (pi : QStarGroup →* A) (hpi : Function.Surjective pi)
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) :
    completeQuotientWeight (R := A) J ≤
      completeQuotientWeight (R := QStar) J := by
  calc
    completeQuotientWeight (R := A) J ≤
        completeQuotientWeight (R := QStarGroup) J :=
      completeQuotientWeight_le_of_surjective pi hpi J
    _ = completeQuotientWeight (R := QStar) J :=
      Non2UnipotentPrefixFiniteMenu.completeQuotientWeight_congr qStarEquiv J

end DegreeThreeFourBlockTwoSignComparator

namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

/-- Assemble the target comparison record once the literal top, proper-axis,
and bottom estimates have been proved against the degree-ten comparator.

The normal stratification is a theorem, rather than a field of the supplied
data.  Thus a caller cannot omit a normal stratum: the section type is
definitionally the full finite type of nonbottom axes not containing E. -/
noncomputable def degreeThreeFourBlockTwoSignComparison_of_literalBounds
    (bottomCoefficient : ℝ)
    (topCoefficient : ℝ)
    (sectionCoefficient : TwoSignProperAxis (E block P) → ℝ)
    (tailCoefficient : ℝ)
    (bottomCoefficient_nonneg : 0 ≤ bottomCoefficient)
    (topCoefficient_nonneg : 0 ≤ topCoefficient)
    (sectionCoefficient_nonneg :
      ∀ i, 0 ≤ sectionCoefficient i)
    (tailCoefficient_nonneg : 0 ≤ tailCoefficient)
    (top_bound : ∀ {b : ℕ}
      (J : Subgroup (Equiv.Perm (Fin b))),
      completeQuotientWeight
          (R := preE7NonPairAction w U ⧸ E block P) J ≤
        topCoefficient *
          completeQuotientWeight
            (R := DegreeThreeFourBlockTwoSignComparator.QStar) J)
    (section_bound : ∀ (i : TwoSignProperAxis (E block P)) {b : ℕ}
      (J : Subgroup (Equiv.Perm (Fin b))),
      bundledNormalQuotientWeight (twoSignProperAxis i) J ≤
        sectionCoefficient i *
          completeQuotientWeight
            (R := DegreeThreeFourBlockTwoSignComparator.QStar) J)
    (bottom_bound : ∀ {b : ℕ}
      (J : Subgroup (Equiv.Perm (Fin b))),
      (Nat.card
          (GroupEpimorphism J (preE7NonPairAction w U)) : ℝ) ≤
        bottomCoefficient *
            completeQuotientWeight
              (R := DegreeThreeFourBlockTwoSignComparator.QStar) J +
          tailCoefficient *
            (2 : ℝ) ^ ((Real.logb 2 3 / 3) * b))
    (mainCoefficient_le :
      bottomCoefficient + topCoefficient +
          ∑ i : TwoSignProperAxis (E block P), sectionCoefficient i ≤
        (2 : ℝ) ^ (384 : ℝ))
    (tailCoefficient_le :
      tailCoefficient ≤ (2 : ℝ) ^ (384 : ℝ)) :
    DegreeThreeFourBlockTwoSignComparison block P where
  Section := TwoSignProperAxis (E block P)
  sectionAxis := twoSignProperAxis
  Q := DegreeThreeFourBlockTwoSignComparator.QStar
  bottomCoefficient := bottomCoefficient
  topCoefficient := topCoefficient
  sectionCoefficient := sectionCoefficient
  tailCoefficient := tailCoefficient
  bottomCoefficient_nonneg := bottomCoefficient_nonneg
  topCoefficient_nonneg := topCoefficient_nonneg
  sectionCoefficient_nonneg := sectionCoefficient_nonneg
  tailCoefficient_nonneg := tailCoefficient_nonneg
  stratified_bound := by
    intro b J
    exact completeQuotientWeight_le_twoSign_strata (E block P) J
  top_bound := top_bound
  section_bound := section_bound
  bottom_bound := bottom_bound
  mainCoefficient_le := mainCoefficient_le
  tailCoefficient_le := tailCoefficient_le

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
