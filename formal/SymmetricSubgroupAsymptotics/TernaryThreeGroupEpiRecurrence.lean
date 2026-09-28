import SymmetricSubgroupAsymptotics.TernaryThreeGroupQuotientEpi
import SymmetricSubgroupAsymptotics.FusionEpimorphismTransport
import SymmetricSubgroupAsymptotics.PrimeElementaryEpimorphismBound
import SymmetricSubgroupAsymptotics.DegreeTwelveTopGeometry
import SymmetricSubgroupAsymptotics.C1NumericalRows
import SymmetricSubgroupAsymptotics.C1DegreeNineSourceRank

/-!
# Character-sensitive quotient epimorphism recursion for ternary groups

The source character rank is retained until the final application.  One
three-block layer contributes exactly one ninth of the block degree to the
base-three exponent.  This gives distinct generic and marked degree-nine
rows and prevents the marked improvement from being used inside degree 27.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

/-- A uniform fixed-action bound for all actual quotient targets.  The
constant is independent of the complete source subgroup and its degree. -/
def TernaryQuotientCharacterEnvelope {X : Type} [Finite X]
    (U : Subgroup (Equiv.Perm X)) (offset constant : ℝ) : Prop :=
  ∀ {Q : Type} [Group Q] [Finite Q]
    (q : U →* Q), Function.Surjective q →
    ∀ (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))),
      (Nat.card (GroupEpimorphism J Q) : ℝ) ≤
        constant * (3 : ℝ) ^
          ((Module.finrank (ZMod 3) (PrimeCharacters 3 J) : ℝ) +
            offset * b)

/-- The exact target-local factor retained by one arbitrary-normal block
section. -/
def ternaryBlockSectionConstant {X : Type} [Finite X]
    {U : Subgroup (Equiv.Perm X)} [MulAction.IsPretransitive U X] {x : X}
    (D : TransitiveThreeBlockCover U x) (hU : IsPGroup 3 U)
    (N : {N : Subgroup U // N.Normal}) : ℝ :=
  Nat.card (D.sectionModule hU N.1) *
    Nat.card (groupCohomology.H1 (D.sectionRepresentation hU N.1))

/-- The finite original-normal menu absorbs the target-local module and
cohomology factors only after they have been retained axis by axis. -/
def ternaryBlockAggregateConstant {X : Type} [Finite X]
    {U : Subgroup (Equiv.Perm X)} [MulAction.IsPretransitive U X] {x : X}
    (D : TransitiveThreeBlockCover U x) (hU : IsPGroup 3 U) : ℝ :=
  ∑ N : {N : Subgroup U // N.Normal},
    ternaryBlockSectionConstant D hU N

theorem ternaryBlockSectionConstant_nonneg {X : Type} [Finite X]
    {U : Subgroup (Equiv.Perm X)} [MulAction.IsPretransitive U X] {x : X}
    (D : TransitiveThreeBlockCover U x) (hU : IsPGroup 3 U)
    (N : {N : Subgroup U // N.Normal}) :
    0 ≤ ternaryBlockSectionConstant D hU N := by
  unfold ternaryBlockSectionConstant
  positivity

theorem ternaryBlockSectionConstant_le_aggregate {X : Type} [Finite X]
    {U : Subgroup (Equiv.Perm X)} [MulAction.IsPretransitive U X] {x : X}
    (D : TransitiveThreeBlockCover U x) (hU : IsPGroup 3 U)
    (N : {N : Subgroup U // N.Normal}) :
    ternaryBlockSectionConstant D hU N ≤
      ternaryBlockAggregateConstant D hU := by
  unfold ternaryBlockAggregateConstant
  exact Finset.single_le_sum
    (fun M _ => ternaryBlockSectionConstant_nonneg D hU M)
    (Finset.mem_univ N)

theorem ternaryBlockAggregateConstant_nonneg {X : Type} [Finite X]
    {U : Subgroup (Equiv.Perm X)} [MulAction.IsPretransitive U X] {x : X}
    (D : TransitiveThreeBlockCover U x) (hU : IsPGroup 3 U) :
    0 ≤ ternaryBlockAggregateConstant D hU := by
  unfold ternaryBlockAggregateConstant
  exact Finset.sum_nonneg fun N _ => ternaryBlockSectionConstant_nonneg D hU N

/-- A quotient of a faithful transitive three-point 3-group costs exactly
one copy of the complete ternary character space of the source. -/
theorem degreeThree_quotientCharacterEnvelope
    {X : Type} [Finite X]
    (U : Subgroup (Equiv.Perm X)) [MulAction.IsPretransitive U X]
    (hDegree : Nat.card X = 3) (hU : IsPGroup 3 U) :
    TernaryQuotientCharacterEnvelope U 0 1 := by
  intro Q _ _ q hq b J
  have hUcard : Nat.card U = 3 :=
    transitiveThreePoint_threePGroup_card hDegree hU
  letI : Fact (Nat.card U).Prime := ⟨by rw [hUcard]; norm_num⟩
  rcases q.ker.eq_bot_or_eq_top_of_prime_card with hker | hker
  · have hqi : Function.Injective q := (MonoidHom.ker_eq_bot_iff q).mp hker
    let eUQ : U ≃* Q := MulEquiv.ofBijective q ⟨hqi, hq⟩
    have hQcard : Nat.card Q = 3 := by
      calc
        Nat.card Q = Nat.card U := Nat.card_congr eUQ.symm.toEquiv
        _ = 3 := hUcard
    let eQ : Q ≃* Multiplicative (ZMod 3) :=
      mulEquivOfPrimeCardEq hQcard (by
        simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative,
          ZMod.card])
    have hcount := groupEpimorphism_card_le_elementary 3 (G := J) eQ
    have hcountR : (Nat.card (GroupEpimorphism J Q) : ℝ) ≤
        (3 : ℝ) ^ (Module.finrank (ZMod 3) (PrimeCharacters 3 J) *
          Module.finrank (ZMod 3) (ZMod 3)) := by
      exact_mod_cast hcount
    rw [← Real.rpow_natCast] at hcountR
    simpa only [Module.finrank_self, mul_one, Nat.cast_zero, zero_mul,
      add_zero, one_mul] using hcountR
  · have hqone : q = 1 := MonoidHom.ker_eq_top_iff.mp hker
    have hQ : Subsingleton Q := by
      constructor
      intro y z
      obtain ⟨u, rfl⟩ := hq y
      obtain ⟨v, rfl⟩ := hq z
      simp only [hqone, MonoidHom.one_apply]
    letI : Subsingleton Q := hQ
    have hEpi : Nat.card (GroupEpimorphism J Q) = 1 := by
      letI : Subsingleton (GroupEpimorphism J Q) :=
        ⟨fun f g => Subtype.ext (MonoidHom.ext fun _ => Subsingleton.elim _ _)⟩
      have hnonempty : Nonempty (GroupEpimorphism J Q) :=
        ⟨⟨1, fun y => ⟨1, Subsingleton.elim _ _⟩⟩⟩
      exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, hnonempty⟩
    rw [hEpi]
    simp only [Nat.cast_one, zero_mul, add_zero, one_mul]
    exact Real.one_le_rpow (by norm_num) (by positivity)

/-- One block layer adds exactly `s/9` to the character-sensitive exponent,
where `s` is the number of blocks.  Every original normal axis is retained;
only the finite sum of its target-local constants is taken at the end. -/
theorem ternaryQuotientCharacterEnvelope_blockStep
    {X : Type} [Finite X]
    {U : Subgroup (Equiv.Perm X)} [MulAction.IsPretransitive U X] {x : X}
    (D : TransitiveThreeBlockCover U x) (hU : IsPGroup 3 U)
    [Nontrivial D.Points]
    {offset constant : ℝ} (hconstant : 0 ≤ constant)
    (hTop : TernaryQuotientCharacterEnvelope D.Top offset constant) :
    TernaryQuotientCharacterEnvelope U
      (offset + (Nat.card D.Points : ℝ) / 9)
      (constant * ternaryBlockAggregateConstant D hU) := by
  intro Q _ _ q hq b J
  let N : {N : Subgroup U // N.Normal} := ⟨q.ker, inferInstance⟩
  letI : N.1.Normal := N.2
  letI : Finite (D.sectionRepresentation hU N.1) :=
    Finite.of_surjective
      ((D.originalKernelChart hU).normalSpace D.topMap.rangeRestrict
        (D.kernelModule hU) N.1).mkQ
      ((D.originalKernelChart hU).normalSpace D.topMap.rangeRestrict
        (D.kernelModule hU) N.1).mkQ_surjective
  have hquot := D.quotient_epimorphism_card_le_top_mul_schur hU N.1 J
  have htop := hTop (D.sectionTopQuotient N.1)
    (D.sectionTopQuotient_surjective N.1) b J
  have htransport : Nat.card (GroupEpimorphism J (U ⧸ N.1)) =
      Nat.card (GroupEpimorphism J Q) :=
    fusionGroupEpimorphism_card_congr (MulEquiv.refl J)
      (QuotientGroup.quotientKerEquivOfSurjective q hq)
  have hsection : ternaryBlockSectionConstant D hU N ≤
      ternaryBlockAggregateConstant D hU :=
    ternaryBlockSectionConstant_le_aggregate D hU N
  have hsection_nonneg : 0 ≤ ternaryBlockSectionConstant D hU N :=
    ternaryBlockSectionConstant_nonneg D hU N
  rw [← htransport]
  calc
    (Nat.card (GroupEpimorphism J (U ⧸ N.1)) : ℝ) ≤
        Nat.card (GroupEpimorphism J (U ⧸ (D.TopKernel ⊔ N.1))) *
          (ternaryBlockSectionConstant D hU N *
            (3 : ℝ) ^ (((Nat.card D.Points : ℝ) / 3) * ((b : ℝ) / 3))) := by
      simpa only [ternaryBlockSectionConstant, mul_assoc] using hquot
    _ ≤ (constant * (3 : ℝ) ^
          ((Module.finrank (ZMod 3) (PrimeCharacters 3 J) : ℝ) +
            offset * b)) *
          (ternaryBlockSectionConstant D hU N *
            (3 : ℝ) ^ (((Nat.card D.Points : ℝ) / 3) * ((b : ℝ) / 3))) := by
      gcongr
    _ = (constant * ternaryBlockSectionConstant D hU N) *
        ((3 : ℝ) ^
          ((Module.finrank (ZMod 3) (PrimeCharacters 3 J) : ℝ) +
            offset * b) *
        (3 : ℝ) ^ (((Nat.card D.Points : ℝ) / 3) * ((b : ℝ) / 3))) := by
      ring
    _ = (constant * ternaryBlockSectionConstant D hU N) *
        (3 : ℝ) ^
          ((Module.finrank (ZMod 3) (PrimeCharacters 3 J) : ℝ) +
            (offset + (Nat.card D.Points : ℝ) / 9) * b) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 1
      ring_nf
    _ ≤ (constant * ternaryBlockAggregateConstant D hU) *
        (3 : ℝ) ^
          ((Module.finrank (ZMod 3) (PrimeCharacters 3 J) : ℝ) +
            (offset + (Nat.card D.Points : ℝ) / 9) * b) := by
      gcongr

/-- The unrestricted degree-nine quotient row keeps one source-character
term and pays `b/3` for its single non-base block layer. -/
theorem degreeNine_quotientCharacterEnvelope
    {X : Type} [Finite X]
    (U : Subgroup (Equiv.Perm X)) [MulAction.IsPretransitive U X]
    (hDegree : Nat.card X = 9) (hU : IsPGroup 3 U) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      TernaryQuotientCharacterEnvelope U (1 / 3 : ℝ) constant := by
  letI : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let x : X := Classical.choice (inferInstance : Nonempty X)
  obtain ⟨D⟩ := transitiveThreeBlockCover_nonempty U hU x
  letI : Finite D.Top := D.top_finite
  letI : MulAction.IsPretransitive D.Top D.Points := D.top_pretransitive
  have hPoints : Nat.card D.Points = 3 := by
    have h := D.degree_product
    omega
  letI : Nontrivial D.Points :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hPoints]; norm_num)
  have hTop : TernaryQuotientCharacterEnvelope D.Top 0 1 :=
    degreeThree_quotientCharacterEnvelope D.Top hPoints (D.top_isPGroup hU)
  have hstep : TernaryQuotientCharacterEnvelope U
      (0 + (Nat.card D.Points : ℝ) / 9)
      (1 * ternaryBlockAggregateConstant D hU) :=
    ternaryQuotientCharacterEnvelope_blockStep
      D hU (offset := 0) (constant := 1) (by norm_num) hTop
  refine ⟨ternaryBlockAggregateConstant D hU,
    ternaryBlockAggregateConstant_nonneg D hU, ?_⟩
  have hoffset : (1 / 3 : ℝ) =
      0 + (Nat.card D.Points : ℝ) / 9 := by
    rw [hPoints]
    norm_num
  rw [hoffset]
  intro Q _ _ q hq b J
  simpa only [one_mul] using hstep (Q := Q) q hq b J

/-- The unrestricted degree-twenty-seven row recurses through the generic
degree-nine row.  Its exponent is `d₃(J) + 4b/3`; no marked width-nine
source hypothesis is imported into this step. -/
theorem degreeTwentySeven_quotientCharacterEnvelope
    {X : Type} [Finite X]
    (U : Subgroup (Equiv.Perm X)) [MulAction.IsPretransitive U X]
    (hDegree : Nat.card X = 27) (hU : IsPGroup 3 U) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      TernaryQuotientCharacterEnvelope U (4 / 3 : ℝ) constant := by
  letI : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let x : X := Classical.choice (inferInstance : Nonempty X)
  obtain ⟨D⟩ := transitiveThreeBlockCover_nonempty U hU x
  letI : Finite D.Top := D.top_finite
  letI : MulAction.IsPretransitive D.Top D.Points := D.top_pretransitive
  have hPoints : Nat.card D.Points = 9 := by
    have h := D.degree_product
    omega
  letI : Nontrivial D.Points :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hPoints]; norm_num)
  obtain ⟨topConstant, htopConstant, hTop⟩ :=
    degreeNine_quotientCharacterEnvelope D.Top hPoints (D.top_isPGroup hU)
  have hstep : TernaryQuotientCharacterEnvelope U
      ((1 / 3 : ℝ) + (Nat.card D.Points : ℝ) / 9)
      (topConstant * ternaryBlockAggregateConstant D hU) :=
    ternaryQuotientCharacterEnvelope_blockStep
      D hU htopConstant hTop
  refine ⟨topConstant * ternaryBlockAggregateConstant D hU,
    mul_nonneg htopConstant (ternaryBlockAggregateConstant_nonneg D hU), ?_⟩
  have hoffset : (4 / 3 : ℝ) =
      (1 / 3 : ℝ) + (Nat.card D.Points : ℝ) / 9 := by
    rw [hPoints]
    norm_num
  rw [hoffset]
  intro Q _ _ q hq b J
  exact hstep (Q := Q) q hq b J

/-- The unrestricted degree-nine recurrence has binary slope `16/15`.
This is the generic internal row used by degree twenty seven; it is not the
marked physical degree-nine owner. -/
theorem degreeNine_quotientEpimorphism_le_binary
    {X : Type} [Finite X]
    (U : Subgroup (Equiv.Perm X)) [MulAction.IsPretransitive U X]
    (hDegree : Nat.card X = 9) (hU : IsPGroup 3 U) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ {Q : Type} [Group Q] [Finite Q]
        (q : U →* Q), Function.Surjective q →
        ∀ (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))),
          (Nat.card (GroupEpimorphism J Q) : ℝ) ≤
            constant * (2 : ℝ) ^ (((16 : ℝ) / 15) * b) := by
  obtain ⟨constant, hconstant, hEnvelope⟩ :=
    degreeNine_quotientCharacterEnvelope U hDegree hU
  refine ⟨constant, hconstant, ?_⟩
  intro Q _ _ q hq b J
  let d := Module.finrank (ZMod 3) (PrimeCharacters 3 J)
  have hrank := permutation_ternaryCharacterRank_le_third J (Fin b)
  simp only [Nat.card_fin] at hrank
  have hthree : 3 * d ≤ b := by
    dsimp only [d]
    omega
  have hthreeR : (3 : ℝ) * (d : ℝ) ≤ (b : ℝ) := by
    exact_mod_cast hthree
  have hexponent : (d : ℝ) + (1 / 3 : ℝ) * b ≤
      (2 / 3 : ℝ) * b := by
    linarith
  calc
    (Nat.card (GroupEpimorphism J Q) : ℝ) ≤
        constant * (3 : ℝ) ^ ((d : ℝ) + (1 / 3 : ℝ) * b) :=
      hEnvelope q hq b J
    _ ≤ constant * (3 : ℝ) ^ ((2 / 3 : ℝ) * b) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent) hconstant
    _ ≤ constant * (2 : ℝ) ^
        ((8 / 5 : ℝ) * ((2 / 3 : ℝ) * b)) :=
      mul_le_mul_of_nonneg_left
        (c1_ternary_rpow_envelope (by positivity)) hconstant
    _ = constant * (2 : ℝ) ^ (((16 : ℝ) / 15) * b) := by
      congr 2
      ring

/-- The source-pattern improvement is retained as a hypothesis.  With one
regular `C3` orbit and no natural `A4` orbit, every quotient target of the
same degree-nine ternary action has the physical binary slope `8/9`. -/
theorem degreeNine_marked_quotientEpimorphism_le_binary
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    {X : Type} [Finite X]
    (U : Subgroup (Equiv.Perm X)) [MulAction.IsPretransitive U X]
    (hDegree : Nat.card X = 9) (hU : IsPGroup 3 U) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ {Q : Type} [Group Q] [Finite Q]
        (q : U →* Q), Function.Surjective q →
        ∀ (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))),
          C1DegreeNineSourcePattern J →
          (Nat.card (GroupEpimorphism J Q) : ℝ) ≤
            constant * (2 : ℝ) ^ (((8 : ℝ) / 9) * b) := by
  obtain ⟨constant, hconstant, hEnvelope⟩ :=
    degreeNine_quotientCharacterEnvelope U hDegree hU
  refine ⟨3 * constant, by positivity, ?_⟩
  intro Q _ _ q hq b J hsource
  let d := Module.finrank (ZMod 3) (PrimeCharacters 3 J)
  have hbudget : 9 * d ≤ 2 * b + 3 := by
    exact c1DegreeNineSource_ternaryCharacterRank
      hChief hPrimitive h18 J hsource
  have hbudgetR : (9 : ℝ) * (d : ℝ) ≤ 2 * (b : ℝ) + 3 := by
    exact_mod_cast hbudget
  have hexponent : (d : ℝ) + (1 / 3 : ℝ) * b ≤
      1 + (5 / 9 : ℝ) * b := by
    linarith
  calc
    (Nat.card (GroupEpimorphism J Q) : ℝ) ≤
        constant * (3 : ℝ) ^ ((d : ℝ) + (1 / 3 : ℝ) * b) :=
      hEnvelope q hq b J
    _ ≤ constant * (3 : ℝ) ^ (1 + (5 / 9 : ℝ) * b) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent) hconstant
    _ = (3 * constant) * (3 : ℝ) ^ ((5 / 9 : ℝ) * b) := by
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      norm_num
      ring
    _ ≤ (3 * constant) * (2 : ℝ) ^
        ((8 / 5 : ℝ) * ((5 / 9 : ℝ) * b)) :=
      mul_le_mul_of_nonneg_left
        (c1_ternary_rpow_envelope (by positivity)) (by positivity)
    _ = (3 * constant) * (2 : ℝ) ^ (((8 : ℝ) / 9) * b) := by
      congr 2
      ring

/-- The unrestricted degree-twenty-seven quotient row has binary slope
`8/3`, obtained only after the generic degree-nine recursion has been
completed. -/
theorem degreeTwentySeven_quotientEpimorphism_le_binary
    {X : Type} [Finite X]
    (U : Subgroup (Equiv.Perm X)) [MulAction.IsPretransitive U X]
    (hDegree : Nat.card X = 27) (hU : IsPGroup 3 U) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ {Q : Type} [Group Q] [Finite Q]
        (q : U →* Q), Function.Surjective q →
        ∀ (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))),
          (Nat.card (GroupEpimorphism J Q) : ℝ) ≤
            constant * (2 : ℝ) ^ (((8 : ℝ) / 3) * b) := by
  obtain ⟨constant, hconstant, hEnvelope⟩ :=
    degreeTwentySeven_quotientCharacterEnvelope U hDegree hU
  refine ⟨constant, hconstant, ?_⟩
  intro Q _ _ q hq b J
  let d := Module.finrank (ZMod 3) (PrimeCharacters 3 J)
  have hrank := permutation_ternaryCharacterRank_le_third J (Fin b)
  simp only [Nat.card_fin] at hrank
  have hthree : 3 * d ≤ b := by
    dsimp only [d]
    omega
  have hthreeR : (3 : ℝ) * (d : ℝ) ≤ (b : ℝ) := by
    exact_mod_cast hthree
  have hexponent : (d : ℝ) + (4 / 3 : ℝ) * b ≤
      (5 / 3 : ℝ) * b := by
    linarith
  calc
    (Nat.card (GroupEpimorphism J Q) : ℝ) ≤
        constant * (3 : ℝ) ^ ((d : ℝ) + (4 / 3 : ℝ) * b) :=
      hEnvelope q hq b J
    _ ≤ constant * (3 : ℝ) ^ ((5 / 3 : ℝ) * b) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent) hconstant
    _ ≤ constant * (2 : ℝ) ^
        ((8 / 5 : ℝ) * ((5 / 3 : ℝ) * b)) :=
      mul_le_mul_of_nonneg_left
        (c1_ternary_rpow_envelope (by positivity)) hconstant
    _ = constant * (2 : ℝ) ^ (((8 : ℝ) / 3) * b) := by
      congr 2
      ring

end SymmetricSubgroupAsymptotics

end
