import SymmetricSubgroupAsymptotics.CFSGSufficientTernaryStability
import SymmetricSubgroupAsymptotics.C1DegreeNineSourceRankWithoutCatalogue
import SymmetricSubgroupAsymptotics.C1DegreeNineRankBudgetWithoutCatalogue
import SymmetricSubgroupAsymptotics.C1BinaryNineRegularTopWithoutCatalogue
import SymmetricSubgroupAsymptotics.C1DegreeNinePatternDeletionWithoutCatalogue
import SymmetricSubgroupAsymptotics.C3C1PatternAlignedCoverageWithoutCatalogue

/-! Proof-only sufficient-index forwarding on the unchanged actual source
families. All original normal subgroups, complement actions, numerical
rows and rank predicates are retained; no sharp universal hSI is produced. -/

/-! The original orbitwise source rank budgets tolerate head2 at degree10:
9*2≤2*10. No old strict-head premise is needed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics
/-- The local capacity behind the one-exceptional-orbit sum.  Degrees three
and four are resolved by their exact action classifications; degree nine
uses its sharp stability value two; all other degrees use the ordinary
stability envelope. -/
theorem c1DegreeNineSource_local_capacity_of_sufficient
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    {X : Type} [Finite X] (J : Subgroup (Equiv.Perm X))
    (exceptional : OrbitProfileFromOrbits.Orbit J)
    (hexceptional : IsRegularC3Orbit J exceptional)
    (hunique : ∀ o, IsRegularC3Orbit J o → o = exceptional)
    (hnoA4 : ∀ o, ¬ IsNaturalA4Action
      (OrbitProfileFromOrbits.orbitImage J o) o.orbit)
    (o : OrbitProfileFromOrbits.Orbit J)
    (N : Subgroup (OrbitProfileFromOrbits.orbitImage J o)) (hN : N.Normal) :
    letI := hN
    9 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) ≤
      2 * Nat.card o.orbit + if o = exceptional then 3 else 0 := by
  let A := OrbitProfileFromOrbits.orbitImage J o
  let w := Nat.card o.orbit
  let d := Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)
  letI : MulAction.IsPretransitive A o.orbit := orbitImage_pretransitive J o
  letI : Nonempty o.orbit := ⟨⟨o.out, by
    rw [o.orbit_eq_orbit_out Quotient.out_eq']
    exact MulAction.mem_orbit_self o.out⟩⟩
  letI : N.Normal := hN
  have hrel : d≤ternaryRelaxedStabilityBound w := by
    exact transitiveTernaryHead_relaxed_stability_of_sufficient
      hChief hgen hindex published8 h18 N
  by_cases h10 : w=10
  · have hd : d≤2 := by simpa only [h10,ternaryRelaxedStabilityBound] using hrel
    omega
  have hstable : d≤ternaryStabilityBound w := by
    simpa only [ternaryRelaxedStabilityBound,if_neg h10] using hrel
  by_cases h3 : w = 3
  · have hd : d ≤ 1 := by
      simpa only [w, h3, ternaryStabilityBound_three] using hstable
    by_cases hd0 : d = 0
    · simp only [d, hd0]
      omega
    · have hd1 : d = 1 := by omega
      have hgroup : IsPGroup 3 A :=
        degreeThree_rankOne_isPGroup h3 N hd1
      have hoe : o = exceptional := hunique o ⟨h3, hgroup⟩
      have hcard : Nat.card exceptional.orbit = 3 := by
        rw [← hoe]
        exact h3
      simp only [d, hd1, hoe, ↓reduceIte]
      omega
  by_cases h4 : w = 4
  · have hd : d ≤ 1 := by
      simpa only [w, h4, ternaryStabilityBound_four] using hstable
    have hd0 : d = 0 := by
      by_contra hd0
      have hd1 : d = 1 := by omega
      exact hnoA4 o (degreeFour_rankOne_isNaturalA4 h4 N hd1)
    simp only [d, hd0]
    omega
  by_cases h9 : w = 9
  · have hd : d ≤ 2 := by
      simpa only [w, h9, ternaryStabilityBound_nine] using hstable
    omega
  · have hord : d ≤ 5 * w / 27 :=
      hstable.trans (ternaryStability_le_base w h3 h4 h9)
    have hmul : 27 * d ≤ 5 * w :=
      by simpa only [Nat.mul_comm] using
        (Nat.le_div_iff_mul_le (by decide : 0 < 27)).mp hord
    omega

/-- The exact source-pattern rank budget used by every quotient target of
the mixed degree-nine top. -/
theorem c1DegreeNineSource_ternaryCharacterRank_of_sufficient
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b)))
    (hsource : C1DegreeNineSourcePattern J) :
    9 * Module.finrank (ZMod 3) (PrimeCharacters 3 J) ≤ 2 * b + 3 := by
  obtain ⟨exceptional, hexceptional, hunique, hnoA4⟩ := hsource
  simpa only [Nat.card_fin] using
    ternaryCharacterRank_oneExceptionalOrbit J exceptional
      (c1DegreeNineSource_local_capacity_of_sufficient hChief hgen hindex published8 h18 J exceptional
        hexceptional hunique hnoA4)

end SymmetricSubgroupAsymptotics

end


/-! Install the proved orbitwise rank capacity on the unchanged source pattern. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics
/-- The one-regular-`C3`, no-natural-`A4` pattern proves the retained
numerical source budget. -/
theorem C1DegreeNineSourcePattern.rankBudget_of_sufficient
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    {X : Type} [Fintype X] (J : Subgroup (Equiv.Perm X))
    (h : C1DegreeNineSourcePattern J) :
    C1DegreeNineRankBudget J := by
  unfold C1DegreeNineRankBudget
  obtain ⟨exceptional, hexceptional, hunique, hnoA4⟩ := h
  exact ternaryCharacterRank_oneExceptionalOrbit J exceptional
    (c1DegreeNineSource_local_capacity_of_sufficient hChief hgen hindex published8 h18 J exceptional
      hexceptional hunique hnoA4)

end SymmetricSubgroupAsymptotics


/-! Preserve the complete original-normal mixed binary-nine physical row;
only its exact source rank-budget producer is replaced by a proved theorem. -/
set_option autoImplicit false
noncomputable section
attribute [-instance] SymmetricSubgroupAsymptotics.originalNormalFintype
open Filter
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics
/-- The binary-nine physical row with a constant independent of the source
degree.  The source pattern is required only on complete sources whose
surviving onto maps are accepted by the local predicate. -/
theorem C1BinaryNineTopOwnerWitness.physical_owner_bound_ternaryTop_of_sufficient
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    (U : Subgroup (Equiv.Perm (Fin 12)))
    (W : C1BinaryNineTopOwnerWitness U (Fin 12))
    (hregular : ∀ N : {N : Subgroup U // N.Normal},
      ∃ F : (W.originalKernelChart.sectionRepresentation
          W.projection W.baseRepresentation N.1).ρ.IntertwiningMap
        (Representation.leftRegular (ZMod 2)
          (U ⧸ (W.projection.ker ⊔ N.1))), Function.Injective F) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (b : ℕ) (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop),
      FusionOrbitNatural U P →
      (∀ (N : {N : Subgroup U // N.Normal})
        (J : Subgroup (Equiv.Perm (Fin b))) (β : GroupEpimorphism J (U ⧸ N.1)),
        P (fusionFullGoursatEncode N J β).1 → C1DegreeNineSourcePattern J) →
      (Nat.card (FusionOrbitFamily U (FusionAcceptedOrbitPredicate U P)) : ℝ) /
          exactBenchmark (b + 12) ≤
        c1EarlierKernel b .degreeTwelveMixed D
          (Nat.card (Subgroup.normalizer (U : Set (Equiv.Perm (Fin 12)))) : ℝ) *
          ((subgroupCount b : ℝ) / exactBenchmark b) := by
  letI := W.label_finite
  obtain ⟨C, hC, hEpi⟩ := degreeNine_rankBudget_quotientEpimorphism_le_binary
    W.labelImage W.label_card W.labelImage_isPGroup
  refine ⟨∑ N : {N : Subgroup U // N.Normal},
      (originalNormalRegularConstant 2 W.projection W.baseRepresentation
        W.originalKernelChart N : ℝ) * C,
    Finset.sum_nonneg (fun N _ => mul_nonneg (Nat.cast_nonneg _) hC), ?_⟩
  intro b P hP hSource
  letI : Finite ↥W.baseRepresentation := by
    change Finite W.BaseVector
    infer_instance
  apply c1EarlierPhysical_regular_owner_bound_of_source (p := 2)
    .degreeTwelveMixed U W.projection W.baseRepresentation W.originalKernelChart
    hregular b P hP C1DegreeNineSourcePattern hSource (fun _ => C) (fun _ => hC)
  intro J hJ N
  letI : N.1.Normal := N.2
  have hbudget := hJ.rankBudget_of_sufficient hChief hgen hindex published8 h18 J
  have htop : (Nat.card (GroupEpimorphism J (U ⧸ (W.projection.ker ⊔ N.1))) : ℝ) ≤
      C * (2 : ℝ) ^ (((8 : ℝ) / 9) * b) :=
    hEpi (W.labelAxisTop N.1) (W.labelAxisTop_surjective N.1) b J hbudget
  have hmass : (regularTopCharacterMass 2 J (U ⧸ (W.projection.ker ⊔ N.1)) : ℝ) ≤
      (Nat.card (GroupEpimorphism J (U ⧸ (W.projection.ker ⊔ N.1))) : ℝ) *
        (2 : ℝ) ^ (b / 2) := by
    exact_mod_cast regularTopCharacterMass_le_of_rank 2 (J := J)
      (B := U ⧸ (W.projection.ker ⊔ N.1)) (b / 2) (fun β => by
        have h := epimorphismKernel_binaryCharacterRank_le_half J β.1
        simpa only [Nat.card_fin] using h)
  calc
    (regularTopCharacterMass 2 J (U ⧸ (W.projection.ker ⊔ N.1)) : ℝ) ≤
        (Nat.card (GroupEpimorphism J (U ⧸ (W.projection.ker ⊔ N.1))) : ℝ) *
          (2 : ℝ) ^ (b / 2) := hmass
    _ ≤ (C * (2 : ℝ) ^ (((8 : ℝ) / 9) * b)) * (2 : ℝ) ^ (((1 : ℝ) / 2) * b) :=
      mul_le_mul htop (binaryKernelPower_le_half b) (by positivity)
        (mul_nonneg hC (by positivity))
    _ = C * (2 : ℝ) ^ (((25 : ℝ) / 18) * b) := by
      rw [mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 2
      ring
    _ ≤ C * ((b : ℝ) + 1) * (2 : ℝ) ^ (c1EarlierExponent .degreeTwelveMixed * b) := by
      simp only [c1EarlierExponent]
      have hp : (0 : ℝ) ≤ (2 : ℝ) ^ (((25 : ℝ) / 18) * b) := by positivity
      nlinarith [mul_nonneg hC hp, (Nat.cast_nonneg b : (0 : ℝ) ≤ b)]

end SymmetricSubgroupAsymptotics


/-! Deleting the same actual nonmarker orbit preserves the same full source
pattern; install its newly proved rank budget without a strict-head premise. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics
open FusionOrbitProfileChart

/-- The numerical rank budget is the smaller invariant consequence needed
by the degree-nine ternary epimorphism row. -/
theorem C1DegreeNineSourcePattern.complementImage_rankBudget_of_sufficient
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    {X : Type} [Fintype X] {c : ℕ}
    (H : Subgroup (Equiv.Perm X))
    (selected : OrbitProfileFromOrbits.Orbit H)
    (eC : Fin c ≃ ↥((orbitSubaction H selected)ᶜ))
    (hpattern : C1DegreeNineSourcePattern H)
    (hselected : ¬ IsRegularC3Orbit H selected) :
    C1DegreeNineRankBudget (Complement.image H selected eC) :=
  (hpattern.complementImage H selected eC hselected).rankBudget_of_sufficient
    hChief hgen hindex published8 h18 (Complement.image H selected eC)

/-- In an exact selected-orbit chart, deleting a nonmarker orbit attaches the
degree-nine rank budget to the literal source projection of the actual fusion
model. -/
theorem C1DegreeNineSourcePattern.deletedModel_rankBudget_of_sufficient
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    {X : Type} [Fintype X] {w c : ℕ}
    (H : Subgroup (Equiv.Perm X))
    (selected : OrbitProfileFromOrbits.Orbit H)
    (U : Subgroup (Equiv.Perm (Fin w)))
    (eO : Fin w ≃ selected.orbit)
    (eC : Fin c ≃ ↥((orbitSubaction H selected)ᶜ))
    (himage : relabelSubgroup eO U =
      OrbitProfileFromOrbits.orbitImage H selected)
    (hpattern : C1DegreeNineSourcePattern H)
    (hselected : ¬ IsRegularC3Orbit H selected) :
    C1DegreeNineRankBudget
      ((fusionDeletedModel U
          (relabelSubgroup (chart H selected eO eC).symm H)).map
        (MonoidHom.snd U (Equiv.Perm (Fin c)))) := by
  rw [Complement.deletedSource_eq_image H selected eO eC U himage]
  exact hpattern.complementImage_rankBudget_of_sufficient hChief hgen hindex published8 h18
    H selected eC hselected

end SymmetricSubgroupAsymptotics

end


/-! The exact aligned nine-point source restriction uses the proved
unchanged rank budget on the same deleted model and complement. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics
namespace C3HighNestedCarrier

/-- The exact degree-nine chart inherits the source rank budget from the
complete one-C3 pattern. -/
theorem Data.degreeNine_deletedModel_rankBudget_of_sufficient
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    {b : ℕ}
    (H : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)))
    (C : Data H)
    (hw : Nat.card C.orbit.orbit = 9)
    (i : Non2TransitiveActionClass (Fin 9))
    (eO : Fin 9 ≃ C.orbit.orbit)
    (himage : relabelSubgroup eO i.representative =
      OrbitProfileFromOrbits.orbitImage (C3ComplementSource b H) C.orbit)
    (hpattern : C1DegreeNineSourcePattern (physicalSubgroup H)) :
    C1DegreeNineRankBudget
      ((fusionDeletedModel i.representative
          (relabelSubgroup (chart H C.orbit hw eO).symm
            (physicalSubgroup H))).map
        (MonoidHom.snd i.representative
          (Equiv.Perm (Fin (b + 3 - 9))))) := by
  have hselected : ¬ IsRegularC3Orbit
      (physicalSubgroup H) (liftedOrbit H C.orbit) := by
    intro hregular
    have hcard := hregular.1
    rw [liftedOrbit_card H C.orbit, hw] at hcard
    omega
  exact hpattern.deletedModel_rankBudget_of_sufficient hChief hgen hindex published8 h18
    (physicalSubgroup H) (liftedOrbit H C.orbit) i.representative
    (pointEquiv H C.orbit eO) (complementEquiv H C.orbit hw)
    (pointEquiv_image H C.orbit i.representative eO himage) hselected

/-- A degree-nine high-C3 chart from the exact c=1 family enters the aligned
first-owner cell with the source budget installed in its local predicate. -/
theorem Data.mem_non2FirstOwnerCanonicalFamily_forAction_rankBudget_of_sufficient
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    {r b : ℕ}
    (Eligible : ∀ n, Fin r → Subgroup (Equiv.Perm (Fin n)) → Prop)
    (hEligible : DegreeNaturalOwnerMenu Eligible)
    (H : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)))
    (C : Data H)
    (hw : Nat.card C.orbit.orbit = 9)
    (q : TernaryCyclic ⊕ Fin b ≃ Fin (b + 3))
    (hordinary : ¬ IsCriticalSubgroup (b + 3)
      (relabelSubgroup q (physicalSubgroup H)))
    (owner : Fin r)
    (howner : FirstOwned (Eligible (b + 3)) owner
      (relabelSubgroup q (physicalSubgroup H)))
    (i : Non2TransitiveActionClass (Fin 9))
    (eO : Fin 9 ≃ C.orbit.orbit)
    (himage : relabelSubgroup eO i.representative =
      OrbitProfileFromOrbits.orbitImage (C3ComplementSource b H) C.orbit)
    (hpattern : C1DegreeNineSourcePattern (physicalSubgroup H)) :
    relabelSubgroup q (physicalSubgroup H) ∈
      FusionWidthCanonicalFamily i.representative (by
        have hwb := width_le H C.orbit hw
        omega)
        (FusionSourceRestrictedPredicate i.representative
          (non2FirstOwnerPredicate Eligible 9 (owner, i) (b + 3 - 9))
          C1DegreeNineRankBudget) := by
  have hownerLocal :=
    C.deletedModel_non2FirstOwnerPredicate_forAction
      Eligible hEligible H hw q hordinary owner howner i eO himage
  have hbudget := C.degreeNine_deletedModel_rankBudget_of_sufficient
    hChief hgen hindex published8 h18 H hw i eO himage hpattern
  exact mem_widthCanonicalFamily_of_relabel H C hw i.representative
    eO himage q
    (FusionSourceRestrictedPredicate i.representative
      (non2FirstOwnerPredicate Eligible 9 (owner, i) (b + 3 - 9))
      C1DegreeNineRankBudget)
    ⟨hownerLocal, hbudget⟩

end C3HighNestedCarrier
end SymmetricSubgroupAsymptotics
