import SymmetricSubgroupAsymptotics.C1DegreeNineTopMass
import SymmetricSubgroupAsymptotics.TernaryThreeGroupRankBudgetOwner
import SymmetricSubgroupAsymptotics.OriginalKernelLabelRegularEmbedding
import SymmetricSubgroupAsymptotics.DegreeTwelveKleinCoordinates

/-!
# The binary-nine owner with both structural inputs discharged

The binary-nine physical row needs two structural inputs on every original
normal axis.  This file supplies both without a finite catalogue.

* The acting quotient `G/base` is a transitive ternary group on its nine
  literal translation labels.  The degree-nine ternary quotient recursion
  therefore bounds the onto maps to every actual quotient
  `G/(base ⊔ N)` on a source with the exact rank budget.  This replaces the
  target-chart alternative of `C1DegreeNineTopMass`.
* Labelled binary coordinates embed every original-normal binary section in
  the regular module of its literal top.  For the saturated four-by-three
  minimal block system these coordinates are the Klein characters of the
  three literal block coordinates.

The row retains every literal normal axis, the original normalizer and the
complete source subgroup.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

namespace C1BinaryNineTopOwnerWitness

variable {G Ω : Type} [Group G] [MulAction G Ω]
    (W : C1BinaryNineTopOwnerWitness G Ω)

attribute [local instance] baseCommGroup baseVectorModule

theorem label_finite : Finite W.Label :=
  Nat.finite_of_card_ne_zero (by rw [W.label_card]; norm_num)

theorem label_nonempty : Nonempty W.Label := by
  have h : 0 < Nat.card W.Label := by rw [W.label_card]; norm_num
  exact (Nat.card_pos_iff.mp h).1

theorem top_card_odd [Finite G] : Odd (Nat.card (G ⧸ W.base)) := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card.mp W.quotient_three_group)
  rw [hk]
  exact Odd.pow (by decide)

/-- Labelled binary coordinates give the regular section embedding on every
original normal axis. -/
theorem axis_regular_embedding_of_labels [Finite G]
    (κ : Additive W.base →+ (W.Label → ZMod 2))
    (hκ : Function.Injective κ)
    (hequiv : ∀ (g : G) (k : W.base) (s : W.Label),
      κ (Additive.ofMul (MulAut.conjNormal g k)) (W.action (W.projection g) s) =
        κ (Additive.ofMul k) s)
    (N : Subgroup G) [N.Normal] :
    ∃ F : (W.axisRepresentation N).ρ.IntertwiningMap
      (Representation.leftRegular (ZMod 2) (G ⧸ (W.projection.ker ⊔ N))),
      Function.Injective F := by
  letI := W.label_finite
  obtain ⟨s₀⟩ := W.label_nonempty
  let κ' : W.baseRepresentation →ₗ[ZMod 2] (W.Label → ZMod 2) :=
    κ.toZModLinearMap 2
  apply OriginalKernelModuleChart.section_regular_embedding_of_labels
    W.projection W.baseRepresentation W.originalKernelChart N
    W.projection_surjective W.top_card_odd W.action W.action_transitive κ' hκ _ s₀
  intro q v s
  obtain ⟨g, rfl⟩ := W.projection_surjective q
  obtain ⟨k, rfl⟩ : ∃ k : W.base, Additive.ofMul k = v := ⟨v.toMul, rfl⟩
  change κ (W.baseRepresentation.ρ (W.projection g) (Additive.ofMul k))
      (W.action (W.projection g) s) = κ (Additive.ofMul k) s
  rw [W.baseRepresentation_apply]
  exact hequiv g k s

/-- The acting quotient, viewed as its faithful image on the nine labels. -/
abbrev labelImage : Subgroup (Equiv.Perm W.Label) := W.action.range

def labelImageEquiv : (G ⧸ W.base) ≃* W.labelImage :=
  MonoidHom.ofInjective W.action_injective

instance labelImage_pretransitive : MulAction.IsPretransitive W.labelImage W.Label where
  exists_smul_eq s t := by
    obtain ⟨q, hq⟩ := W.action_transitive s t
    exact ⟨⟨W.action q, q, rfl⟩, hq⟩

theorem labelImage_isPGroup : IsPGroup 3 W.labelImage :=
  W.quotient_three_group.of_equiv W.labelImageEquiv

/-- The literal quotient top on every original normal axis, from the faithful
label image. -/
def labelAxisTop (N : Subgroup G) [N.Normal] :
    W.labelImage →* G ⧸ (W.projection.ker ⊔ N) :=
  (W.axisWholeTopMap N).comp W.labelImageEquiv.symm.toMonoidHom

theorem labelAxisTop_surjective (N : Subgroup G) [N.Normal] :
    Function.Surjective (W.labelAxisTop N) :=
  (W.axisWholeTopMap_surjective N).comp W.labelImageEquiv.symm.surjective

end C1BinaryNineTopOwnerWitness

/-- The binary-nine physical row with a constant independent of the source
degree.  The source pattern is required only on complete sources whose
surviving onto maps are accepted by the local predicate. -/
theorem C1BinaryNineTopOwnerWitness.physical_owner_bound_ternaryTop
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
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
  have hbudget := hJ.rankBudget hChief hPrimitive h18 J
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

namespace OriginalMinimalBlock

variable {A Ω : Type} [Group A] [Finite A] [Finite Ω] [MulAction A Ω]
    [FaithfulSMul A Ω] [MulAction.IsPretransitive A Ω]
    {ω₀ : Ω} (D : OriginalMinimalBlock (A := A) ω₀)

/-- The saturated four-by-three binary-nine owner has the regular section
embedding on every original normal axis, from its literal Klein block
coordinates. -/
theorem fourByThree_nineTopOwnerWitness_regular
    (N : Subgroup A) [N.Normal] (c : ActualChiefSeries D.Component)
    (hPoints : Nat.card D.Points = 3) (hTopOrder : Nat.card D.Top = 3)
    (hWeight : actualChiefSeriesTernaryWeight c = 1)
    (hTop : Module.finrank (ZMod 3)
      (primeRelativeCharacters 3 (originalNormalRange D.topMap N)) = 1)
    (hRank : Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) = 2)
    (e : ∀ x : D.Points, Fin 4 ≃ originalBlockFibre D.map x)
    (M : Subgroup A) [M.Normal] :
    let W := D.fourByThree_nineTopOwnerWitness N c hPoints hTopOrder hWeight hTop hRank e
    ∃ F : (W.axisRepresentation M).ρ.IntertwiningMap
      (Representation.leftRegular (ZMod 2) (A ⧸ (W.projection.ker ⊔ M))),
      Function.Injective F := by
  intro W
  let hEven := D.fourByThree_allEven N c hPoints hTopOrder hWeight hTop hRank e
  let κ : Additive W.base →+ (W.Label → ZMod 2) :=
    DegreeTwelveNineTranslations.kleinCoordinates D.map D.map_equivariant e hEven
  apply W.axis_regular_embedding_of_labels κ
    (DegreeTwelveNineTranslations.kleinCoordinates_injective D.map D.map_equivariant e hEven)
  intro g k s
  exact DegreeTwelveNineTranslations.kleinCoordinates_conjugation
    D.map D.map_equivariant e hEven g k s

end OriginalMinimalBlock

end SymmetricSubgroupAsymptotics

end
