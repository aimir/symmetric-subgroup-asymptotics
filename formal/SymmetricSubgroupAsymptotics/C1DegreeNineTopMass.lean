import SymmetricSubgroupAsymptotics.C1DegreeNineSourceRank
import SymmetricSubgroupAsymptotics.C1BinaryNineTopOwner
import SymmetricSubgroupAsymptotics.C1OriginalNormalEpiSum
import SymmetricSubgroupAsymptotics.C3EpimorphismCharacters
import SymmetricSubgroupAsymptotics.CocycleGeneratorBound
import SymmetricSubgroupAsymptotics.PrimeElementaryEpimorphismBound
import SymmetricSubgroupAsymptotics.PermutationThreeGroupRank

/-!
# Character mass for the mixed degree-nine top

This is the numerical endpoint for a source with one regular `C3` orbit and
no natural `A4` orbit.  The actual target is allowed to be either elementary
ternary of rank at most two, or an arbitrary (possibly nonsplit) extension of
`C3` by a module embedded in one copy of the regular `F3[C3]` module.

The extension count retains the original quotient map and uses the complete
same-source lift fibre.  A deliberately harmless fixed factor bounds the
module and its first cohomology; it does not change the mixed exponent
`25/18`.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

/-- A checked elementary description of one actual quotient target. -/
structure DegreeNineElementaryTargetChart (Q : Type) [Group Q] where
  V : Type
  [addCommGroup : AddCommGroup V]
  [module : Module (ZMod 3) V]
  [finite : Finite V]
  equiv : Q ≃* Multiplicative V
  rank_le_two : Module.finrank (ZMod 3) V ≤ 2

attribute [instance] DegreeNineElementaryTargetChart.addCommGroup
  DegreeNineElementaryTargetChart.module DegreeNineElementaryTargetChart.finite

/-- A checked, possibly nonsplit, `C3`-by-regular-module description of one
actual quotient target.  The map and its literal kernel chart are retained. -/
structure DegreeNineRegularC3ExtensionChart (Q : Type) [Group Q] where
  projection : Q →* TernaryCyclic
  projection_surjective : Function.Surjective projection
  action : Rep (ZMod 3) TernaryCyclic
  [finite : Finite action]
  chart : OriginalKernelModuleChart projection action
  regularEmbedding : action.ρ.IntertwiningMap
    (Representation.leftRegular (ZMod 3) TernaryCyclic)
  regularEmbedding_injective : Function.Injective regularEmbedding

attribute [instance] DegreeNineRegularC3ExtensionChart.finite

/-- The two quotient types occurring in a transitive degree-nine ternary
top.  Establishing this alternative for the opaque nine-label owner is a
separate structural theorem. -/
def IsDegreeNineTopTarget (Q : Type) [Group Q] : Prop :=
  Nonempty (DegreeNineElementaryTargetChart Q) ∨
    Nonempty (DegreeNineRegularC3ExtensionChart Q)

private theorem ternaryGenerator_closure :
    Subgroup.closure (Set.range (fun _ : Fin 1 => ternaryGenerator)) =
      (⊤ : Subgroup TernaryCyclic) := by
  apply top_unique
  intro z _
  have hz : z ∈ Subgroup.zpowers ternaryGenerator := ternaryGenerator_generates z
  apply (Subgroup.zpowers_le_of_mem ?_) hz
  exact Subgroup.subset_closure ⟨0, rfl⟩

/-- Any module embedded in one regular `F3[C3]` has at most 27 elements. -/
theorem degreeNineRegularC3_module_card_le
    {Q : Type} [Group Q] (C : DegreeNineRegularC3ExtensionChart Q) :
    Nat.card C.action ≤ 27 := by
  calc
    Nat.card C.action ≤ Nat.card (TernaryCyclic →₀ ZMod 3) :=
      Nat.card_le_card_of_injective C.regularEmbedding
        C.regularEmbedding_injective
    _ = 27 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_finsupp]
      norm_num [TernaryCyclic]

/-- A one-generator bound is enough for the fixed first-cohomology factor;
the extension is not assumed to split. -/
theorem degreeNineRegularC3_H1_card_le
    {Q : Type} [Group Q] (C : DegreeNineRegularC3ExtensionChart Q) :
    Nat.card (groupCohomology.H1 C.action) ≤ 27 := by
  exact (firstCohomology_card_le_generator_power C.action 1
    (fun _ => ternaryGenerator) ternaryGenerator_closure).trans
      (by simpa only [pow_one] using degreeNineRegularC3_module_card_le C)

private def trueSubtypeEquiv (α : Type*) : α ≃ {x : α // True} where
  toFun x := ⟨x, trivial⟩
  invFun x := x.1
  left_inv _ := rfl
  right_inv x := Subtype.ext rfl

/-- Oriented epimorphisms to the literal `C3` target are bounded by all
ternary characters of the same complete source. -/
theorem ternaryEpimorphism_card_le_characters
    {J : Type} [Group J] [Finite J] :
    Nat.card (GroupEpimorphism J TernaryCyclic) ≤
      Nat.card (PrimeCharacters 3 J) := by
  rw [Nat.card_congr ternaryEpimorphismEquivNonzero]
  exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective

/-- The regular top-character mass over `C3`, using the actual kernels of
the actual oriented quotient maps. -/
theorem ternaryCyclic_regularTopCharacterMass_le
    (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))) :
    regularTopCharacterMass 3 J TernaryCyclic ≤
      3 ^ (Module.finrank (ZMod 3) (PrimeCharacters 3 J) + b / 3) := by
  let d := Module.finrank (ZMod 3) (PrimeCharacters 3 J)
  have hmass := regularTopCharacterMass_le_of_rank 3 (J := J)
    (B := TernaryCyclic) (b / 3) (fun β => by
      have h := groupEpimorphismKernel_three_mul_rank_le_degree J β
      omega)
  calc
    regularTopCharacterMass 3 J TernaryCyclic ≤
        Nat.card (GroupEpimorphism J TernaryCyclic) * 3 ^ (b / 3) := hmass
    _ ≤ Nat.card (PrimeCharacters 3 J) * 3 ^ (b / 3) :=
      Nat.mul_le_mul_right _ ternaryEpimorphism_card_le_characters
    _ = 3 ^ d * 3 ^ (b / 3) := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 3)
        (V := PrimeCharacters 3 J), Nat.card_zmod]
    _ = _ := by rw [← pow_add]

/-- Every epi to a possibly nonsplit `C3`-by-regular-module target is
counted through its original top map and original lift fibre. -/
theorem groupEpimorphism_card_le_degreeNineRegularC3
    {Q : Type} [Group Q] [Finite Q]
    (C : DegreeNineRegularC3ExtensionChart Q)
    (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))) :
    Nat.card (GroupEpimorphism J Q) ≤
      3 ^ (Module.finrank (ZMod 3) (PrimeCharacters 3 J) + b / 3 + 6) := by
  have hfibre := fusionEpimorphism_survival_card_le_regular 3
    C.projection C.projection_surjective C.action C.chart
    C.regularEmbedding C.regularEmbedding_injective
    (fun _ : GroupEpimorphism J Q => True)
  have hcard : Nat.card (GroupEpimorphism J Q) ≤
      (Nat.card C.action * Nat.card (groupCohomology.H1 C.action)) *
        regularTopCharacterMass 3 J TernaryCyclic := by
    rw [Nat.card_congr (trueSubtypeEquiv (GroupEpimorphism J Q))]
    exact hfibre
  have hfixed : Nat.card C.action *
      Nat.card (groupCohomology.H1 C.action) ≤ 3 ^ 6 := by
    calc
      _ ≤ 27 * 27 := Nat.mul_le_mul
        (degreeNineRegularC3_module_card_le C)
        (degreeNineRegularC3_H1_card_le C)
      _ = 3 ^ 6 := by norm_num
  have hmass := ternaryCyclic_regularTopCharacterMass_le b J
  calc
    _ ≤ (Nat.card C.action * Nat.card (groupCohomology.H1 C.action)) *
        regularTopCharacterMass 3 J TernaryCyclic := hcard
    _ ≤ 3 ^ 6 *
        3 ^ (Module.finrank (ZMod 3) (PrimeCharacters 3 J) + b / 3) :=
      Nat.mul_le_mul hfixed hmass
    _ = _ := by rw [← pow_add]; congr 1; omega

/-- Both actual degree-nine quotient types obey one uniform top-map bound.
The fixed `3^6` is only needed by the nonsplit extension alternative. -/
theorem groupEpimorphism_card_le_degreeNineTarget
    (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b)))
    {Q : Type} [Group Q] [Finite Q]
    (hTarget : IsDegreeNineTopTarget Q)
    (hbudget : 9 * Module.finrank (ZMod 3) (PrimeCharacters 3 J) ≤
      2 * b + 3) :
    Nat.card (GroupEpimorphism J Q) ≤
      3 ^ (Module.finrank (ZMod 3) (PrimeCharacters 3 J) + b / 3 + 6) := by
  rcases hTarget with hElementary | hRegular
  · obtain ⟨C⟩ := hElementary
    have h := groupEpimorphism_card_le_elementary_rank_two
      (p := 3) (G := J) (Q := Q) (V := C.V) C.equiv C.rank_le_two
    apply h.trans
    apply Nat.pow_le_pow_right (by decide : 0 < 3)
    have hdiv : 3 * (b / 3) ≤ b := by
      simpa only [mul_comm] using Nat.div_mul_le_self b 3
    omega
  · obtain ⟨C⟩ := hRegular
    exact groupEpimorphism_card_le_degreeNineRegularC3 C b J

/-- The ternary power supplied by the source budget fits the mixed-row
binary envelope.  Floors and the exceptional `+3` are absorbed by `3^7`. -/
theorem degreeNineSource_ternaryPower_le_mixed
    (b d : ℕ) (hbudget : 9 * d ≤ 2 * b + 3) :
    (3 : ℝ) ^ (d + b / 3 + 6) ≤
      2187 * (2 : ℝ) ^ (((8 : ℝ) / 9) * b) := by
  let e := d + b / 3 + 6
  have hdiv : 3 * (b / 3) ≤ b := by
    simpa only [mul_comm] using Nat.div_mul_le_self b 3
  have hen : 9 * e ≤ 5 * b + 57 := by
    dsimp only [e]
    omega
  have her : (e : ℝ) ≤ 7 + (5 / 9 : ℝ) * b := by
    have hen' : (9 : ℝ) * e ≤ 5 * b + 57 := by exact_mod_cast hen
    linarith
  calc
    (3 : ℝ) ^ e = (3 : ℝ) ^ (e : ℝ) := by
      rw [Real.rpow_natCast]
    _ ≤ (3 : ℝ) ^ (7 + (5 / 9 : ℝ) * b) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) her
    _ = 2187 * (3 : ℝ) ^ ((5 / 9 : ℝ) * b) := by
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      norm_num
    _ ≤ 2187 * (2 : ℝ) ^ ((8 / 5 : ℝ) * ((5 / 9 : ℝ) * b)) :=
      mul_le_mul_of_nonneg_left
        (c1_ternary_rpow_envelope (by positivity)) (by norm_num)
    _ = _ := by
      apply congrArg (fun x : ℝ => 2187 * (2 : ℝ) ^ x)
      ring

/-- The binary kernel character factor costs at most half the original
permutation degree. -/
theorem binaryKernelPower_le_half (b : ℕ) :
    (2 : ℝ) ^ (b / 2) ≤ (2 : ℝ) ^ (((1 : ℝ) / 2) * b) := by
  rw [← Real.rpow_natCast]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have h : 2 * (b / 2) ≤ b := by
    simpa only [mul_comm] using Nat.div_mul_le_self b 2
  have h' : (2 : ℝ) * ((b / 2 : ℕ) : ℝ) ≤ (b : ℝ) := by
    exact_mod_cast h
  linarith

/-- Full fixed-target binary character mass for every allowed actual
degree-nine quotient target. -/
theorem degreeNineTarget_regularTopCharacterMass_le
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b)))
    (hsource : C1DegreeNineSourcePattern J)
    {Q : Type} [Group Q] [Finite Q]
    (hTarget : IsDegreeNineTopTarget Q) :
    (regularTopCharacterMass 2 J Q : ℝ) ≤
      2187 * (2 : ℝ) ^ (((25 : ℝ) / 18) * b) := by
  let d := Module.finrank (ZMod 3) (PrimeCharacters 3 J)
  have hbudget : 9 * d ≤ 2 * b + 3 :=
    c1DegreeNineSource_ternaryCharacterRank hChief hPrimitive h18 J hsource
  have htop := groupEpimorphism_card_le_degreeNineTarget b J hTarget hbudget
  have hmass : (regularTopCharacterMass 2 J Q : ℝ) ≤
      (Nat.card (GroupEpimorphism J Q) : ℝ) * (2 : ℝ) ^ (b / 2) := by
    exact_mod_cast regularTopCharacterMass_le_of_rank 2 (J := J) (B := Q)
      (b / 2) (fun β => by
        have h := epimorphismKernel_binaryCharacterRank_le_half J β.1
        simpa only [Nat.card_fin] using h)
  have htop' : (Nat.card (GroupEpimorphism J Q) : ℝ) ≤
      (3 : ℝ) ^ (d + b / 3 + 6) := by exact_mod_cast htop
  calc
    _ ≤ (Nat.card (GroupEpimorphism J Q) : ℝ) * (2 : ℝ) ^ (b / 2) := hmass
    _ ≤ (3 : ℝ) ^ (d + b / 3 + 6) * (2 : ℝ) ^ (b / 2) :=
      mul_le_mul_of_nonneg_right htop' (by positivity)
    _ ≤ (2187 * (2 : ℝ) ^ (((8 : ℝ) / 9) * b)) *
        (2 : ℝ) ^ (((1 : ℝ) / 2) * b) :=
      mul_le_mul (degreeNineSource_ternaryPower_le_mixed b d hbudget)
        (binaryKernelPower_le_half b) (by positivity) (by positivity)
    _ = _ := by
      rw [mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 2
      ring

namespace C1BinaryNineTopOwnerWitness

/-- Install the source-restricted mixed numerical row in the original-normal
physical consumer.  The owner supplies every binary kernel chart.  The two
remaining structural inputs are stated visibly: regular embeddings of those
binary sections, and the degree-nine quotient alternative for every original
normal axis. -/
theorem physical_owner_bound_of_source
    (U : Subgroup (Equiv.Perm (Fin 12)))
    (W : C1BinaryNineTopOwnerWitness U (Fin 12))
    (hregular : ∀ N : {N : Subgroup U // N.Normal},
      ∃ F : (W.originalKernelChart.sectionRepresentation
          W.projection W.baseRepresentation N.1).ρ.IntertwiningMap
        (Representation.leftRegular (ZMod 2)
          (U ⧸ (W.projection.ker ⊔ N.1))), Function.Injective F)
    (hTargets : ∀ N : {N : Subgroup U // N.Normal},
      IsDegreeNineTopTarget (U ⧸ (W.projection.ker ⊔ N.1)))
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (b : ℕ) (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    (hP : FusionOrbitNatural U P)
    (hSource : ∀ (N : {N : Subgroup U // N.Normal})
      (J : Subgroup (Equiv.Perm (Fin b))) (β : GroupEpimorphism J (U ⧸ N.1)),
      P (fusionFullGoursatEncode N J β).1 → C1DegreeNineSourcePattern J) :
    (Nat.card (FusionOrbitFamily U (FusionAcceptedOrbitPredicate U P)) : ℝ) /
        exactBenchmark (b + 12) ≤
      c1EarlierKernel b .degreeTwelveMixed
        (∑ N : {N : Subgroup U // N.Normal},
          (originalNormalRegularConstant 2 W.projection W.baseRepresentation
            W.originalKernelChart N : ℝ) * 2187)
        (Nat.card (Subgroup.normalizer (U : Set (Equiv.Perm (Fin 12)))) : ℝ) *
        ((subgroupCount b : ℝ) / exactBenchmark b) := by
  letI : Finite ↥W.baseRepresentation := by
    change Finite W.BaseVector
    infer_instance
  apply c1EarlierPhysical_regular_owner_bound_of_source (p := 2)
    .degreeTwelveMixed U W.projection W.baseRepresentation W.originalKernelChart
    hregular b P hP C1DegreeNineSourcePattern hSource (fun _ => 2187)
    (fun _ => by norm_num)
  intro J hJ N
  have hm := degreeNineTarget_regularTopCharacterMass_le hChief hPrimitive h18
    b J hJ (hTargets N)
  have hinflate :
      2187 * (2 : ℝ) ^ (((25 : ℝ) / 18) * b) ≤
        2187 * ((b : ℝ) + 1) *
          (2 : ℝ) ^ (((25 : ℝ) / 18) * b) := by
    nlinarith [show (0 : ℝ) ≤ b by positivity,
      show 0 < (2 : ℝ) ^ (((25 : ℝ) / 18) * b) by positivity]
  simpa only [c1EarlierExponent] using hm.trans hinflate

end C1BinaryNineTopOwnerWitness

end SymmetricSubgroupAsymptotics

end
