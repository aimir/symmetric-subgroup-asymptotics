import SymmetricSubgroupAsymptotics.BinaryInvariantCyclicOrbitRegistry
import SymmetricSubgroupAsymptotics.Non2PreE7OrdinaryNumericalInstances
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoFiniteNormalImporter
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoResidualAssembly

/-!
# Semantic importer for the degree-two pair-top certificates

The pair-top files have two independently complete finite parts.  Character
kernel intersection words enumerate every normal subgroup of the literal top,
and cyclic binary modules enumerate every invariant submodule of its natural
permutation module.  `DegreeTwoPairTopFiniteInterface` joins those two checked
registries without treating a JSON completeness flag as a theorem.

The remaining mathematical step is the relative-socle lift from those top
data to every normal quotient of an original pair action.  This file gives
that step an exact target.  A `DegreeTwoPairRelativeLiftData` assigns every
literal original normal a profile

`binary/2 + linear*log_2(3)/3 + ordinary*log_2(5)/3
  + relative*log_2(38/25)`

and proves the corresponding epimorphism envelope.  Everything after that
theorem is constructed here: the finite constants are summed, installed as
a bounded-width polynomial tail, and exported as the final rank-tail source.
Thus the importer does not hide the universal lift behind an unexplained
`source` field.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

/-! ## Complete literal top data -/

/-- The two theorem-producing registries attached to one literal pair top.
The module registry uses the actual natural permutation representation on
the displayed top degree. -/
structure DegreeTwoPairTopFiniteInterface (s : ℕ) : Type 1 where
  top : Subgroup (Equiv.Perm (Fin s))
  normalRegistry : FiniteNormalStateRegistry top
  ModuleState : Type
  [moduleStateFinite : Finite ModuleState]
  moduleState : ModuleState → Subrepresentation
    (permutationFunctionRepresentation (ZMod 2) top (Fin s))
  moduleState_injective : Function.Injective moduleState
  moduleRegistry : BinaryInvariantCyclicOrbitRegistry
    (permutationFunctionRepresentation (ZMod 2) top (Fin s)) moduleState
  normalCount : ℕ
  moduleStateCount : ℕ
  cyclicCount : ℕ
  normalCount_eq : Nat.card normalRegistry.State = normalCount
  moduleStateCount_eq : Nat.card ModuleState = moduleStateCount
  cyclicCount_eq : Nat.card moduleRegistry.Cyclic = cyclicCount

attribute [instance] DegreeTwoPairTopFiniteInterface.moduleStateFinite

namespace DegreeTwoPairTopFiniteInterface

variable {s : ℕ} (D : DegreeTwoPairTopFiniteInterface s)

/-- Every literal normal subgroup of the top is one emitted normal state. -/
theorem normal_complete (N : Subgroup D.top) [N.Normal] :
    ∃ i, D.normalRegistry.state i = N :=
  D.normalRegistry.complete N

/-- Every invariant binary submodule of the actual top action is one emitted
module state.  Completeness comes from vector-orbit coverage and cyclic-sum
closure, not from the stored list length. -/
theorem module_complete
    (W : Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) D.top (Fin s))) :
    ∃ i, D.moduleState i = W :=
  D.moduleRegistry.complete W

/-- The duplicate-free module states are exactly all invariant submodules. -/
noncomputable def moduleStateEquiv :
    D.ModuleState ≃ Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) D.top (Fin s)) :=
  Equiv.ofBijective D.moduleState
    ⟨D.moduleState_injective, D.module_complete⟩

/-- Complete a checked top-normal registry with the canonical semantic
registry of all invariant subrepresentations of the natural binary
permutation module.  This is a census-free bridge for small pilot rows and
for legacy top certificates whose old module table used a different
representation.  A compressed generated module registry can later replace
it without changing any downstream state-profile theorem. -/
noncomputable def withCanonicalModuleRegistry
    (top : Subgroup (Equiv.Perm (Fin s)))
    (normalRegistry : FiniteNormalStateRegistry top) :
    DegreeTwoPairTopFiniteInterface s := by
  let rho := permutationFunctionRepresentation (ZMod 2) top (Fin s)
  exact
    { top := top
      normalRegistry := normalRegistry
      ModuleState := Subrepresentation rho
      moduleState := id
      moduleState_injective := Function.injective_id
      moduleRegistry :=
        BinaryInvariantCyclicOrbitRegistry.allSubrepresentations
      normalCount := Nat.card normalRegistry.State
      moduleStateCount := Nat.card (Subrepresentation rho)
      cyclicCount := Nat.card (Fin s → ZMod 2)
      normalCount_eq := rfl
      moduleStateCount_eq := rfl
      cyclicCount_eq := rfl }

end DegreeTwoPairTopFiniteInterface

/-- A literal finite top realized as the top action of an original pair
frame.  The action equality binds the imported natural permutation module
to the frame's coordinate action. -/
structure DegreeTwoPairTopRealization {s : ℕ}
    (D : DegreeTwoPairTopFiniteInterface s)
    (p : PreE7PairActionClass s) : Type 1 where
  frame : BinaryPairFrame (preE7PairAction s p) (Fin s)
  topEquiv : D.top ≃* frame.top.range
  module_action_eq : ∀ g v,
    permutationFunctionRepresentation (ZMod 2) D.top (Fin s) g v =
      frame.coordinateTopAction (topEquiv g) v

/-! ## The exact mixed prefix/relative-tail boundary -/

/-- Counts of the four character positions used by the pair-relative lemma.
The ordinary and relative general positions remain separate; merging them
would lose the `38/25` tail and makes the width-32 rank-four case fail. -/
structure DegreeTwoPairRelativeProfile where
  binaryPrimary : ℕ
  linear : ℕ
  ordinary : ℕ
  relative : ℕ
  deriving DecidableEq

namespace DegreeTwoPairRelativeProfile

/-- The exact base-two exponent per complement point. -/
def slope (P : DegreeTwoPairRelativeProfile) : ℝ :=
  (P.binaryPrimary : ℝ) / 2 +
    (P.linear : ℝ) * (Real.logb 2 3 / 3) +
    (P.ordinary : ℝ) * (Real.logb 2 5 / 3) +
    (P.relative : ℝ) * Real.logb 2 (38 / 25)

end DegreeTwoPairRelativeProfile

/-- Direct counting consequence of a relative character tuple on one fixed
finite quotient.  The coefficient absorbs the target-dependent factors
`|Aut Q|` and `[Q : O_2(Q)]^q`; it is fixed before the later source `J` is
chosen. -/
structure DegreeTwoPairRelativeQuotientEnvelope
    (Q : Type) [Group Q] [Finite Q]
    (profile : DegreeTwoPairRelativeProfile) : Type where
  coefficient : ℝ
  coefficient_nonneg : 0 ≤ coefficient
  bound : ∀ (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))),
    (Nat.card (GroupEpimorphism J Q) : ℝ) ≤
      coefficient * (2 : ℝ) ^ (profile.slope * b)

/-- The universal-lift conclusion for one original pair action.  It ranges
over every literal original normal subgroup, rather than over sampled lifts
or only the normals of the top action. -/
structure DegreeTwoPairRelativeLiftData
    (s : ℕ) (p : PreE7PairActionClass s) : Type 1 where
  profile :
    {N : Subgroup (preE7PairAction s p) // N.Normal} →
      DegreeTwoPairRelativeProfile
  capacity : ∀ N, (profile N).slope ≤ preE7CharacterWindow (2 * s)
  envelope : ∀ N,
    DegreeTwoPairRelativeQuotientEnvelope
      (preE7PairAction s p ⧸ N.1) (profile N)

namespace DegreeTwoPairRelativeLiftData

variable {s : ℕ} {p : PreE7PairActionClass s}
  (D : DegreeTwoPairRelativeLiftData s p)

/-- The finite coefficient on one literal original normal axis. -/
def tailCoefficient
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) : ℝ :=
  (D.envelope N).coefficient

theorem tailCoefficient_nonneg
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    0 ≤ D.tailCoefficient N :=
  (D.envelope N).coefficient_nonneg

/-- Surviving fusion epimorphisms form a subtype of all epimorphisms to the
same literal quotient. -/
theorem survivingEpiCount_le_card {b : ℕ}
    (P : Subgroup
      (preE7PairAction s p × Equiv.Perm (Fin b)) → Prop)
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal})
    (J : Subgroup (Equiv.Perm (Fin b))) :
    fusionSurvivingEpiCount (preE7PairAction s p) P N J ≤
      Nat.card (GroupEpimorphism J (preE7PairAction s p ⧸ N.1)) := by
  letI := groupEpimorphism_finite (J := J)
    (Q := preE7PairAction s p ⧸ N.1)
  unfold fusionSurvivingEpiCount
  exact_mod_cast Nat.card_le_card_of_injective Subtype.val
    Subtype.val_injective

/-- Once the pair-relative theorem supplies its profile, the profile window
gives the exact broad-source tail envelope used by the numerical catalogue. -/
theorem broad_axis_envelope (b : ℕ)
    (hs : s < 24)
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal})
    (J : Subgroup (Equiv.Perm (Fin b))) :
    fusionSurvivingEpiCount (preE7PairAction s p)
        (preE7NoPairNoC3BroadActionPredicate (2 * s)
          (preE7SmallPairNonPairAction s hs p) b) N J ≤
      D.tailCoefficient N *
        (2 : ℝ) ^ (preE7CharacterWindow (2 * s) * b) := by
  refine (D.survivingEpiCount_le_card _ N J).trans ?_
  refine ((D.envelope N).bound b J).trans ?_
  apply mul_le_mul_of_nonneg_left _ (D.tailCoefficient_nonneg N)
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  exact mul_le_mul_of_nonneg_right (D.capacity N) (Nat.cast_nonneg b)

/-- Numerical geometry for installing the direct relative tail in the
ordinary finite-action catalogue.  Width 24 and 32 producers use the same
padded two-point comparator geometry as the whole character template. -/
structure Numerics : Type where
  v : ℕ
  delta : ℝ
  cutoff : ℝ
  alpha : ℝ
  alpha_eq : alpha = cutoff
  parameters : PreE7CharacterEntryParameters preE7CharacterRho (2 * s)
    v 0 delta cutoff alpha (preE7CharacterWindow (2 * s))
  width_upper : 2 * s ≤ 12288

/-- The numerical geometry is uniform: pad the trivial two-point action and
use the global character window as the pure-tail slope.  Consequently the
width-24 and width-32 catalogues do not need row-specific numerical fields. -/
noncomputable def paddedTwoPointNumerics
    (hmargin : preE7CharacterRho * (2 * s) ≤
      ((evenWidth (2 * s) : ℝ) - 2) / 8)
    (hupper : 2 * s ≤ 12288) : D.Numerics := by
  let ι : ℕ → Type := fun w => {_u : Unit // w = 2 * s}
  have hP := growingPadded_parameterBound (ι := ι) (ρ := preE7CharacterRho)
    (fun _ _ => 2) (fun _ _ => 0)
    (by norm_num [preE7CharacterRho]) (by norm_num [preE7CharacterRho])
    (fun _ _ => le_rfl) (fun _ _ => le_rfl)
    (by
      rintro w ⟨_, rfl⟩
      simpa using hmargin)
  let j : ι (2 * s) := ⟨(), rfl⟩
  let v := paddedComparatorDegree preE7CharacterRho 2 (2 * s)
  let delta := paddedComparatorDelta preE7CharacterRho 0 2 (2 * s)
  let cutoff := (v : ℝ) / 8 + delta / 2
  refine
    { v := v
      delta := delta
      cutoff := cutoff
      alpha := cutoff
      alpha_eq := rfl
      parameters := ?_
      width_upper := hupper }
  exact
    { delta_nonneg := hP.delta_nonneg (2 * s) j
      degree_pos := hP.degree_pos (2 * s) j
      ratio := hP.ratio (2 * s) j
      degree_upper := hP.degree_upper (2 * s) j
      delta_lower := hP.delta_lower (2 * s) j
      hot_margin := hP.hot_margin (2 * s) j
      threshold_eq := hP.threshold_eq (2 * s) j
      delta_upper := hP.delta_upper (2 * s) j
      degree_lower := hP.degree_lower (2 * s) j
      degree_width := hP.degree_width (2 * s) j
      cold_slope := hP.cold_slope (2 * s) j
      cold_gap := hP.cold_gap (2 * s) j
      tail_gap := le_rfl }

/-- Install all original-normal relative envelopes as one ordinary
comparator certificate.  The main row vanishes and the whole estimate sits
in the pure tail at the global character window. -/
noncomputable def comparatorCertificate
    (hs : s < 24) (M : D.Numerics) :
    PreE7EarlierActionComparatorCertificate .bchar (2 * s)
      (preE7SmallPairNonPairAction s hs p) where
  R := PUnit
  v := M.v
  action := 1
  action_injective := fun _ _ _ => Subsingleton.elim _ _
  C := fun _ _ => 0
  tailCoefficient := fun _ N => D.tailCoefficient N
  eta := 0
  delta := M.delta
  cutoff := M.cutoff
  alpha := M.alpha
  theta := preE7CharacterWindow (2 * s)
  alpha_eq := by simpa using M.alpha_eq
  coefficient_nonneg := fun _ _ => le_rfl
  tail_nonneg := fun _ N => D.tailCoefficient_nonneg N
  broad_axis_envelope := by
    intro b N J
    simpa using D.broad_axis_envelope b hs N J

/-- The sum of finitely many target constants is automatically a polynomial
bounded-width tail (degree zero).  No false normalization of those constants
to one is needed. -/
theorem tail_total_polynomial (hs : s < 24) (M : D.Numerics) :
    ∃ K : ℝ, ∃ q : ℕ, 0 ≤ K ∧ ∀ b,
      fusionAxisEnvelopeTotal (preE7PairAction s p)
          ((D.comparatorCertificate hs M).tailCoefficient b) ≤
        K * (1 + (b : ℝ)) ^ q := by
  let K := fusionAxisEnvelopeTotal (preE7PairAction s p) D.tailCoefficient
  refine ⟨K, 0, fusionAxisEnvelopeTotal_nonneg _ _
    D.tailCoefficient_nonneg, fun b => ?_⟩
  simp only [comparatorCertificate, one_pow, mul_one]
  exact le_rfl

/-- The exact numerical package consumed by the ordinary rank-tail owner. -/
noncomputable def numericalPackage
    (hs : s < 24) (M : D.Numerics) :
    PreE7EarlierNumericalPackage .bchar (2 * s)
      (preE7SmallPairNonPairAction s hs p) :=
  .ofBoundedTailComparator (D.comparatorCertificate hs M) M.parameters
    (.inl (by
      intro b
      simp only [comparatorCertificate, fusionAxisEnvelopeTotal]
      positivity))
    M.width_upper (D.tail_total_polynomial hs M)

/-- The universal lift plus its elementary fixed-width numerics closes one
original pair representative at the final source boundary. -/
noncomputable def rankTailSource
    (hs : s < 24) (M : D.Numerics) :
    PreE7RankTailSourceOrYonedaTopData (2 * s)
      (preE7SmallPairNonPairAction s hs p) :=
  .inl (.ordinary .bchar (.package (D.numericalPackage hs M)))

end DegreeTwoPairRelativeLiftData

/-- Exact row-level obligation left by the finite importer.  The profile of
every original normal must be one of the row's finite permitted profiles;
the returned lift data then provides the actual quotient envelope. -/
structure DegreeTwoPairTopRelativeLiftConclusion {t s : ℕ}
    (D : DegreeTwoPairTopFiniteInterface t)
    (p : PreE7PairActionClass s) : Type 1 where
  lift : DegreeTwoPairRelativeLiftData s p
  topNormalState :
    {N : Subgroup (preE7PairAction s p) // N.Normal} →
      D.normalRegistry.State
  moduleState :
    {N : Subgroup (preE7PairAction s p) // N.Normal} → D.ModuleState
  profileOfState : D.normalRegistry.State → D.ModuleState →
    DegreeTwoPairRelativeProfile
  profile_eq : ∀ N,
    lift.profile N = profileOfState (topNormalState N) (moduleState N)
  allowedProfiles : Finset DegreeTwoPairRelativeProfile
  allowed_capacity : ∀ profile ∈ allowedProfiles,
    profile.slope ≤ preE7CharacterWindow (2 * s)
  profile_mem : ∀ N, lift.profile N ∈ allowedProfiles

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
