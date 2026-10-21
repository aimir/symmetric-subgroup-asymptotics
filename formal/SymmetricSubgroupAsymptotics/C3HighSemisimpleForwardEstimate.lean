import SymmetricSubgroupAsymptotics.C3HighSemisimplePhysicalCover
import SymmetricSubgroupAsymptotics.SemisimpleRoundingArbitraryFusion
import SymmetricSubgroupAsymptotics.GrowingQuotientPhysicalAssembly
import SymmetricSubgroupAsymptotics.GrowingMenuMassLogSquared

/-! The separate actual primitive10/12 high sector is exponentially
contractive. It uses only a finite literal action index, the proved complete
semisimple source, the existing outer-factor estimate and coarse subgroup
estimate. Every original quotient axis and the untouched C3 complement are
retained; there is no high-owner estimate premise. -/
set_option autoImplicit false
noncomputable section
open Filter
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.C3HighSemisimpleForward
open Non2UnipotentPrefixFiniteMenu

abbrev Index (w : ℕ) :=
  {U : Subgroup (Equiv.Perm (Fin w)) // (w=10 ∨ w=12) ∧
    Nonempty (LocalSemisimpleRoundingCompressionData U w)}

instance indexFintype (w : ℕ) : Fintype (Index w) := Fintype.ofFinite _

def action (w : ℕ) (i : Index w) := i.1

def data (w : ℕ) (i : Index w) : SemisimpleRoundingFusionData w (action w i) where
  toLocalSemisimpleRoundingCompressionData := Classical.choice i.2.2
  width_lower := by rcases i.2.1 with h|h <;> omega

def divisor (w : ℕ) (i : Index w) : ℝ :=
  Nat.card (Subgroup.normalizer (action w i : Set (Equiv.Perm (Fin w))))

def coefficient (w : ℕ) (i : Index w) (b : ℕ) : ℝ := (data w i).coefficient b

def degree (w : ℕ) (i : Index w) : ℕ := (data w i).degree

def delta (w : ℕ) (i : Index w) : ℝ := (data w i).delta

def cutoff (w : ℕ) (i : Index w) : ℝ := (data w i).cutoff

abbrev source (w : ℕ) (i : Index w) := action w i⧸(data w i).E

def predicate (w : ℕ) (i : Index w) (b : ℕ) :
    Subgroup (action w i×Equiv.Perm (Fin b)) → Prop := fun _ => True

def sector (n : ℕ) : Set (Subgroup (Equiv.Perm (Fin n))) :=
  {G | C3PhysicalHighSemisimpleOwner n G}

def ratio (n : ℕ) : ℝ := (Nat.card (sector n) : ℝ)/exactBenchmark n

theorem divisor_one_le (w : ℕ) (i : Index w) : 1 ≤ divisor w i := by
  unfold divisor
  exact_mod_cast (Nat.succ_le_of_lt (Nat.card_pos (α :=
    Subgroup.normalizer (action w i : Set (Equiv.Perm (Fin w))))))

/-- A fixed finite set of literal actions has subquadratic index count;
no enumeration or numerical class matching is needed. -/
theorem index_subquadratic : SubquadraticMenuIndexCount Index := by
  intro eps heps
  let B : ℝ := subgroupCount 10+subgroupCount 12+1
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨B,hB,?_⟩
  intro w
  have hr : 1 ≤ (2 : ℝ)^(eps*(w : ℝ)^2) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  have hcard : (Nat.card (Index w) : ℝ) ≤ B := by
    by_cases hw : w=10 ∨ w=12
    · have hs : Nat.card (Index w) ≤ subgroupCount w := by
        exact Nat.card_le_card_of_injective (fun i : Index w => i.1) Subtype.val_injective
      have hsR : (Nat.card (Index w) : ℝ) ≤ subgroupCount w := by exact_mod_cast hs
      rcases hw with rfl|rfl <;> dsimp [B] <;>
        nlinarith [(Nat.cast_nonneg (subgroupCount 10) : (0 : ℝ) ≤ subgroupCount 10),
          (Nat.cast_nonneg (subgroupCount 12) : (0 : ℝ) ≤ subgroupCount 12)]
    · letI : IsEmpty (Index w) := ⟨fun i => hw i.2.1⟩
      rw [Nat.card_eq_zero.mpr (Or.inl inferInstance), Nat.cast_zero]
      exact hB
  exact hcard.trans (by nlinarith)

theorem numerator_bound (hOuter : SemisimpleOuterFactorPermutationBound) :
    LinearLogSquaredMenuNumeratorBound 10 coefficient := by
  refine ⟨1,0,16,by norm_num,by norm_num,by norm_num,?_⟩
  intro n w hw i
  have hwb : w+(n-w)+2=n+2 := by
    have := (Finset.mem_Ico.mp hw).2
    omega
  simpa only [coefficient,zero_mul,zero_add,one_mul,hwb,Nat.cast_add,Nat.cast_ofNat]
    using (data w i).coefficient_bound hOuter (n-w)

theorem mass (hOuter : SemisimpleOuterFactorPermutationBound) :
    GrowingMenuMassBound 10 coefficient divisor :=
  growingMenuMassBound_of_linearLogSquared (by decide) coefficient divisor
    (fun w i b => (data w i).coefficient_nonneg b) divisor_one_le index_subquadratic
    (numerator_bound hOuter)

theorem parameters : GrowingQuotientParameterBound preE7CharacterRho
    degree (fun _ _ => 0) delta cutoff cutoff := by
  have h := growingPadded_parameterBound
    (ρ := preE7CharacterRho) (fun w i => (data w i).seedDegree) (fun _ _ => (0 : ℝ))
    (by norm_num [preE7CharacterRho]) (by norm_num [preE7CharacterRho])
    (fun _ _ => le_rfl) (fun w i => (data w i).seedDegree_two_le)
    (by intro w i; simpa only [sub_zero] using (data w i).padded_margin)
  simpa only [degree,delta,cutoff,SemisimpleRoundingFusionData.degree,
    SemisimpleRoundingFusionData.delta,SemisimpleRoundingFusionData.cutoff,zero_add] using h

theorem physical
    (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (published8 : PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification) :
    GrowingQuotientPhysicalBound ratio 10 coefficient divisor degree
      (fun _ _ => 0) delta cutoff cutoff := by
  apply growingQuotientPhysicalBound_of_local ratio 10 (by decide) sector action predicate
    coefficient divisor degree (fun _ _ => 0) delta cutoff cutoff
    (Filter.Eventually.of_forall (fun _ => le_rfl)) ?_ ?_
  · intro n G hG
    obtain ⟨j,hn,hmem⟩ := c3PhysicalHighSemisimpleOwner_finiteFusionCover hindex published8 G hG
    let w := c3SemisimpleHighWidth j.1
    have hw : w=10 ∨ w=12 := by
      dsimp [w,c3SemisimpleHighWidth]
      split <;> simp
    let i : Index w := ⟨c3HighSemisimpleAction j,hw,⟨c3HighSemisimpleCompression j⟩⟩
    let k : GrowingQuotientPhysicalIndex (ι := Index) 10 n :=
      ⟨⟨w,Finset.mem_Ico.mpr ⟨by rcases hw with h|h <;> omega,by omega⟩⟩,i⟩
    exact ⟨k,hmem⟩
  · apply growingQuotientLocalPhysicalBound_of_completeSource 10 action predicate source
      coefficient divisor degree (fun _ _ => 0) delta cutoff cutoff
      (fun w i => (data w i).paddedAction)
      (fun w i => (data w i).paddedAction_injective)
      (fun _ _ _ _ _ _ => trivial)
      (fun w i b => (data w i).coefficient_nonneg b)
      (fun _ _ => rfl) (fun _ _ => by simp) ?_
    intro w i b J
    exact (data w i).source_bound b (predicate w i b) J

/-- Complete actual-sector forward estimate with no unproved owner premise. -/
def forwardEstimate
    (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (published8 : PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (hOuter : SemisimpleOuterFactorPermutationBound)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ))) :
    OrdinaryFrontierClosure.ExponentialForwardEstimate ratio :=
  growingQuotient_exponentialForwardEstimate ratio 10 coefficient divisor degree
    (fun _ _ => 0) delta cutoff cutoff
    (by norm_num [preE7CharacterRho]) (by norm_num [preE7CharacterRho]) (by decide)
    (fun w i b => (data w i).coefficient_nonneg b)
    (fun w i => lt_of_lt_of_le (by norm_num : (0 : ℝ)<1) (divisor_one_le w i))
    parameters (mass hOuter) hcoarse (physical hindex published8)

end SymmetricSubgroupAsymptotics.C3HighSemisimpleForward
