import SymmetricSubgroupAsymptotics.CFSGFFourE6HeightOrbitChart
import SymmetricSubgroupAsymptotics.CFSGFFourFilteredChartCardinality
import SymmetricSubgroupAsymptotics.CFSGFFourE6FixedHeightLifting

/-! Nine independent parameters in the ACTUAL folded positive
centralizer of EVERY relative-Weyl image of the E6 highest root. Each
height chart is separated in the actual next-tail quotient. Only these
charts, their genuine folded membership and integer orthogonality are
used; no exact F4 order or presumed fixed ordered normal form occurs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6CentralizerCapacity
open CFSGFFourE6HeightOrbitChart CFSGFFourE6OrbitRepresentativeHeights
open CFSGFFourE6CentralizerRootPilot CFSGFFourE6CentralizerRootTransport
open CFSGFFourE6PositiveOrbitFactors CFSGFFourFilteredChartCardinality
open CFSGFFourE6FixedHeightLifting CFSGTwistedE6GeckPositiveTwist
open CFSGTwistedE6GeckHeightQuotientTwist CFSGTwistedE6GeckSectionRootParameters
open CFSGNormTwoCoordinateRootHeightFiltration CFSGNormTwoCoordinateRootHeightBound
open CFSGNormTwoCoordinatePositiveRootCardinality CFSGExceptionalCartanPositiveDefinite

def foldedCentralizer (K : Type) [Field K] (r : List (Fin 4)) : Subgroup (Positive K) :=
  foldedUpper K ⊓ rootCentralizer K (transportedHighest r)

def orbitGenerated (K : Type) [Field K] (r : List (Fin 4)) : Subgroup (Positive K) :=
  Subgroup.closure (Set.range (fun z : (i : Fin 15) × RootLine K (transportedRoot r i).val=>
    rootOrbitFactor K (transportedRoot r z.1) z.2))

theorem orbitFactor_mem_generated (K : Type) [Field K] (r : List (Fin 4)) (i : Fin 15)
    (x : RootLine K (transportedRoot r i).val) :
    rootOrbitFactor K (transportedRoot r i) x∈orbitGenerated K r :=
  Subgroup.subset_closure ⟨⟨i,x⟩,rfl⟩

theorem orbitGenerated_le_foldedCentralizer (K : Type) [Field K] [Finite K]
    (r : List (Fin 4)) : orbitGenerated K r≤foldedCentralizer K r := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨⟨i,x⟩,rfl⟩
  constructor
  · exact rootOrbitFactor_mem_folded K (transportedRoot r i) x
  · apply rootOrbitFactor_centralizes
    · exact transportedRoot_orthogonal r i
    · rw [transportedRoot_diagram]
      exact transportedRoot_orthogonal r (partner i)

def centralizerTail (K : Type) [Field K] (r : List (Fin 4)) (n : ℕ) :
    Subgroup (Positive K) := orbitGenerated K r ⊓ TailInPositive K ((n:ℤ)+1)

abbrev Parameters (K : Type) [Field K] (r : List (Fin 4)) (n : ℕ) :=
  ∀j : HeightReps r n,RootLine K (rootSlot r n j).val.val

theorem heightWord_mem_generated (K : Type) [Field K]
    (r : List (Fin 4)) (n : ℕ) (c : Parameters K r n) :
    heightWord K r n c∈orbitGenerated K r := by
  apply heightWord_mem_of_factors
  intro j
  exact orbitFactor_mem_generated K r (representative j.val) (c j)

theorem heightWord_mem_foldedCentralizer (K : Type) [Field K] [Finite K]
    (r : List (Fin 4)) (n : ℕ) (c : Parameters K r n) :
    heightWord K r n c∈foldedCentralizer K r :=
  orbitGenerated_le_foldedCentralizer K r (heightWord_mem_generated K r n c)

def filteredWord (K : Type) [Field K] [Finite K] (r : List (Fin 4)) (n : ℕ)
    (c : Parameters K r n) : centralizerTail K r n :=
  ⟨heightWord K r n c,heightWord_mem_generated K r n c,heightWord_mem_tail K r n c⟩

theorem centralizerTail_antitone_step (K : Type) [Field K] (r : List (Fin 4)) (n : ℕ) :
    centralizerTail K r (n+1)≤centralizerTail K r n := by
  intro u hu
  refine ⟨hu.1,?_⟩
  exact heightTail_antitone CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
    E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K (by omega) hu.2

theorem filteredWord_separation (K : Type) [Field K] [Finite K] (r : List (Fin 4)) (n : ℕ)
    (c d : Parameters K r n)
    (he : (filteredWord K r n c : Positive K)⁻¹*(filteredWord K r n d : Positive K)∈
      centralizerTail K r (n+1)) : c=d := by
  apply heightWord_coset_separation K r n c d
  have hn : (((n+1:ℕ):ℤ)+1)=(n:ℤ)+1+1 := by omega
  simpa only [filteredWord,hn] using he.2

theorem parameters_card (K : Type) [Field K] [Finite K] (r : List (Fin 4)) (n : ℕ) :
    Nat.card (Parameters K r n)=Nat.card K^Nat.card (HeightReps r n) := by
  rw [Nat.card_pi]
  have he (j : HeightReps r n) : Nat.card (RootLine K (rootSlot r n j).val.val)=Nat.card K :=
    positive_rootSubgroup_card CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
      E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K
        (rootSlot r n j).val.val (rootSlot r n j).val.property
  simp only [he,Finset.prod_const,Finset.card_univ,Nat.card_eq_fintype_card]

def heightRepsEquiv (r : List (Fin 4)) (h : Fin (rootHeightBound CartanMatrix.E₆)) :
    HeightReps r h.val ≃ HeightRep r h where
  toFun j := ⟨j.val,Fin.ext j.property⟩
  invFun j := ⟨j.val,congrArg Fin.val j.property⟩
  left_inv _j := rfl
  right_inv _j := rfl

theorem product_parameters_card (K : Type) [Field K] [Finite K] (r : List (Fin 4)) :
    (∏n∈Finset.range (rootHeightBound CartanMatrix.E₆),Nat.card (Parameters K r n))=
      Nat.card K^9 := by
  rw [←Fin.prod_univ_eq_prod_range]
  calc
    (∏h : Fin (rootHeightBound CartanMatrix.E₆),Nat.card (Parameters K r h.val))=
        ∏h : Fin (rootHeightBound CartanMatrix.E₆),Nat.card K^Nat.card (HeightRep r h) := by
      apply Finset.prod_congr rfl
      intro h _
      rw [parameters_card,Nat.card_congr (heightRepsEquiv r h)]
    _=Nat.card K^9 := product_height_parameter_card r (Nat.card K)

theorem centralizerTail_zero (K : Type) [Field K] (r : List (Fin 4)) :
    centralizerTail K r 0=orbitGenerated K r := by
  have ht : TailInPositive K 1=⊤ := by
    ext u
    constructor
    · intro _
      trivial
    · intro _
      change u.val∈heightTail CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
        E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K 1
      rw [CFSGNormTwoCoordinatePositiveHeightNormalForm.heightTail_one_eq_positive]
      exact u.property
  ext u
  change (u∈orbitGenerated K r ∧ u∈TailInPositive K 1) ↔ u∈orbitGenerated K r
  constructor
  · exact And.left
  · intro hu
    refine ⟨hu,?_⟩
    rw [ht]
    trivial

theorem orbit_generated_card_lower_nine (K : Type) [Field K] [Finite K]
    (r : List (Fin 4)) : Nat.card K^9≤Nat.card (orbitGenerated K r) := by
  have h := filtered_chart_card_lower (centralizerTail K r) (Parameters K r)
    (centralizerTail_antitone_step K r) (filteredWord K r) (filteredWord_separation K r)
    (rootHeightBound CartanMatrix.E₆)
  rw [product_parameters_card,centralizerTail_zero] at h
  exact h

theorem folded_centralizer_card_lower_nine (K : Type) [Field K] [Finite K]
    (r : List (Fin 4)) : Nat.card K^9≤Nat.card (foldedCentralizer K r) :=
  (orbit_generated_card_lower_nine K r).trans
    (Nat.card_le_card_of_injective (Subgroup.inclusion (orbitGenerated_le_foldedCentralizer K r))
      (Subgroup.inclusion_injective _))

end SymmetricSubgroupAsymptotics.CFSGFFourE6CentralizerCapacity
