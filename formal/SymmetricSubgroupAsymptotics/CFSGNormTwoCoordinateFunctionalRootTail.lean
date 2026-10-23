import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootHeightFiltration
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootHeightLeading
import SymmetricSubgroupAsymptotics.CFSGGradedQuadraticUnit

/-! Genuine positive-root tails for any nonnegative integral functional.
The original positive-pair commutator identities prove their normality;
the SAME actual root coefficients prove strict matrix support when the
functional is positive. This includes folded simple-orbit complements. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateFunctionalRootTail
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoPairingBounds
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckPositivePGroup
open CFSGNormTwoGeckLatticeDegree CFSGNormTwoCoordinateRootSubgroup
open CFSGNormTwoCoordinateSelectedRootElement CFSGNormTwoCoordinateSelectedRootAdditive
open CFSGNormTwoCoordinatePositiveRootGenerators CFSGNormTwoCoordinatePositivePairCollecting
open CFSGNormTwoCoordinateRootElementRange CFSGNormTwoCoordinateRootHeightLeading
open CFSGNormTwoCoordinateRootCoefficientCoordinates CFSGGradedQuadraticUnit
open CFSGNormTwoCoordinateRootBracketTransport
open CFSGGradedMatrixSupport CFSGGradedMatrixSubgroups
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀ i, A i i = 2)
    (hs : A.transpose = A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀ i j, i ≠ j → A i j ≤ 0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
private abbrev Mat (K : Type) := Matrix ((b₀).support ⊕ Roots A) ((b₀).support ⊕ Roots A) K

def functionalRootGenerators (K : Type) [Field K] (f : (Fin r → ℤ) →ₗ[ℤ] ℤ)
    (h : ℤ) : Set (Mat A hd hs hp ho K)ˣ :=
  {x | ∃ k : PositiveRoot A, h ≤ f k.val.val ∧ ∃ a : K,
    selectedRootElement A hd hs hp ho K k.val a = x}

def functionalTail (K : Type) [Field K] (f : (Fin r → ℤ) →ₗ[ℤ] ℤ)
    (h : ℤ) : Subgroup (Mat A hd hs hp ho K)ˣ :=
  Subgroup.closure (functionalRootGenerators A hd hs hp ho K f h)

theorem root_mem_functionalTail (K : Type) [Field K] (f : (Fin r → ℤ) →ₗ[ℤ] ℤ)
    (h : ℤ) (k : Roots A) (hk : ∀ i, 0 ≤ k.val i) (hfk : h ≤ f k.val) (a : K) :
    selectedRootElement A hd hs hp ho K k a ∈ functionalTail A hd hs hp ho K f h :=
  Subgroup.subset_closure ⟨⟨k, hk⟩, hfk, a, rfl⟩

theorem functionalTail_le_positive (K : Type) [Field K] (f : (Fin r → ℤ) →ₗ[ℤ] ℤ) (h : ℤ) :
    functionalTail A hd hs hp ho K f h ≤ rootGroup A hs hp b₀ s₀ K false := by
  apply (Subgroup.closure_le _).mpr
  rintro x ⟨k, hk, a, rfl⟩
  exact selected_positive_root_mem A hd hs hp ho K k.val k.property a

theorem root_commutator_mem_functionalTail (K : Type) [Field K]
    (f : (Fin r → ℤ) →ₗ[ℤ] ℤ) (h : ℤ) (k l : Roots A)
    (hk : ∀ i, 0 ≤ k.val i) (hl : ∀ i, 0 ≤ l.val i)
    (hfk : 0 ≤ f k.val) (hfl : h ≤ f l.val) (a b : K) :
    selectedRootElement A hd hs hp ho K k a * selectedRootElement A hd hs hp ho K l b *
      (selectedRootElement A hd hs hp ho K k a)⁻¹ *
      (selectedRootElement A hd hs hp ho K l b)⁻¹ ∈ functionalTail A hd hs hp ho K f h := by
  by_cases hkl : k = l
  · subst l
    rw [(selectedRootElement_commute A hd hs hp ho K k a b).eq]
    have he : selectedRootElement A hd hs hp ho K k b * selectedRootElement A hd hs hp ho K k a *
        (selectedRootElement A hd hs hp ho K k a)⁻¹ *
        (selectedRootElement A hd hs hp ho K k b)⁻¹ = 1 := by group
    rw [he]
    exact (functionalTail A hd hs hp ho K f h).one_mem
  have hopp : k.val ≠ -l.val := by
    intro he
    have hz : k.val = 0 := by
      funext j
      have hj := congrFun he j
      change k.val j = -(l.val j) at hj
      have := hk j
      have := hl j
      change k.val j = 0
      omega
    have hn := k.property
    rw [hz] at hn
    norm_num at hn
  rcases root_pairing_interior A hs hp k l hkl hopp with hneg | hother
  · obtain ⟨ε, _, he⟩ := positive_pair_commutator_sign A hd hs hp ho k l hk hl hneg
    rw [he K a b]
    apply root_mem_functionalTail A hd hs hp ho K f h (sumRoot A hs k l hneg)
    · exact fun j => add_nonneg (hk j) (hl j)
    · change h ≤ f (k.val + l.val)
      rw [map_add]
      omega
  · have hc := CFSGNormTwoCoordinatePositivePairCommute.positive_pair_commute
      A hd hs hp ho K k l hk hl hother a b
    have he : selectedRootElement A hd hs hp ho K k a * selectedRootElement A hd hs hp ho K l b *
        (selectedRootElement A hd hs hp ho K k a)⁻¹ *
        (selectedRootElement A hd hs hp ho K l b)⁻¹ = 1 := by rw [hc.eq]; group
    rw [he]
    exact (functionalTail A hd hs hp ho K f h).one_mem

theorem positive_le_normalizer_functionalTail (K : Type) [Field K]
    (f : (Fin r → ℤ) →ₗ[ℤ] ℤ) (h : ℤ)
    (hf : ∀ k : PositiveRoot A, 0 ≤ f k.val.val) :
    rootGroup A hs hp b₀ s₀ K false ≤ Subgroup.normalizer
      (functionalTail A hd hs hp ho K f h : Set (Mat A hd hs hp ho K)ˣ) := by
  rw [positive_group_eq_iSup A hd hs hp ho K]
  apply iSup_le
  intro k
  apply CFSGParameterCommutatorNormalizer.range_normalizes_closure
    (G := (Mat A hd hs hp ho K)ˣ)
    (fun a : K => selectedRootElement A hd hs hp ho K k.val a)
    (rootSubgroup A hd hs hp ho K k.val) (functionalRootGenerators A hd hs hp ho K f h)
    (mem_rootSubgroup_iff_selected A hd hs hp ho K k.val)
  rintro a y ⟨l, hl, b, rfl⟩
  exact root_commutator_mem_functionalTail A hd hs hp ho K f h k.val l.val
    k.property l.property (hf k) hl a b

theorem selected_root_strict (K : Type) [Field K] (f : (Fin r → ℤ) →ₗ[ℤ] ℤ)
    (k : Roots A) (hfk : 0 < f k.val) (a : K) :
    selectedRootElement A hd hs hp ho K k a ∈
      strictUnits (fun j => f (latticeWeight A hs hp b₀ j)) := by
  apply strict_of_height_positive (latticeWeight A hs hp b₀) k.val f.toAddMonoidHom
    (selectedRootElement A hd hs hp ho K k a) _ hfk
  refine ⟨a • selectedFieldCoefficient A hd hs hp ho K k,
    a ^ 2 • selectedSecondCoefficient A hd hs hp ho K k,
    selectedRootElement_expansion A hd hs hp ho K k a, ?_, ?_⟩
  · exact supported_smul _ _ _ (selectedFieldCoefficient_support A hd hs hp ho K k) a
  · exact supported_smul _ _ _ (selectedSecondCoefficient_support A hd hs hp ho K k) (a ^ 2)

theorem functionalTail_le_strict (K : Type) [Field K] (f : (Fin r → ℤ) →ₗ[ℤ] ℤ)
    (h : ℤ) (hh : 0 < h) :
    functionalTail A hd hs hp ho K f h ≤
      strictUnits (fun j => f (latticeWeight A hs hp b₀ j)) := by
  apply (Subgroup.closure_le _).mpr
  rintro x ⟨k, hk, a, rfl⟩
  exact selected_root_strict A hd hs hp ho K f k.val (lt_of_lt_of_le hh hk) a

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateFunctionalRootTail
