import SymmetricSubgroupAsymptotics.CFSGFieldRootTorusConjugacy
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalRootFamily
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveRootCardinality
import SymmetricSubgroupAsymptotics.CFSGConjugateSubgroupDegree

/-! The actual original dominant-root group gives a field-size lower
bound for every proper subgroup index. Full unit scaling supplies literal
nonidentity conjugacy; Burnside's fixed-point count supplies the degree
bound. No minimum-index table or automorphism lift is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalRootDegree
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGGeckSerreRepresentation CFSGNormTwoGeckIntegralRealization
open CFSGNormTwoCoordinateRootHeightQuotient CFSGNormTwoCoordinatePositiveRootGenerators
open CFSGNormTwoCoordinateSelectedRootAdditive CFSGNormTwoCoordinateSelectedRootElement
open CFSGNormTwoCoordinatePositiveRootCardinality CFSGNormTwoCoordinateElementaryRootParameters
open CFSGNormTwoCoordinatePositiveQuotientInjectivity CFSGNormTwoCoordinateOriginalProjection
open CFSGNormTwoCoordinateOriginalRootFamily CFSGNormTwoCoordinateRootTorusConjugation
open CFSGNormTwoCoordinateHighestRootUnitCharacter
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀ i, A i i = 2)
    (hs : A.transpose = A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀ i j, i ≠ j → A i j ≤ 0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    (K : Type) [Field K]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

def positiveSelectedHom (θ : Roots A) (hθ : ∀ j, 0 ≤ θ.val j) :
    Multiplicative K →* PositiveGroup A hd hs hp ho K :=
  (selectedRootHom A hd hs hp ho K θ).codRestrict (PositiveGroup A hd hs hp ho K)
    (fun a => selected_positive_root_mem A hd hs hp ho K θ hθ a.toAdd)

def originalSelectedHom [IsSimpleGroup (Projective (cartan b₀ s₀) K)]
    (i : Fin r) (θ : Roots A) (hθ : ∀ j, 0 ≤ θ.val j) :
    Multiplicative K →* Projective (cartan b₀ s₀) K :=
  ((originalProjection A hd hs hp ho K i).comp (positiveInclusion A hd hs hp ho K)).comp
    (positiveSelectedHom A hd hs hp ho K θ hθ)

theorem originalSelectedHom_apply [IsSimpleGroup (Projective (cartan b₀ s₀) K)]
    (i : Fin r) (θ : Roots A) (hθ : ∀ j, 0 ≤ θ.val j) (a : Multiplicative K) :
    originalSelectedHom A hd hs hp ho K i θ hθ a =
      originalProjection A hd hs hp ho K i (elementarySelectedRootHom A hd hs hp ho K θ a) := rfl

theorem originalSelectedHom_injective [Finite K] [Nontrivial (Fin r)]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)]
    (i : Fin r) (θ : Roots A) (hθ : ∀ j, 0 ≤ θ.val j) :
    Function.Injective (originalSelectedHom A hd hs hp ho K i θ hθ) := by
  apply (originalProjection_positive_injective A hd hs hp ho K p i).comp
  intro a b he
  exact selected_positive_rootHom_injective A hd hs hp ho K θ hθ (congrArg Subtype.val he)

theorem originalSelectedHom_unit_scaling [Nontrivial (Fin r)]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)]
    (i : Fin r) (θ : Roots A) (hθ : ∀ j, 0 ≤ θ.val j)
    (hdom : ∀ j, 0 ≤ integerPairing A θ.val (Pi.single j (1 : ℤ) : Fin r → ℤ))
    (t : Kˣ) : ∃ g : Projective (cartan b₀ s₀) K, ∀ a : K,
      g * originalSelectedHom A hd hs hp ho K i θ hθ (Multiplicative.ofAdd a) * g⁻¹ =
        originalSelectedHom A hd hs hp ho K i θ hθ (Multiplicative.ofAdd (a * (t : K))) := by
  obtain ⟨j, hpair⟩ := dominant_root_has_unit_simple_pairing A hd hs hp ho θ hθ hdom
  refine ⟨originalProjection A hd hs hp ho K i (elementaryTorus A hd hs hp ho K j t), ?_⟩
  intro a
  rw [originalSelectedHom_apply, originalSelectedHom_apply]
  rw [← map_inv, ← map_mul, ← map_mul]
  apply congrArg (originalProjection A hd hs hp ho K i)
  apply Subtype.ext
  simpa only [hpair, zpow_one] using torus_conjugate_selected_root A hd hs hp ho K j t θ a

theorem field_card_le_proper_index [Finite K] [Nontrivial (Fin r)]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)]
    (i : Fin r) (θ : Roots A) (hθ : ∀ j, 0 ≤ θ.val j)
    (hdom : ∀ j, 0 ≤ integerPairing A θ.val (Pi.single j (1 : ℤ) : Fin r → ℤ))
    (H : Subgroup (Projective (cartan b₀ s₀) K)) (hH : H ≠ ⊤) : Nat.card K ≤ H.index := by
  letI : Finite (Projective (cartan b₀ s₀) K) := original_projective_finite A hd hs hp ho K i
  let u := originalSelectedHom A hd hs hp ho K i θ hθ
  have hu : Function.Injective u := originalSelectedHom_injective A hd hs hp ho K p i θ hθ
  letI : Nontrivial u.range := (MonoidHom.ofInjective hu).symm.surjective.nontrivial
  rw [← CFSGFieldRootTorusConjugacy.range_card u hu]
  exact CFSGConjugateSubgroupDegree.card_le_index_of_nonidentity_conjugate u.range
    (CFSGFieldRootTorusConjugacy.nonidentity_range_conjugate u
      (originalSelectedHom_unit_scaling A hd hs hp ho K i θ hθ hdom)) H hH

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalRootDegree
