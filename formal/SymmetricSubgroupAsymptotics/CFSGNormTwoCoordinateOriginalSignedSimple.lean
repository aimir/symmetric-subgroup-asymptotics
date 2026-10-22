import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalOppositePairData
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSelfRootConjugation
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOrthogonalWeyl
import SymmetricSubgroupAsymptotics.CFSGRankOneNoncommutation

/-! Both signed canonical simple parameters in the same original
projective group. Off-diagonal opposite signs commute. Equal-index
parameter-one elements do not commute, including characteristic two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalSignedSimple
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGGeckSerreRepresentation CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckPositivePGroup
open CFSGNormTwoCoordinateOriginalProjection CFSGNormTwoCoordinateOriginalPositiveCenter
open CFSGNormTwoCoordinateOriginalOppositeAlignment CFSGNormTwoCoordinateOriginalOppositePairData
open CFSGNormTwoCoordinateElementaryRootParameters CFSGNormTwoCoordinateRootHeightQuotient
open CFSGNormTwoCoordinatePositiveQuotientInjectivity CFSGNormTwoCoordinateHeight
open CFSGNormTwoGeckOppositeIntersection CFSGNormTwoGeckSelfRootConjugation
open CFSGNormTwoGeckRationalAdjointStrings CFSGNormTwoGeckRationalWeylCollecting
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀ j, A j j = 2)
    (hs : A.transpose = A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀ i j, i ≠ j → A i j ≤ 0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    (K : Type) [Field K]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀

/-- Literal signed parameters before the original projective quotient. -/
def elementarySimpleHom (neg : Bool) (j : Fin r) :
    Multiplicative K →* ElementaryGroup A hd hs hp ho K where
  toFun a := canonicalElementaryRoot D K neg j a.toAdd
  map_one' := Subtype.ext (canonicalRoot_zero D K neg j)
  map_mul' a b := Subtype.ext (canonicalRoot_add D K neg j a.toAdd b.toAdd).symm

/-- The same parameters mapped through the actual original projection. -/
def originalSimpleHom [IsSimpleGroup (Projective (cartan b₀ s₀) K)]
    (i : Fin r) (neg : Bool) (j : Fin r) : Multiplicative K →* Projective (cartan b₀ s₀) K :=
  (originalProjection A hd hs hp ho K i).comp (elementarySimpleHom A hd hs hp ho K neg j)

theorem positive_mem [IsSimpleGroup (Projective (cartan b₀ s₀) K)]
    (i j : Fin r) (a : Multiplicative K) :
    originalSimpleHom A hd hs hp ho K i false j a ∈ originalPositive A hd hs hp ho K i := by
  rw [originalPositive_eq_map]
  exact ⟨elementarySimpleHom A hd hs hp ho K false j a,
    Subgroup.subset_closure ⟨(j, a.toAdd), rfl⟩, rfl⟩

omit [(rootPairing A hs hp).IsReduced] in
theorem negative_mem [IsSimpleGroup (Projective (cartan b₀ s₀) K)]
    (i j : Fin r) (a : Multiplicative K) :
    originalSimpleHom A hd hs hp ho K i true j a ∈ originalNegative A hd hs hp ho K i :=
  ⟨elementarySimpleHom A hd hs hp ho K true j a,
    Subgroup.subset_closure ⟨(j, a.toAdd), rfl⟩, rfl⟩

theorem positive_one_ne_one [Finite K] [Nontrivial (Fin r)]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i j : Fin r) :
    originalSimpleHom A hd hs hp ho K i false j (Multiplicative.ofAdd 1) ≠ 1 := by
  intro he
  let x : PositiveGroup A hd hs hp ho K :=
    ⟨canonicalRoot D K false j 1, Subgroup.subset_closure ⟨(j, 1), rfl⟩⟩
  have hx : x = 1 := originalProjection_positive_injective A hd hs hp ho K p i
    (a₁ := x) (a₂ := 1) (by simpa only [map_one] using he)
  exact canonicalRoot_one_ne_one A hs hp b₀ s₀ coordinateHeight
    (simple_height A hd hs hp ho) K j (congrArg Subtype.val hx)

theorem opposite_distinct_indices_commute
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)]
    (i j k : Fin r) (hjk : j ≠ k) (a b : Multiplicative K) :
    Commute (originalSimpleHom A hd hs hp ho K i false j a)
      (originalSimpleHom A hd hs hp ho K i true k b) := by
  have hc := CFSGSerreQuadraticSignedCommutation.roots_commute D K false true j k
    (by rw [rational_E_eq, rational_F_eq, EF, if_neg hjk]) a.toAdd b.toAdd
  have he : Commute (elementarySimpleHom A hd hs hp ho K false j a)
      (elementarySimpleHom A hd hs hp ho K true k b) := Subtype.ext hc.eq
  exact he.map (originalProjection A hd hs hp ho K i)

set_option maxHeartbeats 800000 in
theorem same_index_not_commute [Finite K] [Nontrivial (Fin r)]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i j : Fin r)
    (hdisj : originalPositive A hd hs hp ho K i ⊓ originalNegative A hd hs hp ho K i = ⊥) :
    ¬ Commute (originalSimpleHom A hd hs hp ho K i false j (Multiplicative.ofAdd 1))
      (originalSimpleHom A hd hs hp ho K i true j (Multiplicative.ofAdd 1)) := by
  let u := elementarySimpleHom A hd hs hp ho K false j (Multiplicative.ofAdd 1)
  let v := elementarySimpleHom A hd hs hp ho K true j (Multiplicative.ofAdd 1)
  let f := originalProjection A hd hs hp ho K i
  have hsep : f u ≠ (f v)⁻¹ := by
    intro he
    have hm : f u ∈ originalPositive A hd hs hp ho K i ⊓ originalNegative A hd hs hp ho K i :=
      ⟨positive_mem A hd hs hp ho K i j _, by
        rw [he]
        exact (originalNegative A hd hs hp ho K i).inv_mem (negative_mem A hd hs hp ho K i j _)⟩
    rw [hdisj, Subgroup.mem_bot] at hm
    exact positive_one_ne_one A hd hs hp ho K p i j hm
  apply CFSGRankOneNoncommutation.not_commute (f u) (f v) hsep
  have href : (u * v⁻¹ * u) * u * (u * v⁻¹ * u)⁻¹ = v⁻¹ := by
    apply Subtype.ext
    have hu : u.val = canonicalRoot D K false j 1 := rfl
    have hv : (v⁻¹).val = canonicalRoot D K true j (-1) :=
      canonicalRoot_inverse D K true j 1
    change (u.val * (v⁻¹).val * u.val) * u.val *
      (u.val * (v⁻¹).val * u.val)⁻¹ = (v⁻¹).val
    rw [hu, hv]
    exact self_root_word A hs hp b₀ s₀ K j 1
  simpa only [map_mul, map_inv] using congrArg f href

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalSignedSimple
