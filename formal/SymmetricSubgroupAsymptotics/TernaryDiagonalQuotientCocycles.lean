import SymmetricSubgroupAsymptotics.TernarySignResolution
import SymmetricSubgroupAsymptotics.DiagonalIsotypeProjection
import Mathlib.LinearAlgebra.Dimension.RankNullity

/-!
# Exact cocycles on an original diagonal sign quotient

The quotient is by the literal invariant submodule K. Distinct original
signs supply projections on that same quotient, so arbitrary correlations
within each sign isotype survive. Summing projected evaluations identifies
its cocycles with the quotient itself when all coordinate signs are
nontrivial. The source B may be an infinite binary group.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.TernaryDiagonalQuotientCocycles

open groupCohomology OddMarkerTernaryChart DiagonalIsotypeProjection

variable {B ι : Type} [Group B] [Fintype ι]
    (χ : ι → B →* Multiplicative (ZMod 2))

def scalar (i : ι) (b : B) : ZMod 3 := signScalar (χ i b)

def diagonalRepresentation : Representation (ZMod 3) B (ι → ZMod 3) where
  toFun := diagonalOperator (scalar χ)
  map_one' := by
    apply LinearMap.ext
    intro v
    funext i
    change signScalar (χ i 1) * v i = v i
    rw [map_one, signScalar_one, one_mul]
  map_mul' b c := by
    apply LinearMap.ext
    intro v
    funext i
    change signScalar (χ i (b*c)) * v i =
      signScalar (χ i b) * (signScalar (χ i c) * v i)
    rw [map_mul, signScalar_mul, mul_assoc]

variable (K : Submodule (ZMod 3) (ι → ZMod 3))
    (hK : ∀ b v, v ∈ K → diagonalOperator (scalar χ) b v ∈ K)

def quotientRep : Rep (ZMod 3) B :=
  Rep.of ((diagonalRepresentation χ).quotient K (fun b _ hv => hK b _ hv))

abbrev Label := CharacterLabel (scalar χ)

/-- A representative only names the actual character of this distinct
scalar label. The projection still contains every original coordinate
with that character. -/
def representative (a : Label χ) : ι := Classical.choose a.2

theorem representative_spec (a : Label χ) : scalar χ (representative χ a) = a.1 :=
  Classical.choose_spec a.2

def labelSign (a : Label χ) : B →* Multiplicative (ZMod 2) := χ (representative χ a)

def projection (a : Label χ) : (quotientRep χ K hK) →ₗ[ZMod 3] quotientRep χ K hK :=
  K.mapQ K (isotypeProjection (scalar χ) a)
    (fun _ hv => isotypeProjection_mem (scalar χ) K hK a _ hv)

@[simp] theorem projection_mk (a : Label χ) (v : ι → ZMod 3) :
    projection χ K hK a (K.mkQ v) = K.mkQ (isotypeProjection (scalar χ) a v) := rfl

@[simp] theorem action_mk (b : B) (v : ι → ZMod 3) :
    (quotientRep χ K hK).ρ b (K.mkQ v) =
      K.mkQ (diagonalOperator (scalar χ) b v) := rfl

private theorem projection_diagonal (a : Label χ) (b : B) (v : ι → ZMod 3) :
    isotypeProjection (scalar χ) a (diagonalOperator (scalar χ) b v) =
      signScalar (labelSign χ a b) • isotypeProjection (scalar χ) a v := by
  funext i
  by_cases hi : scalar χ i = a.1
  · have he : scalar χ i b = signScalar (labelSign χ a b) := by
      change scalar χ i b = scalar χ (representative χ a) b
      rw [hi, representative_spec]
    simp only [isotypeProjection_apply, if_pos hi, diagonalOperator_apply,
      Pi.smul_apply, smul_eq_mul, he]
  · simp only [isotypeProjection_apply, if_neg hi, Pi.smul_apply, smul_zero]

private theorem diagonal_projection (a : Label χ) (b : B) (v : ι → ZMod 3) :
    diagonalOperator (scalar χ) b (isotypeProjection (scalar χ) a v) =
      signScalar (labelSign χ a b) • isotypeProjection (scalar χ) a v := by
  funext i
  by_cases hi : scalar χ i = a.1
  · have he : scalar χ i b = signScalar (labelSign χ a b) := by
      change scalar χ i b = scalar χ (representative χ a) b
      rw [hi, representative_spec]
    simp only [diagonalOperator_apply, isotypeProjection_apply, if_pos hi,
      Pi.smul_apply, smul_eq_mul, he]
  · simp only [diagonalOperator_apply, isotypeProjection_apply, if_neg hi,
      Pi.smul_apply, smul_zero, mul_zero]

theorem projection_action (a : Label χ) (b : B) (v : quotientRep χ K hK) :
    projection χ K hK a ((quotientRep χ K hK).ρ b v) =
      signScalar (labelSign χ a b) • projection χ K hK a v := by
  obtain ⟨w,rfl⟩ := K.mkQ_surjective v
  rw [action_mk, projection_mk, projection_diagonal, map_smul, projection_mk]
  rfl

theorem action_projection (a : Label χ) (b : B) (v : quotientRep χ K hK) :
    (quotientRep χ K hK).ρ b (projection χ K hK a v) =
      signScalar (labelSign χ a b) • projection χ K hK a v := by
  obtain ⟨w,rfl⟩ := K.mkQ_surjective v
  rw [projection_mk, action_mk, diagonal_projection, map_smul]
  rfl

/-- Every distinct sign occurs once, including when its physical
coordinate multiplicity is divisible by three. -/
theorem sum_projection (v : quotientRep χ K hK) :
    (∑ a : Label χ, projection χ K hK a v) = v := by
  obtain ⟨w,rfl⟩ := K.mkQ_surjective v
  simp only [projection_mk]
  calc
    (∑ a : Label χ, K.mkQ (isotypeProjection (scalar χ) a w)) =
        K.mkQ (∑ a : Label χ, isotypeProjection (scalar χ) a w) :=
      (map_sum K.mkQ _ _).symm
    _ = K.mkQ w := congrArg K.mkQ (sum_isotypeProjection (scalar χ) w)

def principalEquiv (hB : IsPGroup 2 B) (hχ : ∀ i, χ i ≠ 1) :
    quotientRep χ K hK ≃ₗ[ZMod 3] cocycles₁ (quotientRep χ K hK) :=
  TernarySignResolution.principalEquiv (quotientRep χ K hK)
    (labelSign χ) (projection χ K hK) hB
    (projection_action χ K hK) (action_projection χ K hK) (sum_projection χ K hK)
    (fun a => Classical.choose (TernarySignCocycles.exists_nontrivial_sign
      (labelSign χ a) (hχ (representative χ a))))
    (fun a => Classical.choose_spec (TernarySignCocycles.exists_nontrivial_sign
      (labelSign χ a) (hχ (representative χ a))))

theorem cocycles_card (hB : IsPGroup 2 B) (hχ : ∀ i, χ i ≠ 1) :
    Nat.card (cocycles₁ (quotientRep χ K hK)) = Nat.card ((ι → ZMod 3) ⧸ K) :=
  (Nat.card_congr (principalEquiv χ K hK hB hχ).toEquiv).symm

theorem cocycles_card_pow (hB : IsPGroup 2 B) (hχ : ∀ i, χ i ≠ 1) :
    Nat.card (cocycles₁ (quotientRep χ K hK)) =
      3 ^ (Fintype.card ι - Module.finrank (ZMod 3) K) := by
  rw [cocycles_card χ K hK hB hχ, Module.natCard_eq_pow_finrank (K := ZMod 3),
    Nat.card_zmod, K.finrank_quotient]
  simp

end SymmetricSubgroupAsymptotics.TernaryDiagonalQuotientCocycles

end
