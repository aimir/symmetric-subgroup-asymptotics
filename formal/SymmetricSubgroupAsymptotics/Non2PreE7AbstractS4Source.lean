import SymmetricSubgroupAsymptotics.Non2PreE7SmallAdditiveRecoveredNumerics
import SymmetricSubgroupAsymptotics.Non2PreE7SmallAdditiveNumericalInstances

/-!
# The abstract S4 complete source at width six

The historical `S4` owner is phrased for the natural four-point action, but
its counting theorem only uses the abstract target group.  In particular the
same normal-menu projection to `S3` and the same second-derived epimorphism
bound apply to either faithful transitive six-point action of `S4`.

This file records that action-independent consequence at the exact source
interface used by T1.  It does not classify an arbitrary six-point action as
`S4`; the affine exceptional-cell classifier supplies that finite structural
identification separately.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

open Equiv

/-- A retained width-six action whose abstract group is `S4`.  No choice of
the six-point permutation representation is made. -/
structure PreE7AbstractS4Source (i : PreE7NonPairActionClass 6) : Type where
  equiv : preE7NonPairAction 6 i ≃* Perm (Fin 4)

namespace PreE7AbstractS4Source

variable {i : PreE7NonPairActionClass 6} (S : PreE7AbstractS4Source i)

/-- The natural three-point quotient is a comparator for every nonbottom
normal quotient of an abstract `S4` target. -/
def model : PreE7NormalComparatorModel 6 i where
  G := Perm (Fin 4)
  equiv := S.equiv
  index := Unit
  R := Perm (Fin 3)
  degree := 3
  action := MonoidHom.id _
  action_injective := Function.injective_id
  proj := fun _ => NaturalS4.pairing
  proj_surjective := fun _ => NaturalS4.pairing_surjective
  normal_cover := fun N hN hNb => by
    haveI := hN
    refine ⟨(), ?_⟩
    rw [NaturalS4.ker_pairing]
    exact le_of_minimal_selfCentralizing NaturalS4.klein
      NaturalS4.klein_minimal NaturalS4.klein_selfCentralizing N hNb
  tailSlope := 1 / 4
  tailConstant := 2 * Nat.card (Perm (Fin 4) ≃* Perm (Fin 4))
  tailConstant_nonneg := by positivity
  tail := fun _ J => NaturalS4.epi_card_le J
  comparator_window := by
    norm_num [preE7CharacterRho, evenWidth, halfDegree]
  tail_window := by
    norm_num [preE7CharacterWindow, preE7CharacterRho, halfDegree]

private theorem aut_tail_le :
    (2 : ℝ) * Nat.card (Perm (Fin 4) ≃* Perm (Fin 4)) ≤
      (2 : ℝ) ^ (144 : ℝ) := by
  let G := Perm (Fin 4)
  have h : Nat.card (G ≃* G) ≤ 24 ^ 24 := by
    have hraw := mulEquiv_card_le_card_pow_card G
    calc
      Nat.card (G ≃* G) ≤ Nat.card G ^ Nat.card G := hraw
      _ = 24 ^ 24 := by
        congr 1 <;> rw [Nat.card_perm, Nat.card_fin] <;> norm_num
  have hnat : 2 * Nat.card (Perm (Fin 4) ≃* Perm (Fin 4)) ≤ 2 ^ 144 :=
    (Nat.mul_le_mul_left 2 h).trans (by norm_num)
  exact_mod_cast hnat

/-- The complete additive numerical package at the actual ambient width six.
The larger width only improves both windows from the natural width-four row. -/
noncomputable def numericalData :
    PreE7SmallAdditiveNumericalData .s4 6 i := by
  let M := S.model
  apply M.numericalData .s4
  · intro b
    calc
      (Nat.card {N : Subgroup (preE7NonPairAction 6 i) // N.Normal} : ℝ) ≤
          (2 : ℝ) ^ (Nat.card M.G : ℝ) :=
        M.normalAxis_card_cast_le_modelRpow
      _ = (2 : ℝ) ^ (24 : ℝ) := by
        have hcard : Nat.card M.G = 24 := by
          change Nat.card (Perm (Fin 4)) = 24
          rw [Nat.card_perm, Nat.card_fin]
          norm_num
        congr 1
        exact_mod_cast hcard
      _ ≤ (2 : ℝ) ^ (16 * (6 : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        norm_num
      _ ≤ _ := two_rpow_sixteen_width_le_menuMass (w := 6) (by norm_num) b
  · intro b
    change (2 : ℝ) * Nat.card (Perm (Fin 4) ≃* Perm (Fin 4)) ≤ _
    calc
      _ ≤ (2 : ℝ) ^ (144 : ℝ) := aut_tail_le
      _ ≤ (2 : ℝ) ^ (36 * (6 : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        norm_num
      _ ≤ _ := two_rpow_thirtySix_width_le_menuMass (w := 6) (by norm_num) b

/-- An abstract width-six `S4` action enters the concrete owner sum used by
the final T1 exhaustion. -/
noncomputable def toRankTailOwnerSource :
    PreE7RankTailOwnerSourceData 6 i :=
  .ordinary .s4 (.small S.numericalData)

end PreE7AbstractS4Source

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
