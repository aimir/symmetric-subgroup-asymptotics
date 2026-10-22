import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4StabilizerAction
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4AutomorphismCoordinates
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4HammingDirectionGroup

/-! The ACTUAL projective-D4 root-plane stabilizer has a constructed
three-direction homomorphism, whose kernel has index at most six.
This is a local residue kernel; identifying it with a global natural
geometry stabilizer is deliberately not asserted here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexTrialityD2Coordinates
open CFSGOrthogonalDIndexTrialityD4HammingEdges
variable (K : Type) [Field K] [Finite K]

local instance trialityD4LocalDirectionRootPointsNontrivial : Nontrivial (RootPoints K) :=
  rootPoints_nontrivial K

local instance trialityD4LocalDirectionRulingNontrivial : Nontrivial (RulingParameters K) := by
  have hc := rulingParameter_card K
  letI : Finite (RulingParameters K) := Nat.finite_of_card_ne_zero (by rw [hc]; omega)
  apply Finite.one_lt_card_iff_nontrivial.mp
  rw [hc]
  have hp : 0 < Nat.card K := Nat.card_pos
  omega

def originalResidueBase : OriginalResidueCoordinates K :=
  fun i => Classical.choice (inferInstance : Nonempty (OriginalResidueFamily K i))

variable (p : ℕ) [Fact p.Prime] [CharP K p]

def rootStabilizerCoordinatesHom : originalRootStabilizer K p →*
    Equiv.Perm (OriginalResidueCoordinates K) :=
  (((neighborTwinQuotientEquiv K).trans
    (tripleEquiv (RootPoints K) (RulingParameters K) (RulingParameters K))).permCongrHom.toMonoidHom).comp
      (rootStabilizerTwinHom K p)

theorem rootStabilizerCoordinatesHom_apply (f : originalRootStabilizer K p) :
    rootStabilizerCoordinatesHom K p f =
      originalResidueCoordinatePermutation K p f.val (originalRootStabilizer_fix K p f) := by
  apply Equiv.ext
  intro x
  rfl

def rootStabilizerHammingHom : originalRootStabilizer K p →*
    hammingAut (D := OriginalResidueFamily K) where
  toFun f := ⟨rootStabilizerCoordinatesHom K p f, by
    rw [rootStabilizerCoordinatesHom_apply]
    exact originalResidueCoordinatePermutation_closed K p f.val (originalRootStabilizer_fix K p f)⟩
  map_one' := Subtype.ext ((rootStabilizerCoordinatesHom K p).map_one)
  map_mul' f g := Subtype.ext ((rootStabilizerCoordinatesHom K p).map_mul f g)

def rootStabilizerDirectionHom : originalRootStabilizer K p →* Equiv.Perm (Fin 3) :=
  (directionHom (originalResidueBase K)).comp (rootStabilizerHammingHom K p)

theorem rootStabilizer_direction_kernel_index_le_six :
    (rootStabilizerDirectionHom K p).ker.index ≤ 6 := by
  have hh : (rootStabilizerDirectionHom K p).ker.index ≤ Nat.card (Equiv.Perm (Fin 3)) := by
    change Nat.card (originalRootStabilizer K p ⧸ (rootStabilizerDirectionHom K p).ker) ≤ _
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (rootStabilizerDirectionHom K p)).toEquiv]
    exact Nat.card_le_card_of_injective
      (fun g : (rootStabilizerDirectionHom K p).range => g.val) Subtype.val_injective
  norm_num [Nat.card_eq_fintype_card, Fintype.card_perm] at hh
  exact hh

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
