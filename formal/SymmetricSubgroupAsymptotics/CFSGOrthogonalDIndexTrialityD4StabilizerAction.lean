import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4NeighborAutomorphism

/-! Genuine group actions of the original projective-D4 root-plane
stabilizer on its original neighbours and their intrinsic twin quotient.
The stabilizer and both homomorphisms are constructed internally. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexPlaneFamilyAction
variable (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]

def originalRootStabilizer : Subgroup (MulAut (elementaryProjective K 4)) :=
  (MulAction.stabilizer (Equiv.Perm (SingularPlanes K 0)) (originalRootPlane K)).comap
    (singularActionHom K p 0)

theorem originalRootStabilizer_fix (f : originalRootStabilizer K p) :
    singularActionHom K p 0 f.val (originalRootPlane K) = originalRootPlane K := f.property

def rootStabilizerNeighborHom : originalRootStabilizer K p →* Equiv.Perm (Neighbors K) where
  toFun f := originalNeighborPermutation K p f.val (originalRootStabilizer_fix K p f)
  map_one' := by
    apply Equiv.ext
    intro S
    apply Subtype.ext
    change (singularActionHom K p 0 (1 : MulAut (elementaryProjective K 4))
      (neighborAsPlane K S)).val = S.val
    rw [map_one]
    rfl
  map_mul' f g := by
    apply Equiv.ext
    intro S
    apply Subtype.ext
    change (singularActionHom K p 0 (f.val * g.val) (neighborAsPlane K S)).val =
      (singularActionHom K p 0 f.val
        (singularActionHom K p 0 g.val (neighborAsPlane K S))).val
    exact congrArg (fun e : Equiv.Perm (SingularPlanes K 0) => (e (neighborAsPlane K S)).val)
      ((singularActionHom K p 0).map_mul f.val g.val)

def rootStabilizerTwinHom : originalRootStabilizer K p →* Equiv.Perm (NeighborTwinQuotient K) where
  toFun f := originalTwinQuotientPermutation K p f.val (originalRootStabilizer_fix K p f)
  map_one' := by
    apply Equiv.ext
    intro x
    refine Quotient.inductionOn x ?_
    intro S
    change Quotient.mk (neighborTwinSetoid K)
      ((rootStabilizerNeighborHom K p) 1 S) = Quotient.mk (neighborTwinSetoid K) S
    have hh := congrArg (fun e : Equiv.Perm (Neighbors K) => e S)
      ((rootStabilizerNeighborHom K p).map_one)
    exact congrArg (Quotient.mk (neighborTwinSetoid K)) hh
  map_mul' f g := by
    apply Equiv.ext
    intro x
    refine Quotient.inductionOn x ?_
    intro S
    change Quotient.mk (neighborTwinSetoid K)
      ((rootStabilizerNeighborHom K p) (f * g) S) = Quotient.mk (neighborTwinSetoid K)
        ((rootStabilizerNeighborHom K p) f ((rootStabilizerNeighborHom K p) g S))
    exact congrArg (Quotient.mk (neighborTwinSetoid K))
      (congrArg (fun e : Equiv.Perm (Neighbors K) => e S)
        ((rootStabilizerNeighborHom K p).map_mul f g))

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
