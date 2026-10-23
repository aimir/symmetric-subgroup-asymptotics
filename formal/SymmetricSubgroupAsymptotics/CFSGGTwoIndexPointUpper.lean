import SymmetricSubgroupAsymptotics.CFSGGTwoSingularPointAction
import SymmetricSubgroupAsymptotics.CFSGGTwoNaturalProjectiveModel
import SymmetricSubgroupAsymptotics.CFSGQuotientOrbitIndex
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport

/-! A moved singular ray gives a proper subgroup of the same original
projective G2 model. Its actual orbit injects into the counted singular
ray carrier, giving ell < 3q^5 without a group order formula. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoIndexPointUpper
open CFSGGTwoSerreMatrices CFSGGTwoSingularPointCount CFSGGTwoSingularPointAction
open CFSGGTwoNaturalProjectiveModel PrimitiveSocleRawStructure CFSG.Models.Chevalley
variable (K : Type) [Field K] [Finite K]

theorem native_leastProperIndex_lt (hq : 3 ≤ Nat.card K) (ell : ℕ)
    (hell : LeastProperIndex (naturalGroup K) ell) : ell < 3 * Nat.card K ^ 5 := by
  letI := pointAction K
  let O := MulAction.orbit (naturalGroup K) (movedPoint K)
  let encode : O → singularPoints K := fun y => ⟨y.val, by
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp y.property
    rw [←hg]
    exact point_preserves_singular K g (movedPoint K) (movedPoint_singular K)⟩
  have hinj : Function.Injective encode := by
    intro x y he
    apply Subtype.ext
    have hv := congrArg (fun p : singularPoints K => p.val) he
    change x.val = y.val at hv
    exact hv
  obtain ⟨H, hH, hindex⟩ :=
    CFSGQuotientActionIndexUpper.exists_proper_subgroup_of_moved_point_orbit
      (MonoidHom.id (naturalGroup K)) Function.surjective_id (movedPoint K)
      (by
        intro g hg
        change g = 1 at hg
        rw [hg]
        exact one_smul _ _)
      (naturalRoot K false 1 1) (long_root_moves_point K)
  calc
    ell ≤ H.index := hell.2 H hH
    _ = Nat.card O := hindex
    _ ≤ Nat.card (singularPoints K) := Nat.card_le_card_of_injective encode hinj
    _ < 3 * Nat.card K ^ 5 := singularPoints_card_lt K hq

theorem original_leastProperIndex_lt (hq : 3 ≤ Nat.card K)
    [IsSimpleGroup (Projective CartanMatrix.G₂ K)] (ell : ℕ)
    (hell : LeastProperIndex (Projective CartanMatrix.G₂ K) ell) :
    ell < 3 * Nat.card K ^ 5 :=
  native_leastProperIndex_lt K hq ell
    (CFSGReduction.leastProperIndex_of_mulEquiv (naturalEquivOriginal K hq).symm ell hell)

end SymmetricSubgroupAsymptotics.CFSGGTwoIndexPointUpper
