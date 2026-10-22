import SymmetricSubgroupAsymptotics.CFSGTransitiveTwoGroupCentralMatching
import SymmetricSubgroupAsymptotics.CFSGInvolutionPairFlipGroup
import SymmetricSubgroupAsymptotics.CFSGTwoGroupTranspositionMatching

/-! The normalizer of an actual transitive symmetric Sylow two-subgroup
preserves an actual fixed-point-free matching. Its individual pair flips
are proved to belong to that same Sylow subgroup by maximality. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGTransitiveSymmetricSylowMatching
open Equiv MulAction

theorem exists_invariant_matching
    {X : Type*} [Finite X] [DecidableEq X] [Nontrivial X]
    (P : Sylow 2 (Perm X)) [IsPretransitive P X] :
    ∃ t : Perm X, Function.Involutive t ∧ (∀ x, t x ≠ x) ∧
      (∀ x, Equiv.swap x (t x) ∈ P) ∧
      ∀ g ∈ Subgroup.normalizer (P : Set (Perm X)), ∀ x, g (t x) = t (g x) := by
  letI : Nontrivial P := by
    obtain ⟨x, y, hxy⟩ := exists_pair_ne X
    obtain ⟨g, hg⟩ := exists_smul_eq P x y
    refine ⟨⟨g, 1, ?_⟩⟩
    intro h
    subst g
    exact hxy (by simpa only [one_smul] using hg)
  obtain ⟨z, hz, hsq, hfree⟩ :=
    CFSGTransitiveTwoGroupCentralMatching.exists_fixed_point_free_involution
      (X := X) P.isPGroup'
  let t : Perm X := z.val
  have ht : Function.Involutive t := by
    intro x
    have he := congrArg (fun g : P => (g.val : Perm X) x) hsq
    simpa only [pow_two, Subgroup.coe_mul, Subgroup.coe_one, Perm.mul_apply,
      Perm.one_apply] using he
  have hc : (P : Subgroup (Perm X)) ≤ Subgroup.centralizer ({t} : Set (Perm X)) := by
    intro g hg
    apply Subgroup.mem_centralizer_iff.mpr
    intro u hu
    have hu' : u = t := Set.mem_singleton_iff.mp hu
    subst u
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨g, hg⟩)).symm
  have hflips := CFSGInvolutionPairFlipGroup.flips_le_sylow t ht P hc
  have hflip : ∀ x, Equiv.swap x (t x) ∈ P := fun x =>
    hflips (CFSGInvolutionPairFlipGroup.swap_mem t ht x)
  refine ⟨t, ht, hfree, hflip, ?_⟩
  intro g hg x
  exact CFSGTwoGroupTranspositionMatching.normalizer_preserves_pairing
    P P.isPGroup' t hfree hflip g hg x

end SymmetricSubgroupAsymptotics.CFSGTransitiveSymmetricSylowMatching
