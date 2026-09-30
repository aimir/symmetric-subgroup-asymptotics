import SymmetricSubgroupAsymptotics.BinaryDegree16SplitFrontier
import SymmetricSubgroupAsymptotics.BinaryDegreeEightElementaryTopClassification

/-!
# Exact top-axis classification of the degree-sixteen split residual

The retained two-orbit statement in `SplitResidual` rules out the transitive
elementary axis of `8T9`.  Consequently the abstract residual carries, under
one ambient permutation of its eight pair labels, exactly one of the three
literal top-and-axis pairs selected by the complete finite registries.
-/

set_option autoImplicit false
noncomputable section
open scoped Pointwise

namespace SymmetricSubgroupAsymptotics.BinaryDegree16SplitTopClassification

open SymmetricSubgroupAsymptotics
open BinaryDegree16SplitFrontier
open BinaryDegreeEightElementaryTopClassification

/-- Two actual orbits of a subgroup of a permutation group exclude
transitivity of its ambient permutation image. -/
private theorem not_transitive_of_orbit_card_two
    (T : Subgroup (Equiv.Perm (Fin 8))) (H : Subgroup T)
    (hclasses : Nat.card (MulAction.orbitRel.Quotient H (Fin 8))=2) :
    ¬PermutationSubgroupTransitive (H.map T.subtype) := by
  intro htrans
  letI : MulAction.IsPretransitive H (Fin 8) := ⟨fun x y => by
    obtain ⟨g,hg,hxy⟩ := htrans x y
    obtain ⟨h,hh,rfl⟩ := hg
    exact ⟨⟨h,hh⟩,hxy⟩⟩
  have hsub : Subsingleton (MulAction.orbitRel.Quotient H (Fin 8)) :=
    (MulAction.pretransitive_iff_subsingleton_quotient H (Fin 8)).mp inferInstance
  have hnonempty : Nonempty (MulAction.orbitRel.Quotient H (Fin 8)) :=
    ⟨Quotient.mk'' (0 : Fin 8)⟩
  have hone : Nat.card (MulAction.orbitRel.Quotient H (Fin 8))=1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨hsub,hnonempty⟩
  omega

/-- Every surviving split residual retains an exact conjugate of one of the
three literal degree-eight top-and-axis pairs. -/
theorem residual_exact_axis
    {U : Subgroup (Equiv.Perm (Fin 16))}
    [MulAction.IsPretransitive U (Fin 16)] (hU : IsPGroup 2 U)
    {N : Subgroup U} [N.Normal]
    (R : SplitResidual U N) :
    ExactAxisCovered R.frame.top.range
      (R.frame.sectionTopRepresentation N).ker := by
  letI : MulAction.IsPretransitive R.frame.top.range (Fin 8) :=
    R.frame.top_pretransitive
  have htrans : PermutationSubgroupTransitive R.frame.top.range := by
    intro x y
    obtain ⟨g,hxy⟩ := MulAction.exists_smul_eq R.frame.top.range x y
    exact ⟨g,g.property,hxy⟩
  obtain ⟨_,_,_,⟨data⟩,hclasses,_,_⟩ := R.residual
  obtain ⟨_,_,_,hpow,_,_⟩ :=
    R.frame.eight_rank_two_original_orders N hU (Nat.card_fin 8) R.residual
  exact complete_exact_axis R.frame.top.range (R.frame.top_isPGroup hU)
    htrans (R.frame.sectionTopRepresentation N).ker R.top_order
    data.kernel_index hpow
    (not_transitive_of_orbit_card_two R.frame.top.range
      (R.frame.sectionTopRepresentation N).ker hclasses)

end SymmetricSubgroupAsymptotics.BinaryDegree16SplitTopClassification
