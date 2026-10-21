import SymmetricSubgroupAsymptotics.CFSGRankOneSylowAlignment
import SymmetricSubgroupAsymptotics.CFSGSuzukiModelGoodSylow
import SymmetricSubgroupAsymptotics.CFSGSuzukiModelCardinality

/-! Sylow and opposite-Sylow alignment inside the pinned original
Suzuki matrix group. The normalizer equality is in that group, rather
than in the ambient general linear group with its extra scalars. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.CFSGSuzukiSylowAlignment
open CFSGSuzukiUnipotent CFSGSuzukiSylowOfNormalizer CFSGSuzukiGoodSylow
open CFSGSuzukiModelCardinality CFSGSuzukiOppositeIntersection

theorem borelEnvelope_le_normalizer (m : ℕ) :
    borelEnvelope m ≤ Subgroup.normalizer (unipotentSubgroup m : Set (Ambient m)) := by
  rw [borelEnvelope_eq_unipotent_sup_torus]
  exact sup_le Subgroup.le_normalizer (normalizedTorus_normalizes_unipotent m)

theorem modelBorel_le_normalizer (m : ℕ) :
    modelBorel m ≤ Subgroup.normalizer (modelUnipotent m : Set (ActualGroup m)) := by
  intro g hg
  apply (unipotentSubgroup m).le_normalizer_comap
    (CFSG.Models.SuzukiConstruction.subgroup m).subtype
  exact borelEnvelope_le_normalizer m hg

theorem model_normalizer_eq_borel (m : ℕ) :
    Subgroup.normalizer (modelUnipotent m : Set (ActualGroup m))=modelBorel m :=
  le_antisymm (model_normalizer_le_borel m (normalizer_inter_model_le_borel m))
    (modelBorel_le_normalizer m)

def originalSylow (m : ℕ) : Sylow 2 (ActualGroup m) :=
  modelSylow m (normalizer_inter_model_le_borel m)

@[simp] theorem originalSylow_coe (m : ℕ) :
    (originalSylow m : Subgroup (ActualGroup m))=modelUnipotent m := rfl

/-- Every original model automorphism can be adjusted by an original
inner automorphism to preserve both original opposite Sylow subgroups. -/
theorem exists_inner_fix_opposite_pair (m : ℕ) (f : MulAut (ActualGroup m)) :
    ∃ g : ActualGroup m, (MulAut.conj g*f) • originalSylow m=originalSylow m ∧
      (MulAut.conj g*f) • (modelWeyl m • originalSylow m)=
        modelWeyl m • originalSylow m := by
  letI suzukiAlignmentPrimeTwo : Fact (Nat.Prime 2) := ⟨by decide⟩
  exact CFSGRankOneSylowAlignment.exists_inner_fix_pair
    (originalSylow m) (modelBorel m) (modelWeyl m)
    (model_normalizer_eq_borel m).symm
    (fun hw => weyl_not_mem_borel m hw) (actual_model_two_cells m) f

end SymmetricSubgroupAsymptotics.CFSGSuzukiSylowAlignment
