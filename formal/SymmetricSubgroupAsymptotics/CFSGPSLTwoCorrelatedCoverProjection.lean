import SymmetricSubgroupAsymptotics.CFSGPSLTwoCorrelatedCoverMaskRepresentatives
import SymmetricSubgroupAsymptotics.CFSGPSLTwoProductBorelOrbitLabels

/-! The original correlated cover maps equivariantly to the actual
product of PSL2/Borel cosets. Its subset label is well-defined on H-cosets. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGPSLTwoCorrelatedCoverProjection
open CFSGPSLTwoGeometry CFSGPSLTwoRootCoordinates CFSGPSLTwoProductTorusCover
open CFSGPSLTwoBorelTwoOrbits
variable {F J : Type*} [Field F]

abbrev Cover (H : Subgroup (J → projectiveBorel (F:=F))) :=
  (J → PSL (F:=F)) ⧸ H.map borelPowerHom

instance coverAction (H : Subgroup (J → projectiveBorel (F:=F))) :
    MulAction (J → projectiveBorel (F:=F)) (Cover H) :=
  MulAction.compHom (Cover H) borelPowerHom

def projection (H : Subgroup (J → projectiveBorel (F:=F))) : Cover H → (J → Points (F:=F)) :=
  Quotient.lift (fun g i => QuotientGroup.mk (g i)) (by
    intro g k hgk
    funext i
    apply QuotientGroup.eq.mpr
    have hm : g⁻¹*k ∈ H.map borelPowerHom := QuotientGroup.leftRel_apply.mp hgk
    obtain ⟨b,hb,hbe⟩ := hm
    have he : (b i).val=(g i)⁻¹*k i := congrFun hbe i
    rw [←he]
    exact (b i).property)

theorem projection_mk (H : Subgroup (J → projectiveBorel (F:=F))) (g : J → PSL (F:=F)) :
    projection H (QuotientGroup.mk g) = fun i => QuotientGroup.mk (g i) := rfl

theorem projection_equivariant (H : Subgroup (J → projectiveBorel (F:=F)))
    (b : J → projectiveBorel (F:=F)) (q : Cover H) :
    projection H (b • q) = b • projection H q := by
  induction q using Quotient.inductionOn' with
  | h g => rfl

def label (H : Subgroup (J → projectiveBorel (F:=F))) (q : Cover H) : Set J :=
  {i | projection H q i ≠ base}

theorem label_invariant (H : Subgroup (J → projectiveBorel (F:=F)))
    (b : J → projectiveBorel (F:=F)) (q : Cover H) : label H (b • q) = label H q := by
  ext i
  change projection H (b • q) i ≠ base ↔ projection H q i ≠ base
  rw [projection_equivariant]
  change (b i) • projection H q i ≠ base ↔ projection H q i ≠ base
  constructor
  · intro hh he
    exact hh (he ▸ borel_fixes_base (b i))
  · intro hh he
    have h := congrArg (fun z : Points (F:=F) => (b i)⁻¹ • z) he
    dsimp only at h
    rw [inv_smul_smul,borel_fixes_base] at h
    exact hh h

theorem label_mask (H : Subgroup (J → projectiveBorel (F:=F))) (s : Set J) :
    label H (QuotientGroup.mk (weylMask (F:=F) s)) = s := by
  ext i
  by_cases hi : i ∈ s
  · simpa only [label,Set.mem_setOf_eq,projection_mk,weylMask,if_pos hi,
      opposite,hi,iff_true] using opposite_ne_base (F:=F)
  · simp [label,projection_mk,weylMask,hi,base]

end SymmetricSubgroupAsymptotics.CFSGPSLTwoCorrelatedCoverProjection
