import SymmetricSubgroupAsymptotics.CFSGCubicNormCurveSpan
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! A full span over an extension field gives a lower bound on the
dimension of the span over the base field. This does not assume that
the ambient extension-field vector space has the same base dimension. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGScalarRestrictionSpanRank

theorem finrank_le_base_span (F K V T : Type*)
    [Field F] [Field K] [Algebra F K] [AddCommGroup V]
    [Module K V] [Module F V] [IsScalarTower F K V] [Finite V]
    (v : T → V) (hspan : Submodule.span K (Set.range v) = ⊤) :
    Module.finrank K V ≤ Module.finrank F (Submodule.span F (Set.range v)) := by
  classical
  obtain ⟨b, hb, hsp, hli⟩ := exists_linearIndependent K (Set.range v)
  letI : Fintype b := Fintype.ofFinite _
  have hB : Submodule.span K (Set.range ((↑) : b → V)) = ⊤ := by
    simpa only [Subtype.range_coe_subtype, Set.setOf_mem_eq] using hsp.trans hspan
  let B : Module.Basis b K V := Module.Basis.mk hli hB.ge
  let P := Submodule.span F (Set.range v)
  let w : b → P := fun x => ⟨x.val, Submodule.subset_span (hb x.property)⟩
  have hw : LinearIndependent F w :=
    LinearIndependent.of_comp P.subtype (hli.restrict_scalars' F)
  rw [Module.finrank_eq_card_basis B]
  exact hw.fintype_card_le_finrank

theorem base_span_eq_of_dimension_bound (F K V T : Type*)
    [Field F] [Field K] [Algebra F K] [AddCommGroup V]
    [Module K V] [Module F V] [IsScalarTower F K V] [Finite V]
    (v : T → V) (hspan : Submodule.span K (Set.range v) = ⊤)
    (W : Submodule F V) (hW : ∀ t, v t ∈ W)
    (hdim : Module.finrank F W ≤ Module.finrank K V) :
    Submodule.span F (Set.range v) = W := by
  apply Submodule.eq_of_le_of_finrank_le
  · exact Submodule.span_le.mpr (by rintro _ ⟨t, rfl⟩; exact hW t)
  · exact hdim.trans (finrank_le_base_span F K V T v hspan)

end SymmetricSubgroupAsymptotics.CFSGScalarRestrictionSpanRank
