import SymmetricSubgroupAsymptotics.CFSGTrialityMiddleFixedTensorCardinality
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-! The eight actual cubic norm-curve vectors form a basis of the
literal fixed tensor envelope when the base field has order two.
This uses its proved span and exact dimension, not a representation
recognition or an irreducibility assertion. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityBinaryNormCurveBasis
open Module
open CFSGTrialityMiddleFixedTensorSpan CFSGTrialityMiddleFixedTensorCardinality
open CFSGCubicNormMonomialSeparation

def curve (q : CFSG.PrimePower) (t : K q) : fullEnvelope q :=
  ⟨normCurve q.order t,normCurve_mem_fullEnvelope q t⟩

theorem curve_span_top (q : CFSG.PrimePower) :
    Submodule.span (F q) (Set.range (curve q))=⊤ := by
  let S := Submodule.span (F q) (Set.range (curve q))
  have hr : (fullEnvelope q).subtype '' Set.range (curve q) =
      Set.range (normCurve (K := K q) q.order) := by
    ext c
    constructor
    · rintro ⟨v,⟨t,rfl⟩,rfl⟩
      exact ⟨t,rfl⟩
    · rintro ⟨t,rfl⟩
      exact ⟨curve q t,⟨t,rfl⟩,rfl⟩
  have hmap : S.map (fullEnvelope q).subtype=fullEnvelope q := by
    rw [Submodule.map_span,hr,normCurve_base_span]
  apply top_unique
  intro c _
  have hc : c.val ∈ S.map (fullEnvelope q).subtype := by
    rw [hmap]
    exact c.property
  obtain ⟨d,hd,he⟩ := hc
  have he' : d=c := Subtype.ext he
  exact he' ▸ hd

def curveBasis (q : CFSG.PrimePower) (hq : q.order=2) : Basis (K q) (F q) (fullEnvelope q) := by
  classical
  letI : Fintype (K q) := Fintype.ofFinite (K q)
  apply basisOfTopLeSpanOfCardEqFinrank (curve q)
  · rw [curve_span_top]
  · rw [fullEnvelope_finrank,←Nat.card_eq_fintype_card,
      CFSGTrialityTripleFixedRoots.extension_three_card,hq]
    rfl

theorem curveBasis_apply (q : CFSG.PrimePower) (hq : q.order=2) (t : K q) :
    curveBasis q hq t=curve q t := by
  classical
  simp only [curveBasis,coe_basisOfTopLeSpanOfCardEqFinrank]

end SymmetricSubgroupAsymptotics.CFSGTrialityBinaryNormCurveBasis
