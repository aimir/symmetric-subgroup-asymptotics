import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryStarPoints
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryIntrinsicRootStars

/-! All literal points of the first singular two-plane, together with
an exact binding to the ORIGINAL projective point-root labels. These
are the same point and subgroup carriers used by the faithful Aut action. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGSerreOrdinaryTwists

def starVectorLinear (q : CFSG.PrimePower) (s : ℕ) :
    (Fin 2 → q.Extension 2) →ₗ[q.Extension 2] (Fin (s + 4) → q.Extension 2) where
  toFun := starVector q s
  map_add' v w := by
    ext k
    simp only [starVector, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  map_smul' a v := by
    ext k
    simp only [starVector, Pi.add_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

def starPlane (q : CFSG.PrimePower) (s : ℕ) :
    Submodule (q.Extension 2) (Fin (s + 4) → q.Extension 2) :=
  (starVectorLinear q s).range

theorem starPlane_finrank (q : CFSG.PrimePower) (s : ℕ) :
    Module.finrank (q.Extension 2) (starPlane q s) = 2 := by
  simpa only [starPlane, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using
    LinearMap.finrank_range_of_inj (f := starVectorLinear q s) (starVector_injective q s)

theorem starPlane_pair_zero (q : CFSG.PrimePower) (s : ℕ)
    (x y : Fin (s + 4) → q.Extension 2) (hx : x ∈ starPlane q s) (hy : y ∈ starPlane q s) :
    unitaryNaturalPair q (s + 3) x y = 0 := by
  obtain ⟨v, rfl⟩ := hx
  obtain ⟨w, rfl⟩ := hy
  exact starVector_pair_zero q s v w

theorem starPoint_le_starPlane (q : CFSG.PrimePower) (s : ℕ)
    (v : Fin 2 → q.Extension 2) (hv : v ≠ 0) : (starPoint q s v hv).val ≤ starPlane q s := by
  apply (Submodule.span_singleton_le_iff_mem _ _).mpr
  exact ⟨v, rfl⟩

theorem exists_starPoint_of_le (q : CFSG.PrimePower) (s : ℕ)
    (P : unitarySingularPoints q s) (hP : P.val ≤ starPlane q s) :
    ∃ (v : Fin 2 → q.Extension 2) (hv : v ≠ 0), starPoint q s v hv = P := by
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (Submodule.one_le_finrank_iff.mp (by rw [P.property.1]))
  obtain ⟨v, hvw⟩ := hP hw
  have hv : v ≠ 0 := by
    intro h
    apply hw0
    rw [← hvw, h, map_zero]
  have he : (q.Extension 2) ∙ w = P.val :=
    Submodule.eq_of_le_of_finrank_le ((Submodule.span_singleton_le_iff_mem _ _).mpr hw)
      (by rw [P.property.1, finrank_span_singleton hw0])
  refine ⟨v, hv, Subtype.ext ?_⟩
  change (q.Extension 2) ∙ starVector q s v = P.val
  change starVector q s v = w at hvw
  rw [hvw]
  exact he

theorem unitaryPointRoot_starPoint_representative (q : CFSG.PrimePower) (s : ℕ)
    (v : Fin 2 → q.Extension 2) (hv : v ≠ 0) (g : naturalFixed (s + 3) q)
    (c : q.Extension 2) (hc : c ≠ 0)
    (hgv : unitaryCentralVector q s g = c • starVector q s v) :
    unitaryPointRoot q s (starPoint q s v hv) =
      conjugateProjectiveCentralRootLine q s (unitaryProjectiveCover q s g) := by
  apply unitaryCentralPointLabel_representative
  rw [conjugateCentralPoint_eq_span]
  change (q.Extension 2) ∙ unitaryCentralVector q s g = (q.Extension 2) ∙ starVector q s v
  rw [hgv]
  exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hc) _

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
