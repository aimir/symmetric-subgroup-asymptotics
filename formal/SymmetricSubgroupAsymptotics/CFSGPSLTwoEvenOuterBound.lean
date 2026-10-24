import SymmetricSubgroupAsymptotics.CFSGPSLTwoOuterBound
import Mathlib.Algebra.CharP.Two

/-! The actual PSL2 torus has no scalar kernel in characteristic two.
Charging this same full torus inside the actual opposed-pair stabilizer
removes the factor two in the outer bound. Both inner alignment and the
faithful torus injection are the previously checked literal ones. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGPSLTwoEvenOuterBound
open CFSGPSLTwoRootCoordinates CFSGPSLTwoGeometry CFSGPSLTwoPairRestriction
open CFSGOuterCardinalityAlignment PrimitiveSocleRawStructure
variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem torus_kernel_eq_bot (hchar : ringChar F=2) :
    (projectiveTorusHom (F:=F)).ker=⊥ := by
  apply bot_unique
  intro c hc
  apply Subgroup.mem_bot.mpr
  apply Units.ext
  have hs := torus_kernel_square_one c hc
  rcases sq_eq_one_iff.mp hs with h | h
  · exact h
  · exact h.trans (neg_one_eq_one_iff.mpr hchar)

theorem pairTorus_card_eq_units (hchar : ringChar F=2) :
    Nat.card (pairTorus (F:=F))=Nat.card Fˣ := by
  have hc := (projectiveTorusHom (F:=F)).ker.card_mul_index
  rw [Subgroup.index_ker] at hc
  change Nat.card (projectiveTorusHom (F:=F)).ker*Nat.card (pairTorus (F:=F))=
    Nat.card Fˣ at hc
  have hk : Nat.card (projectiveTorusHom (F:=F)).ker=1 :=
    Subgroup.card_eq_one.mpr (torus_kernel_eq_bot hchar)
  rw [hk,one_mul] at hc
  exact hc

theorem outer_card_le (hchar : ringChar F=2) :
    Nat.card (Outer (PSL (F:=F)))≤Nat.card (F ≃+* F) := by
  apply outer_card_le_of_aligned_bound (pairStabilizer (F:=F)) (pairTorus (F:=F))
    (d:=Nat.card (F ≃+* F))
  · intro f
    obtain ⟨g,hU,hO,_⟩ := exists_inner_fix_opposite_pair f
    exact ⟨g,hU,hO⟩
  · exact pairTorus_conj_mem_pair
  · exact inner_pairTorus_injective
  · simpa only [pairTorus_card_eq_units hchar] using (pairStabilizer_card_le (F:=F))

theorem typeA_rank_one_outer_card (q : CFSG.PrimePower) (hp : q.prime=2) :
    Nat.card (Outer (CFSG.Models.A 1 q))≤q.exponent := by
  have hc : ringChar q.Field=2 := (ringChar.eq q.Field q.prime).trans hp
  change Nat.card (Outer (PSL (F:=q.Field)))≤q.exponent
  simpa only [CFSGFiniteFieldAutomorphisms.primePower_card_ringAut q] using
    (outer_card_le (F:=q.Field) hc)

end SymmetricSubgroupAsymptotics.CFSGPSLTwoEvenOuterBound
