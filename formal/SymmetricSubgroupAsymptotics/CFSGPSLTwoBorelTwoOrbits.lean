import SymmetricSubgroupAsymptotics.CFSGPSLTwoCosetCardinality
import Mathlib.Data.Fintype.Card

/-! The two actual Borel orbits on the original PSL2/Borel cosets. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGPSLTwoBorelTwoOrbits
open CFSGPSLTwoGeometry CFSGPSLTwoRootCoordinates
variable {F : Type*} [Field F]

def base : Points (F:=F) := QuotientGroup.mk (1 : PSL (F:=F))
def opposite : Points (F:=F) := QuotientGroup.mk (projectiveWeyl (F:=F))

theorem borel_fixes_base (b : projectiveBorel (F:=F)) : b • base (F:=F) = base := by
  change (QuotientGroup.mk (b.val*1) : Points (F:=F)) = QuotientGroup.mk 1
  apply QuotientGroup.eq.mpr
  simpa only [mul_one] using (projectiveBorel (F:=F)).inv_mem b.property

theorem opposite_ne_base : opposite (F:=F) ≠ base := by
  intro he
  have hh : (projectiveWeyl (F:=F))⁻¹ ∈ projectiveBorel (F:=F) := by
    simpa only [mul_one] using QuotientGroup.eq.mp he
  apply projectiveWeyl_not_mem_borel (F:=F)
  simpa only [inv_inv] using (projectiveBorel (F:=F)).inv_mem hh

theorem base_or_opposite_orbit (q : Points (F:=F)) :
    q = base ∨ q ∈ MulAction.orbit (projectiveBorel (F:=F)) (opposite (F:=F)) := by
  induction q using Quotient.inductionOn' with
  | h g =>
    rcases two_cells g with hg | ⟨b,u,he⟩
    · left
      apply QuotientGroup.eq.mpr
      simpa only [mul_one] using (projectiveBorel (F:=F)).inv_mem hg
    · right
      apply MulAction.mem_orbit_iff.mpr
      refine ⟨b,?_⟩
      change (QuotientGroup.mk (b.val*projectiveWeyl) : Points (F:=F)) = QuotientGroup.mk g
      apply QuotientGroup.eq.mpr
      rw [he]
      simpa only [inv_mul_cancel_left] using projectiveRoot_le_borel u.property

theorem opposite_orbit_eq_complement :
    MulAction.orbit (projectiveBorel (F:=F)) (opposite (F:=F)) =
      {q : Points (F:=F) | q ≠ base} := by
  ext q
  constructor
  · intro hq he
    obtain ⟨b,hb⟩ := MulAction.mem_orbit_iff.mp hq
    have hh := congrArg (fun z : Points (F:=F) => b⁻¹ • z) (hb.trans he)
    dsimp only at hh
    rw [inv_smul_smul,borel_fixes_base] at hh
    exact opposite_ne_base hh
  · intro hq
    exact (base_or_opposite_orbit q).resolve_left hq

theorem opposite_orbit_card [Finite F] :
    Nat.card (MulAction.orbit (projectiveBorel (F:=F)) (opposite (F:=F))) = Nat.card F := by
  classical
  letI : Fintype (Points (F:=F)) := Fintype.ofFinite _
  letI : Fintype {q : Points (F:=F) // q = base} := Fintype.ofFinite _
  letI : Fintype {q : Points (F:=F) // q ≠ base} := Fintype.ofFinite _
  calc
    _ = Nat.card {q : Points (F:=F) // q ≠ base} :=
      Nat.card_congr (Equiv.setCongr opposite_orbit_eq_complement)
    _ = Nat.card (Points (F:=F)) - 1 := by
      simp only [Nat.card_eq_fintype_card,Fintype.card_subtype_compl,Fintype.card_subtype_eq]
    _ = Nat.card F := by rw [points_card]; omega

end SymmetricSubgroupAsymptotics.CFSGPSLTwoBorelTwoOrbits
