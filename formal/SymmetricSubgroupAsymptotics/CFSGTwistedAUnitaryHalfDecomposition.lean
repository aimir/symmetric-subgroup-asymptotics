import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryOppositeSpace

/-! The actual signed-unitary coordinate space is the sum of its two
singular coordinate halves and the possible middle coordinate. In even
vector dimension the two halves already span the whole space. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates

def unitaryStandardProjection (q : CFSG.PrimePower) (r : ℕ)
    (x : Fin (r + 1) → q.Extension 2) : Fin (r + 1) → q.Extension 2 :=
  fun i => if r < 2 * i.val + 1 then 0 else x i

def unitaryCentralCoordinateProjection (q : CFSG.PrimePower) (r : ℕ)
    (x : Fin (r + 1) → q.Extension 2) : Fin (r + 1) → q.Extension 2 :=
  fun i => if 2 * i.val = r then x i else 0

theorem unitaryStandardProjection_mem (q : CFSG.PrimePower) (r : ℕ)
    (x : Fin (r + 1) → q.Extension 2) :
    unitaryStandardProjection q r x ∈ unitaryStandardSingularSpace q r := by
  intro i hi
  exact if_pos hi

theorem unitary_half_decomposition (q : CFSG.PrimePower) (r : ℕ)
    (x : Fin (r + 1) → q.Extension 2) :
    x = unitaryStandardProjection q r x + unitaryOppositeProjection q r x +
      unitaryCentralCoordinateProjection q r x := by
  funext i
  have hv : i.rev.val = r - i.val := by rw [Fin.val_rev]; omega
  have hib := i.isLt
  by_cases hi : r < 2 * i.val + 1
  · by_cases hj : r < 2 * i.rev.val + 1
    · have hm : 2 * i.val = r := by omega
      simp only [unitaryStandardProjection, unitaryOppositeProjection,
        unitaryCentralCoordinateProjection, Pi.add_apply, if_pos hi, if_pos hj, if_pos hm, zero_add]
    · have hm : ¬2 * i.val = r := by omega
      simp only [unitaryStandardProjection, unitaryOppositeProjection,
        unitaryCentralCoordinateProjection, Pi.add_apply, if_pos hi, if_neg hj, if_neg hm, zero_add, add_zero]
  · have hj : r < 2 * i.rev.val + 1 := by omega
    have hm : ¬2 * i.val = r := by omega
    simp only [unitaryStandardProjection, unitaryOppositeProjection,
      unitaryCentralCoordinateProjection, Pi.add_apply, if_neg hi, if_pos hj, if_neg hm, add_zero]

theorem unitaryCentralCoordinateProjection_eq_zero_of_odd (q : CFSG.PrimePower) (r : ℕ)
    (hr : Odd r) (x : Fin (r + 1) → q.Extension 2) :
    unitaryCentralCoordinateProjection q r x = 0 := by
  obtain ⟨k, hk⟩ := hr
  funext i
  have hn : ¬2 * i.val = r := by omega
  exact if_neg hn

theorem unitaryStandard_opposite_sup_eq_top_of_odd (q : CFSG.PrimePower) (r : ℕ)
    (hr : Odd r) :
    unitaryStandardSingularSpace q r ⊔ unitaryOppositeSingularSpace q r = ⊤ := by
  apply top_unique
  intro x _
  have hd := unitary_half_decomposition q r x
  rw [unitaryCentralCoordinateProjection_eq_zero_of_odd q r hr x, add_zero] at hd
  rw [hd]
  exact Submodule.add_mem_sup (unitaryStandardProjection_mem q r x)
    (unitaryOppositeProjection_mem q r x)

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
