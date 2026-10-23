import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryStarRootRealization

/-! The converse natural containment: every original central root at a
point of the displayed singular two-plane is in the actual shear group.
Both directions use explicit norm-scaled parameters in the SAME fixed
group, rather than a projective or named-group recognition assumption. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUnitaryNaturalRadical
open CFSGSerreOrdinaryTwists CFSGTwistedAUpperUnipotent

theorem conjugateCentralFixed_mem_rootStarGroup (q : CFSG.PrimePower) (s : ℕ)
    (t : q.Extension 2) (ht : t ≠ 0) (htc : t ∈ centralParameters q (s + 1))
    (v : Fin 2 → q.Extension 2) (g : naturalFixed (s + 3) q) (c : q.Extension 2)
    (hgv : unitaryCentralVector q s g = c • starVector q s v)
    (b : q.Extension 2) (hb : Condition q (s + 1) 0 b) :
    g * centralFixed q (s + 1) b hb * g⁻¹ ∈ naturalRootStarGroup q s := by
  have hbf : b ∈ centralParameters q (s + 1) := (centralCondition_iff q (s + 1) b).mp hb
  have hnf : definingFieldAutomorphism q 2 (c * definingFieldAutomorphism q 2 c) =
      c * definingFieldAutomorphism q 2 c := by
    have hcc : definingFieldAutomorphism q 2 (definingFieldAutomorphism q 2 c) = c :=
      extension_two_pow_twice q c
    rw [map_mul, hcc]
    exact mul_comm _ _
  have hbn : b * (c * definingFieldAutomorphism q 2 c) ∈ centralParameters q (s + 1) :=
    star_central_mul_fixed q s b hbf _ hnf
  let a : q.Extension 2 := (b * (c * definingFieldAutomorphism q 2 c)) / t
  have haf : definingFieldAutomorphism q 2 a = a :=
    star_central_div_fixed q s t ht htc ⟨_, hbn⟩
  have hscale : b * (c * definingFieldAutomorphism q 2 c) = t * a := by
    dsimp only [a]
    field_simp [ht]
  have he := starRankOne_eq_conjugate_of_scale q s t htc a haf v g c b hb hgv hscale
  rw [← he]
  exact ⟨Multiplicative.ofAdd (starRankOneParameters q s t htc a haf v), rfl⟩

theorem conjugateRootLine_le_rootStarGroup (q : CFSG.PrimePower) (s : ℕ)
    (t : q.Extension 2) (ht : t ≠ 0) (htc : t ∈ centralParameters q (s + 1))
    (v : Fin 2 → q.Extension 2) (g : naturalFixed (s + 3) q) (c : q.Extension 2)
    (hgv : unitaryCentralVector q s g = c • starVector q s v) :
    conjugateNaturalCentralRootLine q (s + 1) g ≤ naturalRootStarGroup q s := by
  rintro x ⟨y, hy, rfl⟩
  obtain ⟨b, hb, rfl⟩ := (mem_naturalCentralRootLine_iff q (s + 1) y).mp hy
  exact conjugateCentralFixed_mem_rootStarGroup q s t ht htc v g c hgv b hb

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
