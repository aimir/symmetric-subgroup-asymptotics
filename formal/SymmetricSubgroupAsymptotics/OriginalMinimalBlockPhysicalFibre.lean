import SymmetricSubgroupAsymptotics.OriginalMinimalBlockOfPrimitiveFibre

/-! Identify the canonical coset fibre of a chosen original minimal block
with its original physical equivariant fibre. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [MulAction.IsPretransitive A Ω]
    (b : Ω → X) (hb : ∀ (a : A) (ω : Ω), b (a • ω) = a • b ω)
    (ω₀ : Ω)

include hb in
private theorem physical_stabilizer_le :
    MulAction.stabilizer A ω₀ ≤ MulAction.stabilizer A (b ω₀) := by
  intro a ha
  change a • b ω₀ = b ω₀
  have ha' : a • ω₀ = ω₀ := ha
  rw [← hb,ha']

include hb in
theorem originalTransitiveBlockMap_physical_fibre_iff (ω : Ω) :
    originalTransitiveBlockMap ω₀ (MulAction.stabilizer A (b ω₀)) ω =
      ((1 : A) : A ⧸ MulAction.stabilizer A (b ω₀)) ↔ b ω = b ω₀ := by
  obtain ⟨a,rfl⟩ := MulAction.exists_smul_eq A ω₀ ω
  rw [originalTransitiveBlockMap_smul_base ω₀ _
    (physical_stabilizer_le b hb ω₀),hb]
  rw [QuotientGroup.eq]
  simp only [mul_one,inv_mem_iff]
  rfl

/-- Equality of the chosen stabilizer identifies actual fibres pointwise. -/
def OriginalMinimalBlock.physicalFibreEquiv
    (D : OriginalMinimalBlock (A := A) ω₀)
    (hD : D.subgroup = MulAction.stabilizer A (b ω₀)) :
    D.Fibre ≃ originalBlockFibre b (b ω₀) where
  toFun x := ⟨x.1, by
    apply (originalTransitiveBlockMap_physical_fibre_iff b hb ω₀ x.1).mp
    have hx : originalTransitiveBlockMap ω₀ D.subgroup x.1 =
        ((1 : A) : A ⧸ D.subgroup) := x.2
    rw [hD] at hx
    exact hx⟩
  invFun x := ⟨x.1, by
    have hx := (originalTransitiveBlockMap_physical_fibre_iff b hb ω₀ x.1).mpr x.2
    change originalTransitiveBlockMap ω₀ D.subgroup x.1 = ((1 : A) : A ⧸ D.subgroup)
    rw [hD]
    exact hx⟩
  left_inv _ := rfl
  right_inv _ := rfl

end SymmetricSubgroupAsymptotics
end
