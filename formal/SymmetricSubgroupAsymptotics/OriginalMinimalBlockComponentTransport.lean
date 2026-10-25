import SymmetricSubgroupAsymptotics.OriginalMinimalBlock

/-! The actual minimal-block cover is transported to EVERY original
fibre. Only component primitivity is obtained; no claim of primitive
top action is made. Literal fibre cardinalities are also transported. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.OriginalMinimalBlock

variable {A Ω : Type} [Group A] [MulAction A Ω] [MulAction.IsPretransitive A Ω]
    {ω₀ : Ω} (D : OriginalMinimalBlock (A := A) ω₀)

def fibreEquivAt (x : D.Points) : D.Fibre ≃ originalBlockFibre D.map x := by
  let g : A := Classical.choose (MulAction.exists_smul_eq A D.base x)
  have hg : g • D.base = x := Classical.choose_spec (MulAction.exists_smul_eq A D.base x)
  exact
    { toFun := fun u => ⟨g • u.val,by rw [D.map_equivariant,u.property,hg]⟩
      invFun := fun u => ⟨g⁻¹ • u.val,by
        rw [D.map_equivariant,u.property,← hg,inv_smul_smul]⟩
      left_inv := fun u => Subtype.ext (inv_smul_smul g u.val)
      right_inv := fun u => Subtype.ext (smul_inv_smul g u.val) }

theorem fibre_card_at (x : D.Points) :
    Nat.card (originalBlockFibre D.map x) = Nat.card D.Fibre :=
  (Nat.card_congr (D.fibreEquivAt x)).symm

theorem component_preprimitive_at (x : D.Points) :
    MulAction.IsPreprimitive (originalBlockComponent D.map D.map_equivariant x)
      (originalBlockFibre D.map x) := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq A D.base x
  have hbase : MulAction.stabilizer A ω₀ ⋖ MulAction.stabilizer A D.base := by
    change MulAction.stabilizer A ω₀ ⋖
      MulAction.stabilizer A ((1 : A) : A ⧸ D.subgroup)
    rw [MulAction.stabilizer_quotient]
    exact D.covers
  have hc : MulAction.stabilizer A (g • ω₀) ⋖ MulAction.stabilizer A x := by
    rw [← hg,MulAction.stabilizer_smul_eq_stabilizer_map_conj,
      MulAction.stabilizer_smul_eq_stabilizer_map_conj]
    exact (apply_covBy_apply_iff (MulAut.conj g).mapSubgroup).mpr hbase
  apply originalBlockComponent_preprimitive D.map D.map_equivariant x (g • ω₀) _ hc
  rw [D.map_equivariant,D.map_base,hg]

end SymmetricSubgroupAsymptotics.OriginalMinimalBlock
