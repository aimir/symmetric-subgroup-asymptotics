import SymmetricSubgroupAsymptotics.CFSGTrialityCubicNormSurjectivity

/-! A literal cubic norm intertwining relation forces the fixed-field
map to be the restriction of the cubic-field automorphism. The actual
norm is onto; preserving the fixed field is a conclusion, not an extra
hypothesis on the cubic-field automorphism. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityNormFieldRestriction
open CFSGTrialityNormTorusScalars CFSGTrialityCubicNormSurjectivity CFSGTrialityFixedField

theorem normFieldHom_ringAut_coe (q : CFSG.PrimePower)
    (sigma : q.Extension 3≃+*q.Extension 3) (x : q.Extension 3) :
    sigma ((normFieldHom q x : fixedField q) : q.Extension 3)=
      ((normFieldHom q (sigma x) : fixedField q) : q.Extension 3) := by
  rw [normFieldHom_val,normFieldHom_val,map_pow]

theorem restriction_eq_of_norm_inverse_relation (q : CFSG.PrimePower)
    (sigma : q.Extension 3≃+*q.Extension 3) (tau : fixedField q≃+*fixedField q)
    (hnorm : ∀c:(q.Extension 3)ˣ,
      tau ((normUnits q c : fixedField q)⁻¹)=
        ((normUnits q (Units.map sigma.toMonoidHom c) : (fixedField q)ˣ) : fixedField q)⁻¹) :
    ∀t:fixedField q,(tau t : q.Extension 3)=sigma (t:q.Extension 3) := by
  have hn (c:(q.Extension 3)ˣ) :
      tau (normUnits q c : fixedField q)=
        (normUnits q (Units.map sigma.toMonoidHom c) : fixedField q) := by
    have hh := congrArg Inv.inv (hnorm c)
    simpa only [map_inv₀,inv_inv] using hh
  intro t
  by_cases ht:t=0
  · simp only [ht,map_zero,Subfield.coe_zero]
  · obtain ⟨c,hc⟩ := normUnits_surjective q (Units.mk0 t ht)
    have hct : normFieldHom q (c:q.Extension 3)=t := congrArg Units.val hc
    have hnt : tau t=normFieldHom q (sigma (c:q.Extension 3)) := by
      have hh := hn c
      change tau (normFieldHom q (c:q.Extension 3))=normFieldHom q (sigma (c:q.Extension 3)) at hh
      rwa [hct] at hh
    calc
      (tau t:q.Extension 3)=((normFieldHom q (sigma (c:q.Extension 3)) : fixedField q) : q.Extension 3) :=
        congrArg Subtype.val hnt
      _=sigma ((normFieldHom q (c:q.Extension 3) : fixedField q) : q.Extension 3) :=
        (normFieldHom_ringAut_coe q sigma (c:q.Extension 3)).symm
      _=sigma (t:q.Extension 3) := congrArg sigma (congrArg Subtype.val hct)

end SymmetricSubgroupAsymptotics.CFSGTrialityNormFieldRestriction
