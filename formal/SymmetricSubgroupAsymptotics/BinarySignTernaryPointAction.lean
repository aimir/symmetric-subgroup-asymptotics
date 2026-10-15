import SymmetricSubgroupAsymptotics.BinarySignTernaryAffineSocles
import SymmetricSubgroupAsymptotics.TernaryFourScalarFullAction

/-! The literal twelve-point action of the binary-sign ternary model.
Signs are evaluated at the destination block, matching the semidirect
product multiplication and the retained centered chart. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinarySignTernaryPointAction

open SemidirectProduct BinarySignTernaryLinear

variable {R : Type} [Group R] [MulAction R (Fin 4)]
variable (E : Subrepresentation
  (CyclicOrbitBinarySignNormalGenerators.permutationRepresentation (R := R) (X := Fin 4)))

def signAt (g : SignModel E) (i : Fin 4) : (ZMod 3)ˣ :=
  TernaryFourScalarDiagonalQuotient.bitScalar (Multiplicative.ofAdd (g.left.toAdd.1 i))

theorem signAt_one (i : Fin 4) : signAt E 1 i = 1 := rfl

theorem signAt_mul (g h : SignModel E) (i : Fin 4) :
    signAt E (g*h) i = signAt E g i * signAt E h (g.right⁻¹ • i) :=
  TernaryFourScalarDiagonalQuotient.bitScalar.map_mul _ _

theorem signAt_inv_cancel (g : SignModel E) (i : Fin 4) :
    (signAt E g i : ZMod 3) * (signAt E g⁻¹ (g.right⁻¹ • i) : ZMod 3) = 1 := by
  rw [← Units.val_mul,← signAt_mul,mul_inv_cancel,signAt_one,Units.val_one]

def complement : SignModel E →* Equiv.Perm (Fin 4 × ZMod 3) where
  toFun g :=
    { toFun p := (g.right • p.1,(signAt E g (g.right • p.1) : ZMod 3)*p.2)
      invFun p := (g.right⁻¹ • p.1,(signAt E g⁻¹ (g.right⁻¹ • p.1) : ZMod 3)*p.2)
      left_inv := by
        intro p
        apply Prod.ext
        · exact inv_smul_smul g.right p.1
        · change (signAt E g⁻¹ (g.right⁻¹ • (g.right • p.1)) : ZMod 3) *
              ((signAt E g (g.right • p.1) : ZMod 3)*p.2) = p.2
          rw [inv_smul_smul,← mul_assoc]
          have hc := signAt_inv_cancel E g⁻¹ p.1
          simpa only [SemidirectProduct.inv_right,inv_inv,one_mul] using congrArg (fun a => a*p.2) hc
      right_inv := by
        intro p
        apply Prod.ext
        · exact smul_inv_smul g.right p.1
        · change (signAt E g (g.right • (g.right⁻¹ • p.1)) : ZMod 3) *
              ((signAt E g⁻¹ (g.right⁻¹ • p.1) : ZMod 3)*p.2) = p.2
          rw [smul_inv_smul,← mul_assoc,signAt_inv_cancel,one_mul] }
  map_one' := by
    apply Equiv.ext
    intro p
    apply Prod.ext
    · exact one_smul R p.1
    · change (signAt E 1 ((1 : R) • p.1) : ZMod 3)*p.2 = p.2
      rw [signAt_one,Units.val_one,one_mul]
  map_mul' g h := by
    apply Equiv.ext
    intro p
    apply Prod.ext
    · exact mul_smul g.right h.right p.1
    · change (signAt E (g*h) ((g.right*h.right) • p.1) : ZMod 3)*p.2 =
        (signAt E g (g.right • (h.right • p.1)) : ZMod 3) *
          ((signAt E h (h.right • p.1) : ZMod 3)*p.2)
      rw [signAt_mul,mul_smul,inv_smul_smul,Units.val_mul,mul_assoc]

def pointAction : LinearSemidirectCoprimeSocleBounds.Model (linearHom E) →*
    Equiv.Perm (Fin 4 × ZMod 3) :=
  SemidirectProduct.lift (TernaryMonomialSemidirect.translations (X := Fin 4))
    (complement E) (by
      intro g
      apply MonoidHom.ext
      intro v
      apply Equiv.ext
      intro p
      apply Prod.ext
      · change p.1 = g.right • (g.right⁻¹ • p.1)
        exact (smul_inv_smul g.right p.1).symm
      · change (signAt E g p.1 : ZMod 3)*v.toAdd (g.right⁻¹ • p.1)+p.2 =
          (signAt E g (g.right • (g.right⁻¹ • p.1)) : ZMod 3) *
            (v.toAdd (g.right⁻¹ • p.1)+(signAt E g⁻¹ (g.right⁻¹ • p.1) : ZMod 3)*p.2)
        rw [smul_inv_smul,mul_add,← mul_assoc,signAt_inv_cancel,one_mul])

def action : LinearSemidirectCoprimeSocleBounds.Model (linearHom E) →*
    Equiv.Perm (Fin 12) :=
  TernaryFourAugmentationAffineImage.pointEquiv.symm.permCongrHom.toMonoidHom.comp (pointAction E)

def complementAction : SignModel E →* Equiv.Perm (Fin 12) :=
  TernaryFourAugmentationAffineImage.pointEquiv.symm.permCongrHom.toMonoidHom.comp (complement E)

theorem action_inl (v : Multiplicative Vector) :
    action E (inl v) = TernaryFourFullModuleCoordinates.translation v := by
  simp only [action,pointAction,MonoidHom.comp_apply,SemidirectProduct.lift_inl]
  simp only [TernaryFourFullModuleCoordinates.translation,
    TernaryFourFullModuleCoordinates.pointAction,MonoidHom.comp_apply,
    TernaryMonomialSemidirect.action,SemidirectProduct.lift_inl]

theorem action_inr (r : SignModel E) : action E (inr r) = complementAction E r := by
  simp only [action,pointAction,complementAction,MonoidHom.comp_apply,SemidirectProduct.lift_inr]

theorem action_range_le (T : Subgroup (Equiv.Perm (Fin 12)))
    (ht : ∀ v : Multiplicative Vector, TernaryFourFullModuleCoordinates.translation v ∈ T)
    (hc : ∀ r : SignModel E, complementAction E r ∈ T) : (action E).range ≤ T := by
  rintro _ ⟨g,rfl⟩
  rw [← inl_left_mul_inr_right g,map_mul,action_inl,action_inr]
  exact T.mul_mem (ht g.left) (hc g.right)

end SymmetricSubgroupAsymptotics.BinarySignTernaryPointAction

end
