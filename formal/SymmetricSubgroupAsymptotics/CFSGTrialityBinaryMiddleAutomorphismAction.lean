import SymmetricSubgroupAsymptotics.CentralExtensionScalarPairingCharacteristicKernel
import SymmetricSubgroupAsymptotics.CFSGInvariantQuotientAutomorphism
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleCentralExtensionData

/-! Intrinsic automorphisms of the actual fixed middle radical act on
its literal tensor quotient. In the binary case every additive action
is linear over the actual two-element fixed field. No image assertion
about a larger linear group is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityBinaryMiddleAutomorphismAction
open CFSGTrialityMiddleFixedTensorSpan CFSGTrialityGeckMiddleFixedCommutators
open CFSGTrialityGeckMiddleFixedQuotientCoordinates CFSGTrialityGeckMiddleCentralExtensionData

private theorem invariant (q : CFSG.PrimePower) (f : MulAut (fixedMiddle q)) :
    (projection q).ker.map f.toMonoidHom=(projection q).ker :=
  CentralExtensionScalarPairingCharacteristicKernel.projection_ker_map_eq (extensionData q) f

def additiveAction (q : CFSG.PrimePower) :
    MulAut (fixedMiddle q) →* AddAut (fullEnvelope q) :=
  CFSGInvariantQuotientAutomorphism.quotientAddAutHom (projection q)
    (projection_surjective q) (MonoidHom.id _) (invariant q)

theorem additiveAction_coordinate (q : CFSG.PrimePower) (f : MulAut (fixedMiddle q))
    (u : fixedMiddle q) :
    additiveAction q f (coordinate q u)=coordinate q (f u) :=
  CFSGInvariantQuotientAutomorphism.quotientAddAut_first (projection q)
    (projection_surjective q) (MonoidHom.id _) (invariant q) f u

private theorem binary_smul {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (hk : Nat.card k=2) (f : AddAut V) (c : k) (v : V) : f (c • v)=c • f v := by
  have hc : c=0 ∨ c=1 := by
    by_cases h : c=0
    · exact Or.inl h
    obtain ⟨a,ha,hu⟩ := (Nat.card_eq_two_iff' (0 : k)).mp hk
    exact Or.inr ((hu c h).trans (hu 1 one_ne_zero).symm)
  rcases hc with rfl | rfl <;> simp only [zero_smul,one_smul,map_zero]

private def binaryLinearAction {k V A : Type*} [Field k] [AddCommGroup V]
    [Module k V] [Monoid A] (hk : Nat.card k=2) (rho : A →* AddAut V) :
    A →* (V ≃ₗ[k] V) where
  toFun a := (rho a).toLinearEquiv (binary_smul hk (rho a))
  map_one' := by
    apply LinearEquiv.ext
    intro v
    change rho 1 v=v
    rw [map_one]
    rfl
  map_mul' a b := by
    apply LinearEquiv.ext
    intro v
    change rho (a*b) v=rho a (rho b v)
    rw [map_mul]
    rfl

def linearAction (q : CFSG.PrimePower) (hq : q.order=2) :
    MulAut (fixedMiddle q) →* (fullEnvelope q ≃ₗ[F q] fullEnvelope q) :=
  binaryLinearAction ((CFSGTrialityFixedField.fixedField_card q).trans hq) (additiveAction q)

theorem linearAction_coordinate (q : CFSG.PrimePower) (hq : q.order=2)
    (f : MulAut (fixedMiddle q)) (u : fixedMiddle q) :
    linearAction q hq f (coordinate q u)=coordinate q (f u) :=
  additiveAction_coordinate q f u

end SymmetricSubgroupAsymptotics.CFSGTrialityBinaryMiddleAutomorphismAction
