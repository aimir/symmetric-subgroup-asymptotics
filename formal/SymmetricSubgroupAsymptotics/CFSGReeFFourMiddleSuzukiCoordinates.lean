import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleFixedLaw
import SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotentCharacteristicLayers

/-! An actual multiplicative coordinate equivalence from the literal
middle fixed root group to the already-constructed Suzuki unipotent
group. Only the two original parameter charts and their proved laws are
used. This makes no claim about a whole rank-one subgroup or its Bruhat
presentation, and does not use ordinary F4 simplicity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleSuzukiCoordinates
open CFSGReeFFourFieldParameters CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourMiddleFixedWords CFSGReeFFourMiddleFixedParameters
open CFSGReeFFourMiddleFixedSubgroup CFSGReeFFourMiddleFixedLaw

theorem alpha_eq_suzukiTheta (m : ℕ) : alpha m=CFSGSuzukiFieldParameters.theta m := by
  apply RingHom.ext
  intro x
  rfl

def middleCoordinateElement (m : ℕ) (a c : Field m) : middleFixedSubgroup m :=
  ⟨fixedMiddleParameter m (a,c),a,alpha m a,c,alpha m c+a^2*alpha m a,rfl⟩

theorem middleCoordinateElement_val (m : ℕ) (a c : Field m) :
    (middleCoordinateElement m a c).val=fixedMiddleParameter m (a,c) := rfl

theorem middleCoordinateElement_mul (m : ℕ) (a c e s : Field m) :
    middleCoordinateElement m a c*middleCoordinateElement m e s=
      middleCoordinateElement m (a+e) (c+s+e*alpha m a) := by
  apply Subtype.ext
  exact fixedMiddleParameter_mul m a c e s

def middleParameterEquiv (m : ℕ) : (Field m×Field m)≃middleFixedSubgroup m :=
  Equiv.ofBijective (fun p=>middleCoordinateElement m p.1 p.2) (by
    constructor
    · intro p q he
      exact fixedMiddleParameter_injective m (congrArg (fun g : middleFixedSubgroup m=>g.val) he)
    · intro g
      have hr : g.val∈Set.range (fixedMiddleParameter m) := by
        rw [←middleFixedSubgroup_set]
        exact g.property
      obtain ⟨p,hp⟩ := hr
      exact ⟨p,Subtype.ext hp⟩)

theorem middleParameterEquiv_apply (m : ℕ) (p : Field m×Field m) :
    middleParameterEquiv m p=middleCoordinateElement m p.1 p.2 := rfl

def middleSuzukiEquiv (m : ℕ) : middleFixedSubgroup m≃*
    CFSGSuzukiUnipotent.unipotentSubgroup m := by
  let E : middleFixedSubgroup m≃CFSGSuzukiUnipotent.unipotentSubgroup m :=
    (middleParameterEquiv m).symm.trans (CFSGSuzukiUnipotent.parameterEquiv m)
  have hE (a c : Field m) : E (middleCoordinateElement m a c)=
      CFSGSuzukiUnipotent.coordinateElement m a c := by
    change CFSGSuzukiUnipotent.parameterEquiv m
      ((middleParameterEquiv m).symm ((middleParameterEquiv m) (a,c)))=_
    rw [Equiv.symm_apply_apply]
    rfl
  refine { E with map_mul' := ?_ }
  intro x y
  obtain ⟨⟨a,c⟩,rfl⟩ := (middleParameterEquiv m).surjective x
  obtain ⟨⟨e,s⟩,rfl⟩ := (middleParameterEquiv m).surjective y
  change E (middleCoordinateElement m a c*middleCoordinateElement m e s)=
    E (middleCoordinateElement m a c)*E (middleCoordinateElement m e s)
  rw [middleCoordinateElement_mul,hE,hE,hE,CFSGSuzukiUnipotent.coordinateElement_mul]
  rw [alpha_eq_suzukiTheta,mul_comm e]

theorem middleSuzukiEquiv_coordinateElement (m : ℕ) (a c : Field m) :
    middleSuzukiEquiv m (middleCoordinateElement m a c)=
      CFSGSuzukiUnipotent.coordinateElement m a c := by
  change CFSGSuzukiUnipotent.parameterEquiv m
    ((middleParameterEquiv m).symm ((middleParameterEquiv m) (a,c)))=_
  rw [Equiv.symm_apply_apply]
  rfl

end SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleSuzukiCoordinates
