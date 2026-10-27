import SymmetricSubgroupAsymptotics.ActualComplementCocycleChartTransport
import SymmetricSubgroupAsymptotics.TwistedSimpleRootCocycleCount

/-! Actual full local component image supplies the ONTO predicate needed
by the root epimorphism code. The root action and its compatibility are
derived from the actual baseline conjugation and literal kernel chart.
No capacity or assumed automorphism extension occurs. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ActualComplementFullRootComponent
open TwistedMonomialCocycleFrame TwistedCocycleAssociatedHom
open ActualComplementSubgroupCocycleCode ActualComplementCocycleChartTransport

variable {E Q X A U : Type*} [Group E] [Group Q] [Group A] [Group U]
    [MulAction Q X] (π : E →* Q) (x0 : X)

def rootSubgroup : Subgroup E := (MulAction.stabilizer Q x0).comap π

def rootSection (L : ActualComplementSubgroupCocycleCode.Family π) :
    MulAction.stabilizer Q x0 →* rootSubgroup π x0 where
  toFun h := ⟨sectionHom π L h.val,by
    change π (sectionHom π L h.val)∈MulAction.stabilizer Q x0
    rw [section_right_inverse]
    exact h.property⟩
  map_one' := Subtype.ext (sectionHom π L).map_one
  map_mul' h k := Subtype.ext ((sectionHom π L).map_mul h.val k.val)

def rootKernel : π.ker →* rootSubgroup π x0 where
  toFun n := ⟨n.val,by
    change π n.val • x0=x0
    rw [n.property,one_smul]⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

variable (locMap : rootSubgroup π x0 →* U)

def localHom (L : ActualComplementSubgroupCocycleCode.Family π) :
    MulAction.stabilizer Q x0 →* U := locMap.comp (rootSection π x0 L)

def FullLocal (L : ActualComplementSubgroupCocycleCode.Family π) : Prop :=
  ∀ u : U,∃ g : rootSubgroup π x0,g.val∈L.val ∧ locMap g=u

theorem localHom_surjective (L : ActualComplementSubgroupCocycleCode.Family π)
    (hfull : FullLocal π x0 locMap L) : Function.Surjective (localHom π x0 locMap L) := by
  intro u
  obtain ⟨g,hg,hu⟩ := hfull u
  let h : MulAction.stabilizer Q x0 := ⟨π g.val,g.property⟩
  have hs : rootSection π x0 L h=g := by
    apply Subtype.ext
    change sectionHom π L (π g.val)=g.val
    exact congrArg (fun z : L.val => z.val)
      ((restrictedEquiv π L).symm_apply_apply ⟨g.val,hg⟩)
  exact ⟨h,(congrArg locMap hs).trans hu⟩

variable (L0 : ActualComplementSubgroupCocycleCode.Family π)
    (e : π.ker ≃* (X → A)) (ι : A →* U)
    (hlocMap : ∀ n : π.ker,locMap (rootKernel π x0 n)=ι (e n x0))
    (theta : Q → X → MulAut A)
    (hcoord : ∀ q : Q,∀ f : X → A,∀ x : X,
      (coordinateAction π L0 e q f) (q • x)=theta q x (f x))

include hlocMap in
theorem root_action_compatible (h : MulAction.stabilizer Q x0) (a : A) :
    ι (rootAction (coordinateAction π L0 e) theta hcoord x0 h a)=
      localHom π x0 locMap L0 h*ι a*(localHom π x0 locMap L0 h)⁻¹ := by
  let n : π.ker := e.symm (fun _ : X => a)
  have he : e n x0=a := by
    change e (e.symm (fun _ : X => a)) x0=a
    rw [e.apply_symm_apply]
  have hv : rootAction (coordinateAction π L0 e) theta hcoord x0 h a=
      e (baselineAction π L0 h.val n) x0 := by
    have hh := hcoord h.val (fun _ : X => a) x0
    have hfix : h.val • x0=x0 := h.property
    rw [hfix] at hh
    change e (baselineAction π L0 h.val n) x0=theta h.val x0 a at hh
    exact hh.symm
  have hc : rootKernel π x0 (baselineAction π L0 h.val n)=
      rootSection π x0 L0 h*rootKernel π x0 n*(rootSection π x0 L0 h)⁻¹ := by
    apply Subtype.ext
    exact MulAut.conjNormal_apply (sectionHom π L0 h.val) n
  rw [hv,←hlocMap,hc,map_mul,map_mul,map_inv,hlocMap,he]
  rfl

def associatedRoot (L : ActualComplementSubgroupCocycleCode.Family π) :
    MulAction.stabilizer Q x0 →* U :=
  associatedHom (rootAction (coordinateAction π L0 e) theta hcoord x0)
    (localHom π x0 locMap L0) ι
    (root_action_compatible π x0 locMap L0 e ι hlocMap theta hcoord)
    (rootRestriction (coordinateAction π L0 e) theta hcoord x0 (chartCode π L0 e L))

theorem associatedRoot_eq_localHom (L : ActualComplementSubgroupCocycleCode.Family π) :
    associatedRoot π x0 locMap L0 e ι hlocMap theta hcoord L=localHom π x0 locMap L := by
  ext h
  let d : π.ker := (cocycleCode π L0 L).val h.val
  change ι (e d x0)*locMap (rootSection π x0 L0 h)=locMap (rootSection π x0 L h)
  have hs : rootKernel π x0 d*rootSection π x0 L0 h=rootSection π x0 L h := by
    apply Subtype.ext
    exact section_recovery π L0 L h.val
  calc
    ι (e d x0)*locMap (rootSection π x0 L0 h)=
        locMap (rootKernel π x0 d)*locMap (rootSection π x0 L0 h) := by rw [hlocMap]
    _=locMap (rootKernel π x0 d*rootSection π x0 L0 h) := (locMap.map_mul _ _).symm
    _=locMap (rootSection π x0 L h) := congrArg locMap hs

theorem associatedRoot_surjective (L : ActualComplementSubgroupCocycleCode.Family π)
    (hfull : FullLocal π x0 locMap L) :
    Function.Surjective (associatedRoot π x0 locMap L0 e ι hlocMap theta hcoord L) := by
  rw [associatedRoot_eq_localHom]
  exact localHom_surjective π x0 locMap L hfull

theorem outerMap_surjective (hfull : FullLocal π x0 locMap L0)
    (N : Subgroup U) [N.Normal] :
    Function.Surjective (TwistedSimpleRootCocycleCount.outerMap (localHom π x0 locMap L0) N) :=
  (QuotientGroup.mk'_surjective _).comp (localHom_surjective π x0 locMap L0 hfull)

end SymmetricSubgroupAsymptotics.ActualComplementFullRootComponent
