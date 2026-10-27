import SymmetricSubgroupAsymptotics.ActualComplementFullRootComponent
import SymmetricSubgroupAsymptotics.PermutationalWreathQuotient

/-! Existing literal FullComponent supplies the full-root condition for
the actual complement code. Original and quotient top groups may differ;
only their actual point-action compatibility is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ActualWreathComplementFullRoot
open PermutationalWreathProduct ActualComplementFullRootComponent
open PermutationalWreathProduct.Compression

variable {E Q R X D : Type} [Group E] [Group Q] [Group R] [Group D]
    [MulAction Q X] [MulAction R X]
variable (π : E →* Q) (ξ : E →* PermutationalWreathProduct D R X)
    (htop : ∀ g : E,∀ x : X,(ξ g).right • x=π g • x) (x0 : X)

def component : rootSubgroup π x0 →* D where
  toFun g := (ξ g.val).left x0
  map_one' := by
    change (ξ (1 : E)).left x0=1
    exact congrArg (fun w : PermutationalWreathProduct D R X => w.left x0) ξ.map_one
  map_mul' g h := by
    change (ξ (g.val*h.val)).left x0=(ξ g.val).left x0*(ξ h.val).left x0
    rw [map_mul,mul_left]
    have hg : (ξ g.val).right • x0=x0 := (htop g.val x0).trans g.property
    have hgi : (ξ g.val).right⁻¹ • x0=x0 := by
      calc
        (ξ g.val).right⁻¹ • x0=(ξ g.val).right⁻¹ • ((ξ g.val).right • x0) :=
          congrArg ((ξ g.val).right⁻¹ • ·) hg.symm
        _=x0 := inv_smul_smul _ _
    simp only [Pi.mul_apply,hgi]

theorem fullLocal_of_fullComponent
    (L : ActualComplementSubgroupCocycleCode.Family π)
    (hfull : FullComponent (ξ.comp L.val.subtype)) :
    FullLocal π x0 (component π ξ htop x0) L := by
  intro d
  obtain ⟨l,hfix,hd⟩ := hfull x0 d
  have hlroot : l.val∈rootSubgroup π x0 := by
    change π l.val • x0=x0
    exact (htop l.val x0).symm.trans hfix
  exact ⟨⟨l.val,hlroot⟩,l.property,hd⟩

variable {A : Type} [Group A]
    (L0 : ActualComplementSubgroupCocycleCode.Family π)
    (e : π.ker ≃* (X → A)) (ι : A →* D)
    (hchart : ∀ n : π.ker,(ξ n.val).left x0=ι (e n x0))
    (theta : Q → X → MulAut A)
    (hcoord : ∀ q : Q,∀ f : X → A,∀ x : X,
      (ActualComplementCocycleChartTransport.coordinateAction π L0 e q f) (q • x)=theta q x (f x))

theorem associatedRoot_surjective_of_fullComponent
    (L : ActualComplementSubgroupCocycleCode.Family π)
    (hfull : FullComponent (ξ.comp L.val.subtype)) :
    Function.Surjective
      (associatedRoot π x0 (component π ξ htop x0) L0 e ι
        hchart theta hcoord L) :=
  associatedRoot_surjective π x0 (component π ξ htop x0) L0 e ι
    hchart theta hcoord L (fullLocal_of_fullComponent π ξ htop x0 L hfull)

abbrev FullFamily := {L : ActualComplementSubgroupCocycleCode.Family π //
  FullComponent (ξ.comp L.val.subtype)}

def rootPredicate :
    TwistedMonomialCocycleFrame.Cocycle
      (ActualComplementCocycleChartTransport.coordinateAction π L0 e) → Prop :=
  fun c => Function.Surjective
    (TwistedCocycleAssociatedHom.associatedHom
      (TwistedMonomialCocycleFrame.rootAction
        (ActualComplementCocycleChartTransport.coordinateAction π L0 e) theta hcoord x0)
      (localHom π x0 (component π ξ htop x0) L0) ι
      (root_action_compatible π x0 (component π ξ htop x0) L0 e ι hchart theta hcoord)
      (TwistedMonomialCocycleFrame.rootRestriction
        (ActualComplementCocycleChartTransport.coordinateAction π L0 e) theta hcoord x0 c))

def fullComponentCode (L : FullFamily π ξ) :
    {c : TwistedMonomialCocycleFrame.Cocycle
      (ActualComplementCocycleChartTransport.coordinateAction π L0 e) //
        rootPredicate π ξ htop x0 L0 e ι hchart theta hcoord c} :=
  ⟨ActualComplementCocycleChartTransport.chartCode π L0 e L.val,
    associatedRoot_surjective_of_fullComponent π ξ htop x0 L0 e ι hchart theta hcoord
      L.val L.property⟩

theorem fullComponentCode_injective :
    Function.Injective (fullComponentCode π ξ htop x0 L0 e ι hchart theta hcoord) := by
  intro L M h
  exact Subtype.ext (ActualComplementCocycleChartTransport.chartCode_injective π L0 e
    (congrArg Subtype.val h))

theorem empty_or_full_component_baseline :
    IsEmpty (FullFamily π ξ) ∨ Nonempty (FullFamily π ξ) := by
  by_cases h : Nonempty (FullFamily π ξ)
  · exact Or.inr h
  · exact Or.inl ⟨fun L => h ⟨L⟩⟩

end SymmetricSubgroupAsymptotics.ActualWreathComplementFullRoot
