import SymmetricSubgroupAsymptotics.CoordinateDependencyMonomialAction
import SymmetricSubgroupAsymptotics.ActualComplementCocycleChartTransport
import SymmetricSubgroupAsymptotics.PermutationalWreathQuotient

/-! Construct monomial twists for the EXACT baseline-conjugation action
transported through a literal actual kernel chart. The chart alignment
and top compatibility are explicit; no correlated kernel is replaced by
an independent product. A full-wreath instance constructs its chart. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ActualWreathComplementMonomialCoordinates
open ActualComplementSubgroupCocycleCode ActualComplementCocycleChartTransport

section MovingCoordinate
variable {D T X : Type*} [Group D] [Group T] [MulAction T X]

/-- A kernel element need only act trivially on the top point set; the
top group itself need not act faithfully. -/
theorem conj_left_at_moved (a k : PermutationalWreathProduct D T X)
    (hk : ∀ x : X, k.right • x=x) (x : X) :
    (a*k*a⁻¹).left (a.right • x)=
      a.left (a.right • x)*k.left x*(a.left (a.right • x))⁻¹ := by
  have hkinv (y : X) : k.right⁻¹ • y=y := by
    calc
      _=k.right⁻¹ • (k.right • y) := congrArg (fun z : X => k.right⁻¹ • z) (hk y).symm
      _=y := inv_smul_smul _ _
  simp [PermutationalWreathProduct.mul_left,PermutationalWreathProduct.mul_right,
    PermutationalWreathProduct.inv_left,mul_inv_rev,mul_smul,hkinv]
end MovingCoordinate

section ActualChart
variable {E Q T X A D : Type*} [Group E] [Group Q] [Group T] [Group A] [Group D]
    [MulAction Q X] [MulAction T X]
variable (pi : E →* Q) (e : pi.ker ≃* (X → A))
    (xi : E →* PermutationalWreathProduct D T X) (iota : A →* D)

/-- Literal compatibility of the SAME actual chart and wreath embedding.
Surjectivity/independence is supplied by the genuine equivalence e;
coordinatewise surjectivity alone is not substituted for it. -/
structure Chart where
  iota_injective : Function.Injective iota
  top_compatible : ∀ (g : E) (x : X), (xi g).right • x=pi g • x
  coordinate_compatible : ∀ (n : pi.ker) (x : X), iota (e n x)=(xi n.val).left x

theorem coordinate_conjugation (L0 : Family pi) (C : Chart pi e xi iota)
    (q : Q) (f : X → A) (x : X) :
    iota ((coordinateAction pi L0 e q f) (q • x))=
      (xi (sectionHom pi L0 q)).left (q • x)*iota (f x)*
        ((xi (sectionHom pi L0 q)).left (q • x))⁻¹ := by
  let s : E := sectionHom pi L0 q
  let n : pi.ker := e.symm f
  let z : pi.ker := MulAut.conjNormal s n
  have hvalue : coordinateAction pi L0 e q f=e z := rfl
  have hfix (y : X) : (xi n.val).right • y=y := by
    rw [C.top_compatible]
    have hn : pi n.val=1 := n.property
    rw [hn,one_smul]
  have hmove : (xi s).right • x=q • x := by
    rw [C.top_compatible]
    exact congrArg (fun r : Q => r • x) (section_right_inverse pi L0 q)
  have hmap : xi z.val=xi s*xi n.val*(xi s)⁻¹ := by
    change xi (s*n.val*s⁻¹)=xi s*xi n.val*(xi s)⁻¹
    rw [map_mul,map_mul,map_inv]
  have hncoord : (xi n.val).left x=iota (f x) := by
    calc
      _=iota (e n x) := (C.coordinate_compatible n x).symm
      _=iota (f x) := congrArg (fun v : X → A => iota (v x)) (e.apply_symm_apply f)
  calc
    _=iota (e z (q • x)) := congrArg (fun v : X → A => iota (v (q • x))) hvalue
    _=(xi z.val).left (q • x) := C.coordinate_compatible z (q • x)
    _=(xi s*xi n.val*(xi s)⁻¹).left (q • x) := congrArg (fun w => w.left (q • x)) hmap
    _=(xi s).left (q • x)*(xi n.val).left x*((xi s).left (q • x))⁻¹ := by
      simpa only [hmove] using conj_left_at_moved (xi s) (xi n.val) hfix x
    _=_ := by rw [hncoord]

theorem coordinate_dependency (L0 : Family pi) (C : Chart pi e xi iota) :
    CoordinateDependencyMonomialAction.Depends (coordinateAction pi L0 e) := by
  intro q f g x hfg
  apply C.iota_injective
  rw [coordinate_conjugation pi e xi iota L0 C,
    coordinate_conjugation pi e xi iota L0 C,hfg]

def actualTwist (L0 : Family pi) (C : Chart pi e xi iota) (q : Q) (x : X) : MulAut A :=
  CoordinateDependencyMonomialAction.twist (coordinateAction pi L0 e)
    (coordinate_dependency pi e xi iota L0 C) q x

/-- The action here is EXACTLY the actual transported baseline action. -/
theorem monomial_law (L0 : Family pi) (C : Chart pi e xi iota)
    (q : Q) (f : X → A) (x : X) :
    (coordinateAction pi L0 e q f) (q • x)=actualTwist pi e xi iota L0 C q x (f x) :=
  CoordinateDependencyMonomialAction.monomial_law (coordinateAction pi L0 e)
    (coordinate_dependency pi e xi iota L0 C) q f x

/-- The constructed twist is literal conjugation by the actual moving
component, seen through the actual injective local coefficient map. -/
theorem actualTwist_conjugation (L0 : Family pi) (C : Chart pi e xi iota)
    (q : Q) (x : X) (a : A) :
    iota (actualTwist pi e xi iota L0 C q x a)=
      (xi (sectionHom pi L0 q)).left (q • x)*iota a*
        ((xi (sectionHom pi L0 q)).left (q • x))⁻¹ :=
  coordinate_conjugation pi e xi iota L0 C q (fun _ : X => a) x
end ActualChart

section FullWreath
variable {D Q X : Type*} [Group D] [Group Q] [MulAction Q X]
abbrev W := PermutationalWreathProduct D Q X

/-- This full-product chart is constructed, not assumed for a correlated
subgroup of a wreath product. -/
def fullBaseChart : (PermutationalWreathProduct.rightHom (D := D) (Q := Q) (I := X)).ker ≃*
    (X → D) where
  toFun n := n.val.left
  invFun f := ⟨⟨f,1⟩,rfl⟩
  left_inv n := by
    apply Subtype.ext
    apply PermutationalWreathProduct.ext
    · rfl
    · exact (MonoidHom.mem_ker.mp n.property).symm
  right_inv f := rfl
  map_mul' n m := by
    funext x
    change (n.val*m.val).left x=n.val.left x*m.val.left x
    have hn : n.val.right=1 := n.property
    simp only [PermutationalWreathProduct.mul_left,Pi.mul_apply,hn,inv_one,one_smul]

def fullWreathChart : Chart
    (PermutationalWreathProduct.rightHom (D := D) (Q := Q) (I := X))
    (fullBaseChart (D := D) (Q := Q) (X := X)) (MonoidHom.id W) (MonoidHom.id D) where
  iota_injective := Function.injective_id
  top_compatible g x := rfl
  coordinate_compatible n x := rfl

def fullTwist (L0 : Family (PermutationalWreathProduct.rightHom (D := D) (Q := Q) (I := X)))
    (q : Q) (x : X) : MulAut D :=
  actualTwist _ fullBaseChart (MonoidHom.id W) (MonoidHom.id D) L0 fullWreathChart q x

theorem full_wreath_monomial_law
    (L0 : Family (PermutationalWreathProduct.rightHom (D := D) (Q := Q) (I := X)))
    (q : Q) (f : X → D) (x : X) :
    (coordinateAction _ L0 fullBaseChart q f) (q • x)=fullTwist L0 q x (f x) :=
  monomial_law _ fullBaseChart (MonoidHom.id W) (MonoidHom.id D) L0 fullWreathChart q f x
end FullWreath

end SymmetricSubgroupAsymptotics.ActualWreathComplementMonomialCoordinates
