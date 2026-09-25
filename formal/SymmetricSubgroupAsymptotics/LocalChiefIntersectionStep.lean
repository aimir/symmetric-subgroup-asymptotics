import SymmetricSubgroupAsymptotics.LocalChiefSection
import SymmetricSubgroupAsymptotics.ImprimitiveChiefCoordinates
import SymmetricSubgroupAsymptotics.ChiefTernaryFiltration

/-! An actual elementary section of the original local component
installs the corresponding actual chief-intersection step. Its quotient
action and equality of lower kernels are proved, not supplied as step
evidence by the caller. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics
section Construction
variable {p : ℕ} [Fact p.Prime] {A R V : Type} [Group A] [Finite A] [Group R]
variable [AddCommGroup V] [Module (ZMod p) V]
variable (N H : Subgroup A) [N.Normal] (θ : N→*R) (β : H→*R)
variable (hθ : ∀ (h:H) (n:N),θ (MulAut.conjNormal (h:A) n)=β h*θ n*(β h)⁻¹)
variable (B L : Subgroup R) [B.Normal] [L.Normal]
variable (e : normalChainQuotient B L ≃*Multiplicative V)

include hθ in
theorem localChiefIntersectionCoordinate_equivariant (h:H) (c:localChiefIntersection N θ L) :
    localChiefIntersectionCoordinate N θ L (MulAut.conjNormal (h:A) c)=
      localChiefSectionAction L β h (localChiefIntersectionCoordinate N θ L c) := by
  apply Subtype.ext
  exact hθ h ⟨(c:A),localChiefIntersection_le N θ L c.2⟩

def localChiefIntersectionSectionMap : localChiefIntersection N θ L→*Multiplicative V :=
  (localChiefSectionMap B L e).comp (localChiefIntersectionCoordinate N θ L)

include hθ in
theorem localChiefIntersectionSectionMap_equivariant
    (h:H) (c:localChiefIntersection N θ L) :
    (localChiefIntersectionSectionMap N θ B L e (MulAut.conjNormal (h:A) c)).toAdd=
      localChiefSectionRepresentation (p:=p) B L e β h
        (localChiefIntersectionSectionMap N θ B L e c).toAdd := by
  change (localChiefSectionMap B L e
    (localChiefIntersectionCoordinate N θ L (MulAut.conjNormal (h:A) c))).toAdd=_
  rw [localChiefIntersectionCoordinate_equivariant N H θ β hθ L]
  exact localChiefSectionRepresentation_equivariant (p:=p) B L e β h _

theorem localChiefIntersectionSection_kernel (hBL:B≤L) :
    localChiefAmbientKernel (localChiefIntersection N θ L) H
      (localChiefSectionRepresentation (p:=p) B L e β)
      (localChiefIntersectionSectionMap N θ B L e)
      (localChiefIntersectionSectionMap_equivariant (p:=p) N H θ β hθ B L e)=
        localChiefIntersection N θ B := by
  ext x
  constructor
  · rintro ⟨c,hc,rfl⟩
    let n : N := ⟨(c:A),localChiefIntersection_le N θ L c.2⟩
    apply (mem_localChiefIntersection N θ B n).mpr
    intro a
    have ha := (localChiefQuotientMap_kernel H
      (normalChainSourceAction (localChiefIntersection N θ L))
      (localChiefSectionRepresentation (p:=p) B L e β)
      (localChiefIntersectionSectionMap N θ B L e)
      (localChiefIntersectionSectionMap_equivariant (p:=p) N H θ β hθ B L e) c).mp hc a
    exact (localChiefSectionMap_kernel B L e
      (localChiefIntersectionCoordinate N θ L (MulAut.conjNormal a c))).mp ha
  · intro hx
    let c : localChiefIntersection N θ L :=
      ⟨x,localChiefIntersection_mono N θ hBL hx⟩
    let n : N := ⟨x,localChiefIntersection_le N θ B hx⟩
    refine ⟨c,?_,rfl⟩
    apply (localChiefQuotientMap_kernel H
      (normalChainSourceAction (localChiefIntersection N θ L))
      (localChiefSectionRepresentation (p:=p) B L e β)
      (localChiefIntersectionSectionMap N θ B L e)
      (localChiefIntersectionSectionMap_equivariant (p:=p) N H θ β hθ B L e) c).mpr
    intro a
    apply (localChiefSectionMap_kernel B L e
      (localChiefIntersectionCoordinate N θ L (MulAut.conjNormal a c))).mpr
    exact (mem_localChiefIntersection N θ B n).mp hx a

end Construction

theorem actualTernaryChiefIntersectionStep
    {A R V : Type} [Group A] [Finite A] [Group R]
    [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
    (N H : Subgroup A) [N.Normal] (θ : N→*R) (β : H→*R)
    (hθ : ∀ (h:H) (n:N),θ (MulAut.conjNormal (h:A) n)=β h*θ n*(β h)⁻¹)
    (B L : Subgroup R) [B.Normal] [L.Normal] (hBL:B≤L)
    (e : normalChainQuotient B L ≃*Multiplicative V) :
    TernaryChiefStep (localChiefIntersection N θ B) (localChiefIntersection N θ L) H
      (Module.finrank (ZMod 3) V) :=
  .elementary (localChiefSectionRepresentation (p:=3) B L e β)
    (localChiefIntersectionSectionMap N θ B L e)
    (localChiefIntersectionSectionMap_equivariant (p:=3) N H θ β hθ B L e)
    (localChiefIntersectionSection_kernel (p:=3) N H θ β hθ B L e hBL)

end SymmetricSubgroupAsymptotics
