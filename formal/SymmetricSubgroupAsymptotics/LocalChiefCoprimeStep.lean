import SymmetricSubgroupAsymptotics.LocalChiefIntersectionStep
import SymmetricSubgroupAsymptotics.NormalImageQuotient

/-! Other-prime elementary local factors produce actual power-group
sections of the original chief intersections, hence a zero ternary
contribution. This is a statement about the actual quotient group, not
capacity loss caused by an odd-order action. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics

theorem primeModuleAdditive_isPGroup (p : ℕ) (W : Type*)
    [AddCommGroup W] [Module (ZMod p) W] :
    IsPGroup p (Multiplicative W) := by
  intro w
  refine ⟨1,?_⟩
  rw [pow_one]
  change p • w.toAdd=0
  rw [←Nat.cast_smul_eq_nsmul (ZMod p),ZMod.natCast_self,zero_smul]

section Local
variable {p : ℕ} [Fact p.Prime] {A R V : Type} [Group A] [Finite A] [Group R]
variable [AddCommGroup V] [Module (ZMod p) V]
variable (N H : Subgroup A) [N.Normal] (θ : N→*R) (β : H→*R)
variable (hθ : ∀ (h:H) (n:N),θ (MulAut.conjNormal (h:A) n)=β h*θ n*(β h)⁻¹)
variable (B L : Subgroup R) [B.Normal] [L.Normal] (hBL:B≤L)
variable (e : normalChainQuotient B L ≃*Multiplicative V)

include hθ hBL e in
theorem actualPrimeChiefIntersection_isPGroup :
    IsPGroup p (normalChainQuotient (localChiefIntersection N θ B)
      (localChiefIntersection N θ L)) := by
  let C := localChiefIntersection N θ L
  let ρ := localChiefSectionRepresentation (p:=p) B L e β
  let φ := localChiefIntersectionSectionMap N θ B L e
  let he := localChiefIntersectionSectionMap_equivariant (p:=p) N H θ β hθ B L e
  let π := localChiefQuotientMap H (normalChainSourceAction C) ρ φ he
  have hπ : Function.Surjective π :=
    localChiefQuotientMap_surjective H (normalChainSourceAction C) ρ φ he
  have hker : localChiefIntersection N θ B=π.ker.map C.subtype :=
    (localChiefIntersectionSection_kernel (p:=p) N H θ β hθ B L e hBL).symm
  let eq := normalSectionQuotientEquiv C (localChiefIntersection N θ B) π hπ hker
  exact (primeModuleAdditive_isPGroup p
    (localChiefInducedImage H (normalChainSourceAction C) ρ φ he).toSubmodule).of_equiv eq.symm

include hθ hBL e in
theorem actualCoprimeChiefIntersectionStep (hp3 : (p:ZMod 3)≠0) :
    TernaryChiefStep (localChiefIntersection N θ B) (localChiefIntersection N θ L) H 0 :=
  .coprime (localChiefIntersection_mono N θ hBL) p hp3
    (actualPrimeChiefIntersection_isPGroup (p:=p) N H θ β hθ B L hBL e)

end Local
end SymmetricSubgroupAsymptotics
