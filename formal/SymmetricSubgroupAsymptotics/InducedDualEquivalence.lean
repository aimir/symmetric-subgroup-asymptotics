import SymmetricSubgroupAsymptotics.RepresentationHeadExact
import Mathlib.RepresentationTheory.FiniteIndex

/-!
# Duality for finite-index induced representations

For a finite-index subgroup, the contragredient of an induced
finite-dimensional representation is induced from the contragredient.  We
prove the statement at the literal representation level used by the affine
chief-layer argument.  The intermediate pairing identifies the dual of the
algebraic induced module with the coinduced dual; Mathlib's finite-index
induction--coinduction equivalence then gives the required induced model.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

variable {k G V : Type*} [Field k] [Group G]
  [AddCommGroup V] [Module k V]

namespace InducedDualEquivalence

variable (H : Subgroup G) (rho : Representation k H V)

/-- Pair a coinduced dual vector with the raw tensor model of induction. -/
private def rawPair
    (f : Representation.coindV H.subtype rho.dual) :
    TensorProduct k (G →₀ k) V →ₗ[k] k :=
  TensorProduct.lift (Finsupp.linearCombination k (fun g ↦ f.1 g))

private theorem rawPair_invariant
    (f : Representation.coindV H.subtype rho.dual) (h : H) :
    rawPair H rho f ∘ₗ
        (Representation.tprod
          ((Representation.leftRegular k G).comp H.subtype) rho) h =
      rawPair H rho f := by
  apply TensorProduct.ext'
  intro x v
  induction x using Finsupp.induction with
  | zero => simp [rawPair]
  | single_add g a x hg ha hx =>
      simp only [TensorProduct.add_tmul, map_add]
      rw [hx]
      congr 1
      simp only [LinearMap.comp_apply, Representation.tprod_apply,
        TensorProduct.map_tmul, rawPair, TensorProduct.lift.tmul]
      rw [show
        (((Representation.leftRegular k G).comp H.subtype) h)
            (Finsupp.single g a) =
          Finsupp.single ((h : G) * g) a by
            exact Representation.ofMulAction_single (h : G) g a]
      simp only [Finsupp.linearCombination_single]
      change (a • f.1 ((h : G) * g)) (rho h v) = (a • f.1 g) v
      simp only [LinearMap.smul_apply, RingHom.id_apply]
      congr 1
      calc
        f.1 ((h : G) * g) (rho h v) =
            (rho.dual h (f.1 g)) (rho h v) := by
              exact congrArg (fun l : Module.Dual k V ↦ l (rho h v)) (f.2 h g)
        _ = f.1 g v := by
          change f.1 g (rho h⁻¹ (rho h v)) = f.1 g v
          simp

/-- The perfect finite-index pairing from coinduced dual vectors to linear
forms on the induced module. -/
private def coindDualToIndDualLinear :
    Representation.coindV H.subtype rho.dual →ₗ[k]
      Module.Dual k (Representation.IndV H.subtype rho) where
  toFun f := Representation.Coinvariants.lift _ (rawPair H rho f)
    (rawPair_invariant H rho f)
  map_add' f g := by
    apply Representation.IndV.hom_ext
    intro x
    apply LinearMap.ext
    intro v
    simp [rawPair]
  map_smul' a f := by
    apply Representation.IndV.hom_ext
    intro x
    apply LinearMap.ext
    intro v
    simp [rawPair]

private theorem coindDualToIndDualLinear_mk
    (f : Representation.coindV H.subtype rho.dual) (g : G) (v : V) :
    coindDualToIndDualLinear H rho f
        (Representation.IndV.mk H.subtype rho g v) = f.1 g v := by
  rw [show Representation.IndV.mk H.subtype rho g v =
      Representation.Coinvariants.mk _
        (Finsupp.single g 1 ⊗ₜ[k] v) by rfl]
  simp [coindDualToIndDualLinear, rawPair]

/-- Recover a coinduced dual vector by evaluating an induced linear form on
the literal induced generators. -/
private def indDualToCoindDualLinear :
    Module.Dual k (Representation.IndV H.subtype rho) →ₗ[k]
      Representation.coindV H.subtype rho.dual where
  toFun l := ⟨fun g ↦ l.comp (Representation.IndV.mk H.subtype rho g), by
    intro h g
    apply LinearMap.ext
    intro v
    change l (Representation.IndV.mk H.subtype rho ((h : G) * g) v) =
      l (Representation.IndV.mk H.subtype rho g (rho h⁻¹ v))
    apply congrArg l
    change Representation.Coinvariants.mk _
        (Finsupp.single ((h : G) * g) 1 ⊗ₜ[k] v) =
      Representation.Coinvariants.mk _
        (Finsupp.single g 1 ⊗ₜ[k] rho h⁻¹ v)
    simpa using
      (Representation.Coinvariants.mk_inv_tmul
        ((Representation.leftRegular k G).comp H.subtype) rho
        (Finsupp.single g 1) v h⁻¹)
      |>.symm⟩
  map_add' _ _ := by
    apply Subtype.ext
    funext g
    apply LinearMap.ext
    intro v
    rfl
  map_smul' _ _ := by
    apply Subtype.ext
    funext g
    apply LinearMap.ext
    intro v
    rfl

private theorem coindDualToIndDualLinear_left_inv
    (f : Representation.coindV H.subtype rho.dual) :
    indDualToCoindDualLinear H rho (coindDualToIndDualLinear H rho f) = f := by
  apply Subtype.ext
  funext g
  apply LinearMap.ext
  intro v
  exact coindDualToIndDualLinear_mk H rho f g v

private theorem coindDualToIndDualLinear_right_inv
    (l : Module.Dual k (Representation.IndV H.subtype rho)) :
    coindDualToIndDualLinear H rho (indDualToCoindDualLinear H rho l) = l := by
  apply Representation.IndV.hom_ext
  intro g
  apply LinearMap.ext
  intro v
  exact coindDualToIndDualLinear_mk H rho
    (indDualToCoindDualLinear H rho l) g v

/-- Linear equivalence between the coinduced dual and the dual induced
module. -/
private def coindDualIndDualLinearEquiv :
    Representation.coindV H.subtype rho.dual ≃ₗ[k]
      Module.Dual k (Representation.IndV H.subtype rho) :=
  { toFun := coindDualToIndDualLinear H rho
    invFun := indDualToCoindDualLinear H rho
    left_inv := coindDualToIndDualLinear_left_inv H rho
    right_inv := coindDualToIndDualLinear_right_inv H rho
    map_add' := map_add (coindDualToIndDualLinear H rho)
    map_smul' := map_smul (coindDualToIndDualLinear H rho) }

/-- The pairing is equivariant for the right-translation convention used by
both induced and coinduced representations. -/
private def coindDualIndDualEquiv :
    (Representation.coind H.subtype rho.dual).Equiv
      (Representation.ind H.subtype rho).dual :=
  Representation.Equiv.mk (coindDualIndDualLinearEquiv H rho) (fun g ↦ by
    apply LinearMap.ext
    intro f
    apply Representation.IndV.hom_ext
    intro x
    apply LinearMap.ext
    intro v
    change coindDualToIndDualLinear H rho
        (Representation.coind H.subtype rho.dual g f)
          (Representation.IndV.mk H.subtype rho x v) =
      (Representation.ind H.subtype rho).dual g
        (coindDualToIndDualLinear H rho f)
          (Representation.IndV.mk H.subtype rho x v)
    rw [coindDualToIndDualLinear_mk]
    change f.1 (x * g) v =
      coindDualToIndDualLinear H rho f
        (Representation.ind H.subtype rho g⁻¹
          (Representation.IndV.mk H.subtype rho x v))
    rw [Representation.ind_mk, coindDualToIndDualLinear_mk]
    simp)

/-- **Finite-index induced duality.**  The dual of the literal induced
representation is equivalent to induction of the literal dual fibre. -/
def inducedDualEquiv [H.FiniteIndex] :
    (Representation.ind H.subtype rho.dual).Equiv
      (Representation.ind H.subtype rho).dual :=
  (Representation.equivOfIso (Rep.indCoindIso (Rep.of rho.dual))).trans
    (coindDualIndDualEquiv H rho)

end InducedDualEquivalence
end SymmetricSubgroupAsymptotics

end
