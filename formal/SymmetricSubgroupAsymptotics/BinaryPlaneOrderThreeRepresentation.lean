import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Units
import Mathlib.RepresentationTheory.Intertwining
import SymmetricSubgroupAsymptotics.RepresentationIntertwinerGenerators

/-!
# Uniqueness of the faithful binary plane for a group of order three

The eight-frame row of top order `168` has an order-three local quotient.
Its literal affine module is two-dimensional over `F₂`.  This file records
the small representation-theoretic fact needed to compare an arbitrary
literal realization with the fixed matrix row: two faithful representations
of a group of order three on binary planes are equivalent.

Only the last conjugacy statement is finite.  It is checked on the six
elements of `GL₂(2)`; all transport to abstract two-dimensional spaces and
all extension from a generator to the whole group are proved generically.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

abbrev OrderThreeBinaryPlane := Fin 2 → ZMod 2

/-- A group representation, regarded as a homomorphism into the general
linear group.  The inverse of the unit attached to `g` is the linear action
of `g⁻¹`; hence no determinant calculation is involved. -/
def representationGeneralLinear
    {k G V : Type} [Field k] [Group G]
    [AddCommGroup V] [Module k V]
    (rho : Representation k G V) :
    G →* LinearMap.GeneralLinearGroup k V where
  toFun g := {
    val := rho g
    inv := rho g⁻¹
    val_inv := by
      apply LinearMap.ext
      exact rho.self_inv_apply g
    inv_val := by
      apply LinearMap.ext
      exact rho.inv_self_apply g }
  map_one' := by
    apply Units.ext
    exact map_one rho
  map_mul' g h := by
    apply Units.ext
    exact map_mul rho g h

@[simp] private theorem representationGeneralLinear_toLinearEquiv_apply
    {k G V : Type} [Field k] [Group G]
    [AddCommGroup V] [Module k V]
    (rho : Representation k G V) (g : G) (v : V) :
    (representationGeneralLinear rho g).toLinearEquiv v = rho g v :=
  rfl

/-- Put a representation on the standard binary plane through an arbitrary
linear coordinate equivalence. -/
def coordinateGeneralLinearRepresentation
    {G V : Type} [Group G]
    [AddCommGroup V] [Module (ZMod 2) V]
    (rho : Representation (ZMod 2) G V)
    (e : V ≃ₗ[ZMod 2] OrderThreeBinaryPlane) :
    G →* LinearMap.GeneralLinearGroup (ZMod 2) OrderThreeBinaryPlane :=
  (LinearMap.GeneralLinearGroup.congrLinearEquiv e).toMonoidHom.comp
    (representationGeneralLinear (k := ZMod 2) (G := G) (V := V) rho)

@[simp] private theorem ofLinearEquiv_toLinearEquiv
    {k V : Type} [Field k] [AddCommGroup V] [Module k V]
    (f : V ≃ₗ[k] V) :
    (LinearMap.GeneralLinearGroup.ofLinearEquiv f).toLinearEquiv = f :=
  rfl

/-- The two elements of order three in the matrix model of `GL₂(2)` are
conjugate.  This is the entire finite computation in the binary-plane
uniqueness theorem. -/
private theorem binaryMatrix_orderThree_conjugate :
    ∀ A B : Matrix.GeneralLinearGroup (Fin 2) (ZMod 2),
      A ^ 3 = 1 → A ≠ 1 → B ^ 3 = 1 → B ≠ 1 →
        ∃ C, C * A = B * C := by
  letI : Fintype (Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)) :=
    inferInstance
  letI : DecidableEq (Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)) :=
    inferInstance
  exact of_decide_eq_true rfl

/-- Transport the six-element matrix computation to the linear-map model
used by representations. -/
private theorem binaryPlane_orderThree_conjugate :
    ∀ A B : LinearMap.GeneralLinearGroup (ZMod 2) OrderThreeBinaryPlane,
      A ^ 3 = 1 → A ≠ 1 → B ^ 3 = 1 → B ≠ 1 →
        ∃ C, C * A = B * C := by
  intro A B hA hAne hB hBne
  let e := Matrix.GeneralLinearGroup.toLin (n := Fin 2) (R := ZMod 2)
  have hA' : e.symm A ^ 3 = 1 := by
    rw [← map_pow, hA, map_one]
  have hB' : e.symm B ^ 3 = 1 := by
    rw [← map_pow, hB, map_one]
  have hAne' : e.symm A ≠ 1 := by
    intro h
    apply hAne
    apply e.symm.injective
    simpa using h
  have hBne' : e.symm B ≠ 1 := by
    intro h
    apply hBne
    apply e.symm.injective
    simpa using h
  obtain ⟨C, hC⟩ := binaryMatrix_orderThree_conjugate
    (e.symm A) (e.symm B) hA' hAne' hB' hBne'
  refine ⟨e C, ?_⟩
  apply e.symm.injective
  simpa only [map_mul, e.symm_apply_apply] using hC

/-- Two faithful actions of the same order-three group on two-dimensional
binary spaces are linearly equivalent as representations. -/
noncomputable def binaryPlaneRepresentationEquiv_of_card_three
    {G V W : Type} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (rho : Representation (ZMod 2) G V)
    (sigma : Representation (ZMod 2) G W)
    (hG : Nat.card G = 3)
    (hV : Module.finrank (ZMod 2) V = 2)
    (hW : Module.finrank (ZMod 2) W = 2)
    (hrho : Function.Injective rho)
    (hsigma : Function.Injective sigma) :
    rho.Equiv sigma := by
  let eV : V ≃ₗ[ZMod 2] OrderThreeBinaryPlane :=
    LinearEquiv.ofFinrankEq V OrderThreeBinaryPlane (by
      rw [hV, Module.finrank_pi]
      simp)
  let eW : W ≃ₗ[ZMod 2] OrderThreeBinaryPlane :=
    LinearEquiv.ofFinrankEq W OrderThreeBinaryPlane (by
      rw [hW, Module.finrank_pi]
      simp)
  let phi := coordinateGeneralLinearRepresentation rho eV
  let psi := coordinateGeneralLinearRepresentation sigma eW
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ha_exists : ∃ a : G, orderOf a = 3 :=
    exists_prime_orderOf_dvd_card' (G := G) 3 (by rw [hG])
  let a : G := Classical.choose ha_exists
  have ha : orderOf a = 3 := Classical.choose_spec ha_exists
  have ha_ne : a ≠ 1 := by
    intro ha1
    rw [ha1, orderOf_one] at ha
    norm_num at ha
  have hphi_injective : Function.Injective phi := by
    intro g h hgh
    apply hrho
    have hunits : representationGeneralLinear rho g =
        representationGeneralLinear rho h := by
      apply (LinearMap.GeneralLinearGroup.congrLinearEquiv eV).injective
      simpa only [phi, coordinateGeneralLinearRepresentation,
        MonoidHom.comp_apply] using hgh
    simpa only [representationGeneralLinear] using congrArg Units.val hunits
  have hpsi_injective : Function.Injective psi := by
    intro g h hgh
    apply hsigma
    have hunits : representationGeneralLinear sigma g =
        representationGeneralLinear sigma h := by
      apply (LinearMap.GeneralLinearGroup.congrLinearEquiv eW).injective
      simpa only [psi, coordinateGeneralLinearRepresentation,
        MonoidHom.comp_apply] using hgh
    simpa only [representationGeneralLinear] using congrArg Units.val hunits
  have hphi_three : phi a ^ 3 = 1 := by
    rw [← map_pow, ← ha, pow_orderOf_eq_one, map_one]
  have hpsi_three : psi a ^ 3 = 1 := by
    rw [← map_pow, ← ha, pow_orderOf_eq_one, map_one]
  have hphi_ne : phi a ≠ 1 := by
    intro h
    exact ha_ne (hphi_injective (h.trans (map_one phi).symm))
  have hpsi_ne : psi a ≠ 1 := by
    intro h
    exact ha_ne (hpsi_injective (h.trans (map_one psi).symm))
  have hC_exists : ∃ C, C * phi a = psi a * C :=
    binaryPlane_orderThree_conjugate
      (phi a) (psi a) hphi_three hphi_ne hpsi_three hpsi_ne
  let C := Classical.choose hC_exists
  have hC : C * phi a = psi a * C := Classical.choose_spec hC_exists
  let e : V ≃ₗ[ZMod 2] W :=
    eV.trans (C.toLinearEquiv.trans eW.symm)
  have ha_intertwines : ∀ v, e (rho a v) = sigma a (e v) := by
    intro v
    have hCv := congrArg
      (fun u : LinearMap.GeneralLinearGroup (ZMod 2) OrderThreeBinaryPlane ↦
        u.toLinearEquiv (eV v)) hC
    dsimp only [phi, psi, coordinateGeneralLinearRepresentation,
      MonoidHom.comp_apply] at hCv
    simp only [LinearMap.GeneralLinearGroup.toLinearEquiv_mul,
      LinearEquiv.mul_apply,
      MulEquiv.coe_toMonoidHom,
      LinearMap.GeneralLinearGroup.congrLinearEquiv_apply,
      ofLinearEquiv_toLinearEquiv,
      representationGeneralLinear_toLinearEquiv_apply,
      LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] at hCv
    change C.toLinearEquiv (eV (rho a v)) =
      eW (sigma a (eW.symm (C.toLinearEquiv (eV v)))) at hCv
    apply eW.injective
    simpa only [e, LinearEquiv.trans_apply,
      LinearEquiv.apply_symm_apply] using hCv
  have hgenerates :
      Subgroup.closure (Set.range (fun _ : Unit ↦ a)) = ⊤ := by
    have hrange : Set.range (fun _ : Unit ↦ a) = {a} := by
      ext g
      simp
    rw [hrange, ← Subgroup.zpowers_eq_closure]
    exact zpowers_eq_top_of_prime_card hG ha_ne
  let f := representationIntertwiningMap_of_generators rho sigma
    e.toLinearMap (fun _ : Unit ↦ a) hgenerates (by
      intro _ v
      exact ha_intertwines v)
  exact Representation.Equiv.mk e (by
    intro g
    exact f.isIntertwining' g)

end SymmetricSubgroupAsymptotics

end
