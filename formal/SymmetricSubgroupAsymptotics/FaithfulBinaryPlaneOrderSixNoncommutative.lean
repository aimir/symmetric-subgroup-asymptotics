import SymmetricSubgroupAsymptotics.BinaryPlaneOrderThreeRepresentation

/-!
# Faithful binary planes exclude cyclic order six

The general linear group of a two-dimensional binary space is the
noncommutative group of order six.  Hence a faithful binary-plane action of
an order-six group identifies that group with `GL₂(2)` and cannot have a
commutative source.  This is the exact eligibility fact needed by the
eight-frame local-row catalogue.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

private abbrev BinaryMatrixGL :=
  Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)

theorem binaryPlaneGL_not_isMulCommutative :
    ¬ IsMulCommutative BinaryPlaneGL := by
  have hex : ∃ A B : BinaryMatrixGL, A * B ≠ B * A := by
    exact of_decide_eq_true rfl
  obtain ⟨A, B, hAB⟩ := hex
  intro hcomm
  letI : IsMulCommutative BinaryPlaneGL := hcomm
  let e := Matrix.GeneralLinearGroup.toLin (n := Fin 2) (R := ZMod 2)
  apply hAB
  apply e.injective
  simpa only [map_mul] using (mul_comm' (e A) (e B))

theorem not_isMulCommutative_of_faithful_binary_plane_card_six
    {G V : Type} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (rho : Representation (ZMod 2) G V)
    (hG : Nat.card G = 6)
    (hV : Module.finrank (ZMod 2) V = 2)
    (hrho : Function.Injective rho) :
    ¬ IsMulCommutative G := by
  let e : V ≃ₗ[ZMod 2] OrderThreeBinaryPlane :=
    LinearEquiv.ofFinrankEq V OrderThreeBinaryPlane (by
      rw [hV, Module.finrank_pi]
      simp)
  let phi := coordinateGeneralLinearRepresentation rho e
  have hphi : Function.Injective phi := by
    intro g h hgh
    apply hrho
    have hunits : representationGeneralLinear rho g =
        representationGeneralLinear rho h := by
      apply (LinearMap.GeneralLinearGroup.congrLinearEquiv e).injective
      simpa only [phi, coordinateGeneralLinearRepresentation,
        MonoidHom.comp_apply] using hgh
    simpa only [representationGeneralLinear] using congrArg Units.val hunits
  let glEquiv := Matrix.GeneralLinearGroup.toLin
    (n := Fin 2) (R := ZMod 2)
  letI : Finite BinaryPlaneGL :=
    Finite.of_surjective glEquiv glEquiv.surjective
  have hbij : Function.Bijective phi :=
    (Nat.bijective_iff_injective_and_card phi).mpr
      ⟨hphi, hG.trans binaryPlaneGL_card.symm⟩
  intro hcomm
  apply binaryPlaneGL_not_isMulCommutative
  refine { is_comm.comm := fun A B => ?_ }
  obtain ⟨a, rfl⟩ := hbij.surjective A
  obtain ⟨b, rfl⟩ := hbij.surjective B
  rw [← map_mul, ← map_mul, hcomm.is_comm.comm a b]

theorem not_isMulCommutative_of_faithful_binary_plane_card_six_at
    {p : ℕ} [Fact p.Prime]
    {G V : Type} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod p) V]
    [FiniteDimensional (ZMod p) V]
    (hp : p = 2)
    (rho : Representation (ZMod p) G V)
    (hG : Nat.card G = 6)
    (hV : Module.finrank (ZMod p) V = 2)
    (hrho : Function.Injective rho) :
    ¬ IsMulCommutative G := by
  subst p
  exact not_isMulCommutative_of_faithful_binary_plane_card_six
    rho hG hV hrho

end SymmetricSubgroupAsymptotics

end
