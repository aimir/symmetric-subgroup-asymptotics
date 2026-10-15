import SymmetricSubgroupAsymptotics.FaithfulBinaryPlaneOrderSixNoncommutative

/-! Kernel-checked cardinality and local binary-plane comparisons.
This narrow replacement keeps the older declarations unchanged. The new
consumers use the actual six-element matrix cardinality evaluated by the
kernel, avoiding the historical native cardinality axiom. The order-three
comparison and the symbolic inner-automorphism proof are reused unchanged.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryPlaneKernelClassification

/-- Count the concrete matrix units first, before transporting to linear maps. -/
theorem card : Nat.card BinaryPlaneGL = 6 := by
  let e := Matrix.GeneralLinearGroup.toLin (n := Fin 2) (R := ZMod 2)
  calc
    Nat.card BinaryPlaneGL =
        Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)) :=
      (Nat.card_congr e.toEquiv).symm
    _ = 6 := by
      rw [Nat.card_eq_fintype_card]
      decide +kernel

@[simp] private theorem representationGeneralLinear_toLinearEquiv_apply
    {k G V : Type} [Field k] [Group G]
    [AddCommGroup V] [Module k V]
    (rho : Representation k G V) (g : G) (v : V) :
    (representationGeneralLinear rho g).toLinearEquiv v = rho g v := rfl

@[simp] private theorem ofLinearEquiv_toLinearEquiv
    {k V : Type} [Field k] [AddCommGroup V] [Module k V]
    (f : V ≃ₗ[k] V) :
    (LinearMap.GeneralLinearGroup.ofLinearEquiv f).toLinearEquiv = f := rfl

noncomputable def representationEquiv_of_card_six
    {G V W : Type} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (rho : Representation (ZMod 2) G V)
    (sigma : Representation (ZMod 2) G W)
    (hG : Nat.card G = 6)
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
  have hphi_surjective : Function.Surjective phi := by
    letI := Fintype.ofFinite G
    let e := Matrix.GeneralLinearGroup.toLin (n := Fin 2) (R := ZMod 2)
    letI : Fintype BinaryPlaneGL := Fintype.ofEquiv _ e.toEquiv
    have hcard : Fintype.card G = Fintype.card BinaryPlaneGL := by
      simpa only [Fintype.card_eq_nat_card, hG, card]
    exact ((Fintype.bijective_iff_injective_and_card phi).2
      ⟨hphi_injective, hcard⟩).2
  have hpsi_surjective : Function.Surjective psi := by
    letI := Fintype.ofFinite G
    let e := Matrix.GeneralLinearGroup.toLin (n := Fin 2) (R := ZMod 2)
    letI : Fintype BinaryPlaneGL := Fintype.ofEquiv _ e.toEquiv
    have hcard : Fintype.card G = Fintype.card BinaryPlaneGL := by
      simpa only [Fintype.card_eq_nat_card, hG, card]
    exact ((Fintype.bijective_iff_injective_and_card psi).2
      ⟨hpsi_injective, hcard⟩).2
  let phiEquiv : G ≃* BinaryPlaneGL :=
    MulEquiv.ofBijective phi ⟨hphi_injective, hphi_surjective⟩
  let psiEquiv : G ≃* BinaryPlaneGL :=
    MulEquiv.ofBijective psi ⟨hpsi_injective, hpsi_surjective⟩
  let α : MulAut BinaryPlaneGL := phiEquiv.symm.trans psiEquiv
  let hinner := binaryPlaneGL_automorphism_inner α
  let C : BinaryPlaneGL := Classical.choose hinner
  have hC : ∀ A : BinaryPlaneGL, C * A = α A * C :=
    Classical.choose_spec hinner
  let e : V ≃ₗ[ZMod 2] W :=
    eV.trans (C.toLinearEquiv.trans eW.symm)
  have hintertwines : ∀ g v, e (rho g v) = sigma g (e v) := by
    intro g v
    have hCg := hC (phi g)
    have hα : α (phi g) = psi g := by
      change psiEquiv (phiEquiv.symm (phiEquiv g)) = psiEquiv g
      rw [phiEquiv.symm_apply_apply]
    rw [hα] at hCg
    have hCgv := congrArg
      (fun u : BinaryPlaneGL ↦ u.toLinearEquiv (eV v)) hCg
    dsimp only [phi, psi, coordinateGeneralLinearRepresentation,
      MonoidHom.comp_apply] at hCgv
    simp only [LinearMap.GeneralLinearGroup.toLinearEquiv_mul,
      LinearEquiv.mul_apply, MulEquiv.coe_toMonoidHom,
      LinearMap.GeneralLinearGroup.congrLinearEquiv_apply,
      ofLinearEquiv_toLinearEquiv,
      representationGeneralLinear_toLinearEquiv_apply,
      LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] at hCgv
    change C.toLinearEquiv (eV (rho g v)) =
      eW (sigma g (eW.symm (C.toLinearEquiv (eV v)))) at hCgv
    apply eW.injective
    simpa only [e, LinearEquiv.trans_apply,
      LinearEquiv.apply_symm_apply] using hCgv
  exact Representation.Equiv.mk e
    (fun g ↦ LinearMap.ext (hintertwines g))

/-- Binary-plane uniqueness with only kernel-checked finite inputs. -/
noncomputable def representationEquiv_of_card_three_or_six_at
    {p : ℕ} [Fact p.Prime]
    {G V W : Type} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
    [AddCommGroup W] [Module (ZMod p) W] [FiniteDimensional (ZMod p) W]
    (hp : p = 2)
    (rho : Representation (ZMod p) G V)
    (sigma : Representation (ZMod p) G W)
    (hG : Nat.card G = 3 ∨ Nat.card G = 6)
    (hV : Module.finrank (ZMod p) V = 2)
    (hW : Module.finrank (ZMod p) W = 2)
    (hrho : Function.Injective rho) (hsigma : Function.Injective sigma) :
    rho.Equiv sigma := by
  subst p
  by_cases h3 : Nat.card G = 3
  · exact binaryPlaneRepresentationEquiv_of_card_three rho sigma h3 hV hW hrho hsigma
  · exact representationEquiv_of_card_six rho sigma (hG.resolve_left h3) hV hW hrho hsigma

theorem not_commutative_of_card_six
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
      ⟨hphi, hG.trans card.symm⟩
  intro hcomm
  apply binaryPlaneGL_not_isMulCommutative
  refine { is_comm.comm := fun A B => ?_ }
  obtain ⟨a, rfl⟩ := hbij.surjective A
  obtain ⟨b, rfl⟩ := hbij.surjective B
  rw [← map_mul, ← map_mul, hcomm.is_comm.comm a b]

theorem not_commutative_of_card_six_at
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
  exact not_commutative_of_card_six
    rho hG hV hrho

end SymmetricSubgroupAsymptotics.BinaryPlaneKernelClassification

end
