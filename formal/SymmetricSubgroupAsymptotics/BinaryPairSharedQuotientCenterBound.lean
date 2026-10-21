import SymmetricSubgroupAsymptotics.BinaryPairQuotientCenterProjection

/-! Transfer a JOINT fixed-vector/top capacity through the actual retained
top isomorphism. The denominator is the original coordinate normal and
all affine lift offsets are retained. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X H : Type} [Finite X] [Group H] [Finite H]
    {w : ℕ} {U : Subgroup (Equiv.Perm X)} (F : BinaryPairFrame U (Fin w))

theorem shared_quotient_center_card_le
    (rho : Representation (ZMod 2) H (Fin w → ZMod 2))
    (e : H ≃* F.top.range)
    (he : ∀ g v, rho g v = F.coordinateTopAction (e g) v)
    (K : Submodule (ZMod 2) (Fin w → ZMod 2)) (hK : K = F.kernelSpace)
    (A : Subrepresentation rho) (hA : A.toSubmodule ≤ K) (c : ℕ)
    (hcapacity :
      Nat.card {v : Fin w → ZMod 2 // v ∈ K ∧ ∀ t : H, rho t v - v ∈ A.toSubmodule} *
        Nat.card {t : H // ∀ v, v ∈ K → rho t v - v ∈ A.toSubmodule} ≤
        c * Nat.card A.toSubmodule) :
    Nat.card (Subgroup.center
      (U ⧸ F.coordinateSubgroup (F.sharedSubrepresentation rho e he A).toSubmodule)) ≤ c := by
  let B := F.sharedSubrepresentation rho e he A
  have hb := F.quotient_center_card_mul_le_coordinate_product B (hA.trans_eq hK)
  let fv : {v : Fin w → ZMod 2 // v ∈ F.kernelSpace ∧
      ∀ t : F.top.range, F.coordinateTopAction t v - v ∈ B.toSubmodule} →
      {v : Fin w → ZMod 2 // v ∈ K ∧ ∀ t : H, rho t v - v ∈ A.toSubmodule} :=
    fun v => ⟨v.val, by
      refine ⟨hK.symm ▸ v.property.1, ?_⟩
      intro t
      rw [he]
      exact v.property.2 (e t)⟩
  have hfv : Function.Injective fv := by
    intro x y h
    exact Subtype.ext (congrArg
      (fun v : {v : Fin w → ZMod 2 // v ∈ K ∧ ∀ t : H,
        rho t v - v ∈ A.toSubmodule} => v.val) h)
  let ft : {t : F.top.range // ∀ v, v ∈ F.kernelSpace →
      F.coordinateTopAction t v - v ∈ B.toSubmodule} →
      {t : H // ∀ v, v ∈ K → rho t v - v ∈ A.toSubmodule} := fun t =>
    ⟨e.symm t.val, by
      intro v hv
      rw [he, e.apply_symm_apply]
      exact t.property v (hK ▸ hv)⟩
  have hft : Function.Injective ft := by
    intro x y h
    apply Subtype.ext
    apply e.symm.injective
    exact congrArg (fun t : {t : H // ∀ v, v ∈ K →
      rho t v - v ∈ A.toSubmodule} => t.val) h
  have hprod := Nat.mul_le_mul
    (Nat.card_le_card_of_injective fv hfv) (Nat.card_le_card_of_injective ft hft)
  have hbound := hb.trans (hprod.trans hcapacity)
  have hpos : 0 < Nat.card A.toSubmodule := Nat.card_pos
  change Nat.card A.toSubmodule * _ ≤ c * Nat.card A.toSubmodule at hbound
  nlinarith

end SymmetricSubgroupAsymptotics.BinaryPairFrame
