import SymmetricSubgroupAsymptotics.CoinducedQuotientPullback

/-! Exact transport of a coinduced frame through an ambient group
equivalence, a commuting stabilizer equivalence, and an actual local
representation equivalence. No abstract group identification alone suffices.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CoinducedGroupLocalTransport

variable {k G Q V W : Type} [Field k] [Group G] [Group Q]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  (H : Subgroup G) (L : Subgroup Q) (eG : G ≃* Q) (eH : H ≃* L)
  (commutes : ∀ h : H, eG (h : G) = (eH h : Q))
  (rho : Representation k H V) (sigma : Representation k L W)
  (eV : Representation.Equiv rho (sigma.comp eH.toMonoidHom))

include commutes in
private theorem inverse_stabilizer (l : L) :
    eG.symm (l : Q) = (eH.symm l : G) := by
  apply eG.injective
  rw [eG.apply_symm_apply, commutes, eH.apply_symm_apply]

/-- The target function is evaluated at the exact inverse ambient image. -/
def intertwiner : Representation.IntertwiningMap
    (Representation.coind H.subtype rho)
    ((Representation.coind L.subtype sigma).comp eG.toMonoidHom) where
  toLinearMap := {
    toFun f := ⟨fun q => eV (f.1 (eG.symm q)), by
      intro l q
      change eV (f.1 (eG.symm ((l : Q) * q))) =
        sigma l (eV (f.1 (eG.symm q)))
      rw [map_mul, inverse_stabilizer H L eG eH commutes]
      change eV (f.1 (H.subtype (eH.symm l) * eG.symm q)) =
        sigma l (eV (f.1 (eG.symm q)))
      rw [f.2 (eH.symm l) (eG.symm q)]
      have he := Representation.IntertwiningMap.isIntertwining _ _
        eV.toIntertwiningMap (eH.symm l) (f.1 (eG.symm q))
      simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        eH.apply_symm_apply] using he⟩
    map_add' f g := by
      apply Subtype.ext
      funext q
      exact map_add eV _ _
    map_smul' c f := by
      apply Subtype.ext
      funext q
      exact map_smul eV c _ }
  isIntertwining' g := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext q
    change eV (f.1 (eG.symm q * g)) = eV (f.1 (eG.symm (q * eG g)))
    rw [map_mul, eG.symm_apply_apply]

theorem intertwiner_injective :
    Function.Injective (intertwiner (H := H) (L := L) (eG := eG) (eH := eH)
      (commutes := commutes) (rho := rho) (sigma := sigma) (eV := eV)) := by
  intro f g hfg
  apply Subtype.ext
  funext x
  apply eV.injective
  have h := congrArg
    (fun f : Representation.coindV L.subtype sigma => f.1 (eG x)) hfg
  change eV (f.1 (eG.symm (eG x))) = eV (g.1 (eG.symm (eG x))) at h
  simpa only [eG.symm_apply_apply] using h

include eG eH commutes eV in
/-- Uniform head bounds transport only after both original stabilizer and
local action have been identified equivariantly. -/
theorem uniform_head_le
    [Finite G] [Finite Q] [FiniteDimensional k V] [FiniteDimensional k W]
    (cap : ℕ)
    (hcap : ∀ A : Subrepresentation (Representation.coind L.subtype sigma),
      Module.finrank k
        (A.toRepresentation.IntertwiningMap (Representation.trivial k Q k)) ≤ cap)
    (B : Subrepresentation (Representation.coind H.subtype rho)) :
    Module.finrank k
      (B.toRepresentation.IntertwiningMap (Representation.trivial k G k)) ≤ cap := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  letI : Fintype Q := Fintype.ofFinite Q
  letI : FiniteDimensional k (Representation.coindV H.subtype rho) :=
    FiniteDimensional.of_injective (Representation.coindV H.subtype rho).subtype
      (Representation.coindV H.subtype rho).subtype_injective
  letI : FiniteDimensional k (Representation.coindV L.subtype sigma) :=
    FiniteDimensional.of_injective (Representation.coindV L.subtype sigma).subtype
      (Representation.coindV L.subtype sigma).subtype_injective
  exact uniformSubrepresentationHeadBound_of_injective
    (Representation.coind H.subtype rho)
    ((Representation.coind L.subtype sigma).comp eG.toMonoidHom)
    (intertwiner (H := H) (L := L) (eG := eG) (eH := eH)
      (commutes := commutes) (rho := rho) (sigma := sigma) (eV := eV))
    (intertwiner_injective (H := H) (L := L) (eG := eG) (eH := eH)
      (commutes := commutes) (rho := rho) (sigma := sigma) (eV := eV)) cap
    (CoinducedQuotientPullback.uniform_head_comp_surjective eG.toMonoidHom
      eG.surjective (Representation.coind L.subtype sigma) cap hcap) B

end SymmetricSubgroupAsymptotics.CoinducedGroupLocalTransport

end
