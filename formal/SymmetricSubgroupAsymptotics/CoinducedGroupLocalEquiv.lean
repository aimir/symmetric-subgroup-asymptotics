import SymmetricSubgroupAsymptotics.CoinducedGroupLocalTransport

/-! Exact coinduced transport through the original group, stabilizer and
local-plane charts. The forward map is the existing checked intertwiner;
the inverse function uses the exact forward ambient point and local chart. -/

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

theorem intertwiner_surjective :
    Function.Surjective (intertwiner (H := H) (L := L) (eG := eG) (eH := eH)
      (commutes := commutes) (rho := rho) (sigma := sigma) (eV := eV)) := by
  intro t
  let s : Representation.coindV H.subtype rho := ⟨fun g => eV.symm (t.1 (eG g)), by
    intro h g
    change eV.symm (t.1 (eG ((h : G) * g))) = rho h (eV.symm (t.1 (eG g)))
    rw [map_mul, commutes h]
    have ht := t.2 (eH h) (eG g)
    change t.1 ((eH h : Q) * eG g) = sigma (eH h) (t.1 (eG g)) at ht
    rw [ht]
    have he := Representation.IntertwiningMap.isIntertwining _ _
      eV.symm.toIntertwiningMap h (t.1 (eG g))
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] using he⟩
  refine ⟨s, ?_⟩
  apply Subtype.ext
  funext q
  change eV (eV.symm (t.1 (eG (eG.symm q)))) = t.1 q
  rw [eG.apply_symm_apply, eV.apply_symm_apply]

def equivalence : Representation.Equiv
    (Representation.coind H.subtype rho)
    ((Representation.coind L.subtype sigma).comp eG.toMonoidHom) :=
  (intertwiner (H := H) (L := L) (eG := eG) (eH := eH)
    (commutes := commutes) (rho := rho) (sigma := sigma) (eV := eV)).ofBijective
    ⟨intertwiner_injective (H := H) (L := L) (eG := eG) (eH := eH)
        (commutes := commutes) (rho := rho) (sigma := sigma) (eV := eV),
      intertwiner_surjective (H := H) (L := L) (eG := eG) (eH := eH)
        (commutes := commutes) (rho := rho) (sigma := sigma) (eV := eV)⟩

end SymmetricSubgroupAsymptotics.CoinducedGroupLocalTransport

end
