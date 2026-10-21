import SymmetricSubgroupAsymptotics.CFSGSolubleWreathContainersAction
import SymmetricSubgroupAsymptotics.FaithfulFiniteActionImage
import SymmetricSubgroupAsymptotics.ActualBlockWreathEmbedding

/-! Relabel an actual wreath coordinate action into actual labelled local
and top containers. The original whole-source action is kept through its
explicit equivariant product-point equivalence. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGSolubleWreathContainers

variable {F I : Type} {r s : ℕ}
    (D : Subgroup (Equiv.Perm F)) (Q : Subgroup (Equiv.Perm I))
    (eF : F ≃ Fin r) (eI : I ≃ Fin s)
    (D' : Subgroup (Equiv.Perm (Fin r))) (Q' : Subgroup (Equiv.Perm (Fin s)))
    (hD : ∀ d : D, eF.permCongrHom (d : Equiv.Perm F) ∈ D')
    (hQ : ∀ q : Q, eI.permCongrHom (q : Equiv.Perm I) ∈ Q')

def coveredWreathElement (w : PermutationalWreathProduct D Q I) :
    PermutationalWreathProduct D' Q' (Fin s) :=
  ⟨fun j => ⟨eF.permCongrHom (w.left (eI.symm j) : Equiv.Perm F),
      hD (w.left (eI.symm j))⟩,
    ⟨eI.permCongrHom (w.right : Equiv.Perm I), hQ w.right⟩⟩

def productLabels : F × I ≃ Fin (r * s) :=
  (Equiv.prodCongr eF eI).trans finProdFinEquiv

theorem coveredWreathElement_point (w : PermutationalWreathProduct D Q I) (p : F × I) :
    PermutationalWreathProduct.toFinPerm (u := r) (s := s) D' Q'
      (coveredWreathElement D Q eF eI D' Q' hD hQ w) (productLabels eF eI p) =
        productLabels eF eI (w • p) := by
  rcases p with ⟨v, i⟩
  change finProdFinEquiv
      (PermutationalWreathProduct.toPerm
        (coveredWreathElement D Q eF eI D' Q' hD hQ w)
        (finProdFinEquiv.symm (finProdFinEquiv (eF v, eI i)))) = _
  rw [Equiv.symm_apply_apply]
  change finProdFinEquiv
      (eF (((w.left (eI.symm (eI ((w.right : Equiv.Perm I) (eI.symm (eI i)))))) :
          Equiv.Perm F) (eF.symm (eF v))),
       eI ((w.right : Equiv.Perm I) (eI.symm (eI i)))) =
    finProdFinEquiv
      (eF (((w.left ((w.right : Equiv.Perm I) i)) : Equiv.Perm F) v),
        eI ((w.right : Equiv.Perm I) i))
  simp only [Equiv.symm_apply_apply]

include hD hQ in
theorem action_image_le_wreathEnvelope {G X : Type} [Group G] [MulAction G X]
    (rho : G →* PermutationalWreathProduct D Q I) (points : F × I ≃ X)
    (hpoints : ∀ g p, points (rho g • p) = g • points p) :
    labelledActionImage (A := G) (points.symm.trans (productLabels eF eI)) ≤
      wreathEnvelope D' Q' := by
  rintro _ ⟨g, rfl⟩
  refine ⟨coveredWreathElement D Q eF eI D' Q' hD hQ (rho g), ?_⟩
  apply Equiv.ext
  intro z
  obtain ⟨p, rfl⟩ := (productLabels eF eI).surjective z
  have hright : labelledActionHom (A := G) (points.symm.trans (productLabels eF eI)) g
      (productLabels eF eI p) = productLabels eF eI (rho g • p) := by
    change productLabels eF eI
      (points.symm (g • points ((productLabels eF eI).symm (productLabels eF eI p)))) = _
    rw [Equiv.symm_apply_apply, ← hpoints, Equiv.symm_apply_apply]
  rw [hright]
  exact coveredWreathElement_point D Q eF eI D' Q' hD hQ (rho g) p

end SymmetricSubgroupAsymptotics.CFSGSolubleWreathContainers
