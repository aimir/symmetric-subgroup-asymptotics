import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryIntrinsicRootStars
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitarySubspaceAction

/-! Inner automorphisms of the ORIGINAL projective group act on its
reconstructed singular points by the SAME literal natural matrices.
The proof uses exact original central-root labels and the representative
product g*h. No polar-recognition or semilinear hypothesis enters. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent

private theorem conjugate_subgroup_mul {G : Type*} [Group G] (H : Subgroup G) (g h : G) :
    (H.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      H.map (MulAut.conj (g * h)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  apply MonoidHom.ext
  intro x
  change g * (h * x * h⁻¹) * g⁻¹ = (g * h) * x * (g * h)⁻¹
  simp only [_root_.mul_inv_rev, mul_assoc]

private theorem conjugate_subgroup_hom_mul {A G : Type*} [Group A] [Group G]
    (pi : A →* G) (H : Subgroup G) (g h : A) :
    (H.map (MulAut.conj (pi h)).toMonoidHom).map (MulAut.conj (pi g)).toMonoidHom =
      H.map (MulAut.conj (pi (g * h))).toMonoidHom := by
  exact (conjugate_subgroup_mul H (pi g) (pi h)).trans
    (congrArg (fun x : G => H.map (MulAut.conj x).toMonoidHom) (pi.map_mul g h).symm)

def unitaryNaturalPointMap (q : CFSG.PrimePower) (s : ℕ)
    (g : naturalFixed (s + 3) q) :
    (Fin (s + 4) → q.Extension 2) →ₗ[q.Extension 2] (Fin (s + 4) → q.Extension 2) :=
  Matrix.mulVecLin (g.val.val : Mat (q.Extension 2) (s + 3))

def unitaryNaturalSingularPoint (q : CFSG.PrimePower) (s : ℕ)
    (g : naturalFixed (s + 3) q) (P : unitarySingularPoints q s) : unitarySingularPoints q s :=
  ⟨P.val.map (unitaryNaturalLinearEquiv q (s + 3) g).toLinearMap,
    ((unitaryNaturalLinearEquiv q (s + 3) g).finrank_map_eq P.val).trans P.property.1, by
      rintro x ⟨y, hy, rfl⟩
      exact (unitaryNaturalLinearEquiv_pair q (s + 3) g y y).trans (P.property.2 y hy)⟩

theorem conjugateCentralPoint_product_map (q : CFSG.PrimePower) (s : ℕ)
    (g h : naturalFixed (s + 3) q) :
    conjugateCentralPoint q (s + 1) (g * h) =
      (conjugateCentralPoint q (s + 1) h).map
        (unitaryNaturalLinearEquiv q (s + 3) g).toLinearMap := by
  rw [conjugateCentralPoint_eq_span, conjugateCentralPoint_eq_span,
    Submodule.map_span, Set.image_singleton]
  apply congrArg (fun x : Fin (s + 4) → q.Extension 2 => (q.Extension 2) ∙ x)
  change ((g.val.val : Mat (q.Extension 2) (s + 3)) *
      (h.val.val : Mat (q.Extension 2) (s + 3))) *ᵥ Pi.single 0 1 =
    (g.val.val : Mat (q.Extension 2) (s + 3)) *ᵥ
      ((h.val.val : Mat (q.Extension 2) (s + 3)) *ᵥ Pi.single 0 1)
  exact (Matrix.mulVec_mulVec _ _ _).symm

def unitaryCentralPointOfRepresentative (q : CFSG.PrimePower) (s : ℕ)
    (h : naturalFixed (s + 3) q) : unitaryCentralPoints q s :=
  ⟨conjugateCentralPoint q (s + 1) h, ⟨h, rfl⟩⟩

theorem unitaryCentralPointOfRepresentative_label (q : CFSG.PrimePower) (s : ℕ)
    (h : naturalFixed (s + 3) q) :
    unitaryCentralPointLabel q s (unitaryCentralPointOfRepresentative q s h) =
      conjugateProjectiveCentralRootLine q s (unitaryProjectiveCover q s h) :=
  unitaryCentralPointLabel_representative q s (unitaryCentralPointOfRepresentative q s h) h rfl

theorem unitaryCentralPointAction_inner_representative (q : CFSG.PrimePower) (s : ℕ)
    (g h : naturalFixed (s + 3) q) :
    unitaryCentralPointActionHom q s (MulAut.conj (unitaryProjectiveCover q s g))
      (unitaryCentralPointOfRepresentative q s h) =
      unitaryCentralPointOfRepresentative q s (g * h) := by
  apply unitaryCentralPointLabel_injective q s
  rw [unitaryCentralPointAction_label, unitaryCentralPointOfRepresentative_label,
    unitaryCentralPointOfRepresentative_label]
  exact conjugate_subgroup_hom_mul (unitaryProjectiveCover q s)
    (projectiveCentralRootLine q s) g h

theorem unitaryCentralPointAction_inner (q : CFSG.PrimePower) (s : ℕ)
    (g : naturalFixed (s + 3) q) (P : unitaryCentralPoints q s) :
    (unitaryCentralPointActionHom q s (MulAut.conj (unitaryProjectiveCover q s g)) P).val =
      P.val.map (unitaryNaturalPointMap q s g) := by
  obtain ⟨h, hh⟩ := P.property
  have heP : P = unitaryCentralPointOfRepresentative q s h := Subtype.ext hh.symm
  have he := congrArg (fun T : unitaryCentralPoints q s => T.val)
    (unitaryCentralPointAction_inner_representative q s g h)
  dsimp only at he
  rw [heP, he]
  exact conjugateCentralPoint_product_map q s g h

private theorem subtype_permCongr_value {V : Type*} (A B : V → Prop)
    (e : {v // A v} ≃ {v // B v}) (he : ∀ x, (e x).val = x.val)
    (f : Equiv.Perm {v // A v}) (y : {v // B v}) :
    ((e.permCongrHom f) y).val = (f (e.symm y)).val :=
  he (f (e.symm y))

theorem unitarySingularPointAction_value (q : CFSG.PrimePower) (s : ℕ)
    (f : MulAut (CFSG.Models.TwistedA (s + 3) q)) (P : unitarySingularPoints q s) :
    (unitarySingularPointActionHom q s f P).val =
      (unitaryCentralPointActionHom q s f ((unitaryCentralSingularPointEquiv q s).symm P)).val :=
  subtype_permCongr_value _ _ (unitaryCentralSingularPointEquiv q s) (fun _ => rfl)
    (unitaryCentralPointActionHom q s f) P

theorem unitarySingularPointAction_inner (q : CFSG.PrimePower) (s : ℕ)
    (g : naturalFixed (s + 3) q) (P : unitarySingularPoints q s) :
    (unitarySingularPointActionHom q s (MulAut.conj (unitaryProjectiveCover q s g)) P).val =
      P.val.map (unitaryNaturalPointMap q s g) := by
  rw [unitarySingularPointAction_value]
  exact unitaryCentralPointAction_inner q s g ((unitaryCentralSingularPointEquiv q s).symm P)

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
