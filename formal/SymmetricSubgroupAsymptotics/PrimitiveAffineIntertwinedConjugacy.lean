import SymmetricSubgroupAsymptotics.PrimitiveAffineProfileStructure
import SymmetricSubgroupAsymptotics.OrbitProfileAssembly

/-!
# Actual affine point conjugacy from intertwined factors

An abstract complement isomorphism alone does not determine an affine action.
This file retains the isomorphism of the actual regular translation groups
and its compatibility with the actual point-stabilizer conjugation actions.
It constructs both the ambient group isomorphism and the equivariant point
bijection, and hence actual permutation conjugacy. No classification premise
or representative-coverage statement is introduced.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineIntertwinedConjugacy

variable {G H X Y : Type} [Group G] [Group H] [MulAction G X] [MulAction H Y]
  (P : PrimitiveAffineProfile G X) (Q : PrimitiveAffineProfile H Y)
  (x : X) (y : Y)

/-- The actual translation chart identifies the two original point sets. -/
def points (a : P.V ≃* Q.V) : X ≃ Y :=
  (P.pointEquiv x).symm.trans (a.toEquiv.trans (Q.pointEquiv y))

@[simp] theorem points_translation (a : P.V ≃* Q.V) (v : P.V) :
    points P Q x y a (P.pointEquiv x v) = Q.pointEquiv y (a v) := by
  simp only [points, Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl

private theorem stabilizer_translation
    (k : P.complement x) (v : P.V) :
    (k : G) • P.pointEquiv x v =
      P.pointEquiv x (P.complementAction x k v) := by
  change (k : G) • ((v : G) • x) =
    ((k : G) * (v : G) * (k : G)⁻¹) • x
  have hk : (k : G)⁻¹ • x = x := by
    calc
      (k : G)⁻¹ • x = (k : G)⁻¹ • ((k : G) • x) :=
        congrArg ((k : G)⁻¹ • ·) k.property.symm
      _ = x := inv_smul_smul _ _
  rw [mul_smul, mul_smul, hk]

private theorem semidirect_translation
    (u : P.V ⋊[P.complementAction x] P.complement x) (v : P.V) :
    P.semidirectEquiv x u • P.pointEquiv x v =
      P.pointEquiv x (u.left * P.complementAction x u.right v) := by
  have hu : P.semidirectEquiv x u = (u.left : G) * (u.right : G) := rfl
  rw [hu, mul_smul, stabilizer_translation]
  exact (mul_smul (u.left : G) (P.complementAction x u.right v : G) x).symm

/-- Intertwined actual translation/stabilizer factors identify the whole
original groups through their internal semidirect decompositions. -/
def groupEquiv (a : P.V ≃* Q.V)
    (b : P.complement x ≃* Q.complement y)
    (hab : ∀ k v, a (P.complementAction x k v) =
      Q.complementAction y (b k) (a v)) : G ≃* H :=
  (P.semidirectEquiv x).symm.trans
    ((SemidirectProduct.congr a b (by
      intro k
      apply MulEquiv.ext
      intro v
      exact hab k v)).trans (Q.semidirectEquiv y))

/-- The constructed group and point charts preserve the actual actions. -/
theorem groupEquiv_action (a : P.V ≃* Q.V)
    (b : P.complement x ≃* Q.complement y)
    (hab : ∀ k v, a (P.complementAction x k v) =
      Q.complementAction y (b k) (a v)) (g : G) (z : X) :
    groupEquiv P Q x y a b hab g • points P Q x y a z =
      points P Q x y a (g • z) := by
  obtain ⟨u,rfl⟩ := (P.semidirectEquiv x).surjective g
  obtain ⟨v,rfl⟩ := (P.pointEquiv x).surjective z
  simp only [groupEquiv, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    points_translation]
  rw [semidirect_translation, semidirect_translation]
  simp only [points_translation, map_mul, hab]
  rfl

/-- Any equivariant group/point equivalences between actual permutation
subgroups identify the relabelled subgroups themselves. -/
theorem relabel_eq_of_equivariant
    {X Y : Type} (S : Subgroup (Equiv.Perm X)) (T : Subgroup (Equiv.Perm Y))
    (e : S ≃* T) (c : X ≃ Y)
    (he : ∀ s : S, ∀ z : X, (e s).val (c z) = c (s.val z)) :
    relabelSubgroup c S = T := by
  have hp (s : S) : c.permCongr s.val = (e s).val := by
    ext z
    obtain ⟨w,rfl⟩ := c.surjective z
    simpa only [Equiv.permCongr_apply, Equiv.symm_apply_apply] using (he s w).symm
  ext p
  change p ∈ S.map c.permCongrHom.toMonoidHom ↔ p ∈ T
  constructor
  · rintro ⟨s,hs,rfl⟩
    change c.permCongr s ∈ T
    rw [hp ⟨s,hs⟩]
    exact (e ⟨s,hs⟩).property
  · intro h
    obtain ⟨s,hs⟩ := e.surjective ⟨p,h⟩
    exact ⟨s.val,s.property,(hp s).trans (congrArg Subtype.val hs)⟩

/-- An intertwiner of the actual affine factors gives actual point
relabeling of the literal permutation subgroups. -/
theorem affine_relabel_eq
    {X Y : Type} (S : Subgroup (Equiv.Perm X)) (T : Subgroup (Equiv.Perm Y))
    (P : PrimitiveAffineProfile S X) (Q : PrimitiveAffineProfile T Y)
    (x : X) (y : Y) (a : P.V ≃* Q.V)
    (b : P.complement x ≃* Q.complement y)
    (hab : ∀ k v, a (P.complementAction x k v) =
      Q.complementAction y (b k) (a v)) :
    relabelSubgroup (points P Q x y a) S = T :=
  relabel_eq_of_equivariant S T (groupEquiv P Q x y a b hab)
    (points P Q x y a) (groupEquiv_action P Q x y a b hab)

/-- At a fixed finite degree the point chart is the required ambient
permutation conjugator, rather than only an abstract group isomorphism. -/
theorem affine_conjugate_eq
    {X : Type} (S T : Subgroup (Equiv.Perm X))
    (P : PrimitiveAffineProfile S X) (Q : PrimitiveAffineProfile T X)
    (x y : X) (a : P.V ≃* Q.V)
    (b : P.complement x ≃* Q.complement y)
    (hab : ∀ k v, a (P.complementAction x k v) =
      Q.complementAction y (b k) (a v)) :
    MulAut.conj (points P Q x y a) • S = T := by
  change S.map (MulAut.conj (points P Q x y a)).toMonoidHom = T
  exact affine_relabel_eq S T P Q x y a b hab

end SymmetricSubgroupAsymptotics.PrimitiveAffineIntertwinedConjugacy

end
