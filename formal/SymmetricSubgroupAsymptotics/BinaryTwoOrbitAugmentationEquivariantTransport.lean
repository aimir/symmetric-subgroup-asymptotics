import SymmetricSubgroupAsymptotics.BinaryTwoOrbitAugmentationTransport

/-!
# Equivariant transport of two-orbit augmentation modules

The point relabelling used by the split frontier is accompanied by an
equivalence between the old kernel axis and its conjugate.  This file records
the corresponding transport without requiring either acting group to be the
full permutation subgroup on its point set.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics

/-- An equivariant pair of group and point equivalences carries actual orbit
classes bijectively. -/
def equivariantOrbitEquiv {G H X Y : Type} [Group G] [Group H]
    [MulAction G X] [MulAction H Y]
    (A : Subgroup G) (B : Subgroup H) (φ : A ≃* B) (e : X ≃ Y)
    (he : ∀ g x,e (g • x)=φ g • e x) :
    MulAction.orbitRel.Quotient A X ≃ MulAction.orbitRel.Quotient B Y where
  toFun := Quotient.map' e (by
    intro x y hxy
    rw [MulAction.orbitRel_apply] at hxy ⊢
    obtain ⟨g,hg⟩ := MulAction.mem_orbit_iff.mp hxy
    apply MulAction.mem_orbit_iff.mpr
    exact ⟨φ g,(he g y).symm.trans (congrArg e hg)⟩)
  invFun := Quotient.map' e.symm (by
    intro x y hxy
    rw [MulAction.orbitRel_apply] at hxy ⊢
    obtain ⟨h,hh⟩ := MulAction.mem_orbit_iff.mp hxy
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨φ.symm h,?_⟩
    apply e.injective
    rw [he,φ.apply_symm_apply,e.apply_symm_apply,e.apply_symm_apply]
    exact hh)
  left_inv := by
    intro o
    induction o using Quotient.inductionOn'
    simp only [Quotient.map'_mk'',e.symm_apply_apply]
  right_inv := by
    intro o
    induction o using Quotient.inductionOn'
    simp only [Quotient.map'_mk'',e.apply_symm_apply]

/-- The same point equivalence restricts to corresponding literal orbit
subtypes. -/
def equivariantOrbitPointEquiv {G H X Y : Type} [Group G] [Group H]
    [MulAction G X] [MulAction H Y]
    (A : Subgroup G) (B : Subgroup H) (φ : A ≃* B) (e : X ≃ Y)
    (he : ∀ g x,e (g • x)=φ g • e x)
    (o : MulAction.orbitRel.Quotient A X) :
    o.orbit ≃ (equivariantOrbitEquiv A B φ e he o).orbit where
  toFun x := ⟨e x,by
    apply MulAction.orbitRel.Quotient.mem_orbit.mpr
    have hx := MulAction.orbitRel.Quotient.mem_orbit.mp x.property
    calc
      Quotient.mk'' (e x.val)=
          equivariantOrbitEquiv A B φ e he (Quotient.mk'' x.val) := rfl
      _ = equivariantOrbitEquiv A B φ e he o :=
        congrArg (equivariantOrbitEquiv A B φ e he) hx⟩
  invFun y := ⟨e.symm y,by
    apply MulAction.orbitRel.Quotient.mem_orbit.mpr
    have hy := MulAction.orbitRel.Quotient.mem_orbit.mp y.property
    apply (equivariantOrbitEquiv A B φ e he).injective
    calc
      equivariantOrbitEquiv A B φ e he (Quotient.mk'' (e.symm y.val))=
          Quotient.mk'' y.val := by
        change Quotient.mk'' (e (e.symm y.val))=Quotient.mk'' y.val
        rw [e.apply_symm_apply]
      _ = equivariantOrbitEquiv A B φ e he o := hy⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv y := Subtype.ext (e.apply_symm_apply y.val)

theorem orbitSum_binaryFunctionRelabel_equivariant
    {G H X Y : Type} [Group G] [Group H]
    [MulAction G X] [MulAction H Y] [Fintype X] [Fintype Y]
    (A : Subgroup G) (B : Subgroup H) (φ : A ≃* B) (e : X ≃ Y)
    (he : ∀ g x,e (g • x)=φ g • e x)
    (o : MulAction.orbitRel.Quotient A X) (a : X → ZMod 2) :
    PermutationBinaryTwoOrbitSplit.orbitSum B
        (equivariantOrbitEquiv A B φ e he o) (binaryFunctionRelabel e a)=
      PermutationBinaryTwoOrbitSplit.orbitSum A o a := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  letI : Fintype Y := Fintype.ofFinite Y
  have hsum := Equiv.sum_comp (equivariantOrbitPointEquiv A B φ e he o)
    (fun y : (equivariantOrbitEquiv A B φ e he o).orbit =>
      (binaryFunctionRelabel e a) y.val)
  change (∑ y : (equivariantOrbitEquiv A B φ e he o).orbit,
      (binaryFunctionRelabel e a) y.val)=∑ x : o.orbit,a x.val
  have hright :
      (∑ x : o.orbit,(binaryFunctionRelabel e a)
        (equivariantOrbitPointEquiv A B φ e he o x).val)=∑ x : o.orbit,a x.val := by
    apply Finset.sum_congr rfl
    intro x _
    change a (e.symm (e x.val))=a x.val
    rw [e.symm_apply_apply]
  exact hsum.symm.trans hright

/-- Two-orbit augmentation is natural for every equivariant group/point
equivalence, including the restricted axis equivalence supplied by ambient
conjugacy. -/
theorem binaryRelabelModule_twoOrbitAugmentation_equivariant
    {G H X Y : Type} [Group G] [Group H]
    [MulAction G X] [MulAction H Y] [Fintype X] [Fintype Y]
    (A : Subgroup G) (B : Subgroup H) (φ : A ≃* B) (e : X ≃ Y)
    (he : ∀ g x,e (g • x)=φ g • e x)
    (o₁ o₂ : MulAction.orbitRel.Quotient A X) :
    binaryRelabelModule e
        (PermutationBinaryTwoOrbitSplit.twoOrbitAugmentation A o₁ o₂)=
      PermutationBinaryTwoOrbitSplit.twoOrbitAugmentation B
        (equivariantOrbitEquiv A B φ e he o₁)
        (equivariantOrbitEquiv A B φ e he o₂) := by
  ext a
  constructor
  · rintro ⟨b,hb,rfl⟩
    change (_,_)=(0,0)
    change (_,_)=(0,0) at hb
    apply Prod.ext
    · exact (orbitSum_binaryFunctionRelabel_equivariant A B φ e he o₁ b).trans
        (congrArg Prod.fst hb)
    · exact (orbitSum_binaryFunctionRelabel_equivariant A B φ e he o₂ b).trans
        (congrArg Prod.snd hb)
  · intro ha
    let b : X → ZMod 2 := (binaryFunctionRelabel e).symm a
    refine ⟨b,?_,?_⟩
    · change (_,_)=(0,0)
      change (_,_)=(0,0) at ha
      have h₁ := orbitSum_binaryFunctionRelabel_equivariant A B φ e he o₁ b
      have h₂ := orbitSum_binaryFunctionRelabel_equivariant A B φ e he o₂ b
      rw [(binaryFunctionRelabel e).apply_symm_apply] at h₁ h₂
      apply Prod.ext
      · exact h₁.symm.trans (congrArg Prod.fst ha)
      · exact h₂.symm.trans (congrArg Prod.snd ha)
    · exact (binaryFunctionRelabel e).apply_symm_apply a

end SymmetricSubgroupAsymptotics
