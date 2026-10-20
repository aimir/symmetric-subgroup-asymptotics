import SymmetricSubgroupAsymptotics.FullBinaryLocalFlipUniquePairs

/-! The full binary doubling of an ORIGINAL transitive permutation group.
It is defined as all original permutations lying above that physical top,
so all local flips are present without enumerating a 2^n-element base.
Its unique invariant pairing will let an existential catalogue realization
recover the original top. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.FullBinaryDoubling
variable {I : Type} (U : Subgroup (Equiv.Perm I))

/-- The full physical binary wreath preimage, with the original top kept. -/
def group : Subgroup (Equiv.Perm (I × ZMod 2)) where
  carrier := {a | ∃ u : U,∀ x,(a x).1=(u : Equiv.Perm I) x.1}
  one_mem' := ⟨1,fun _ => rfl⟩
  mul_mem' := by
    rintro a b ⟨u,hu⟩ ⟨v,hv⟩
    refine ⟨u*v,?_⟩
    intro x
    change (a (b x)).1=(u : Equiv.Perm I) ((v : Equiv.Perm I) x.1)
    rw [hu,hv]
  inv_mem' := by
    rintro a ⟨u,hu⟩
    refine ⟨u⁻¹,?_⟩
    intro x
    apply (u : Equiv.Perm I).injective
    have h := hu (a⁻¹ x)
    have ha : a (a⁻¹ x)=x := a.apply_symm_apply x
    rw [ha] at h
    exact h.symm.trans ((u : Equiv.Perm I).apply_symm_apply x.1).symm

def top (g : group U) : U := Classical.choose g.property

theorem top_spec (g : group U) (x : I × ZMod 2) :
    (g.val x).1=(top U g : Equiv.Perm I) x.1 := Classical.choose_spec g.property x

def topHom : group U →* U where
  toFun := top U
  map_one' := by
    apply Subtype.ext
    apply Equiv.ext
    intro i
    exact (top_spec U 1 (i,0)).symm
  map_mul' a b := by
    apply Subtype.ext
    apply Equiv.ext
    intro i
    have h := top_spec U (a*b) (i,0)
    change (a.val (b.val (i,0))).1=(top U (a*b) : Equiv.Perm I) i at h
    rw [top_spec U a,top_spec U b] at h
    exact h.symm

theorem top_surjective : Function.Surjective (topHom U) := by
  intro u
  let a : group U := ⟨Equiv.prodCongr (u : Equiv.Perm I) (Equiv.refl (ZMod 2)),u,fun _ => rfl⟩
  refine ⟨a,?_⟩
  apply Subtype.ext
  apply Equiv.ext
  intro i
  exact (top_spec U a (i,0)).symm

theorem localFlip_mem (i : I) : FullBinaryLocalFlipUniquePairs.localFlip i∈group U :=
  ⟨1,fun _ => rfl⟩

def frame : BinaryPairFrame (group U) I where
  frame := Equiv.refl _
  top := U.subtype.comp (topHom U)
  intertwine := top_spec U

/-- The doubled original action is transitive whenever the original is. -/
theorem transitive [MulAction.IsPretransitive U I] :
    MulAction.IsPretransitive (group U) (I × ZMod 2) := by
  constructor
  rintro ⟨i,a⟩ ⟨j,b⟩
  obtain ⟨u,hu⟩ := MulAction.exists_smul_eq U i j
  let g : group U :=
    ⟨Equiv.prodCongr (u : Equiv.Perm I) (Equiv.addLeft (b-a)),u,fun _ => rfl⟩
  refine ⟨g,?_⟩
  apply Prod.ext
  · exact hu
  · change (b-a)+a=b
    exact sub_add_cancel b a

/-- Nonbinaryness is visible in the actual original quotient U. -/
theorem not_binary (hU : ¬IsPGroup 2 U) : ¬IsPGroup 2 (group U) := by
  intro h
  exact hU (h.of_surjective (topHom U) (top_surjective U))

/-- ANY returned invariant frame has the original displayed physical pairs. -/
theorem every_frame_partner {J : Type} (R : BinaryPairFrame (group U) J) (x : I × ZMod 2) :
    R.partnerMap x=(x.1,x.2+1) :=
  FullBinaryLocalFlipUniquePairs.partner_eq (localFlip_mem U) R x

end SymmetricSubgroupAsymptotics.FullBinaryDoubling
