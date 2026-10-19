import SymmetricSubgroupAsymptotics.MarkedC4QuotientProfiles

/-! Actual image-layer cardinality for the simultaneous column filtration.
The diagonal quotient is factored through an ACTUAL surjection; no extension
of characters from subgroups is invoked. This is valid for original finite
nonabelian sources and their commutative target images. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualLayerImageCard

theorem image_layer_card_le
    {A B Q : Type} [Group A] [Finite A] [CommGroup B] [Finite B] [Group Q] [Finite Q]
    (π : A →* B) (ρ : A →* Q) (L U : Subgroup A) (hLU : L≤U)
    (hker : ∀ x ∈ U,ρ x=1 → x ∈ L) :
    Nat.card (U.map π) ≤ Nat.card (U.map ρ)*Nat.card (L.map π) := by
  let P : Subgroup B := L.map π
  let X : Subgroup B := U.map π
  let D : Subgroup Q := U.map ρ
  let q : B →* B ⧸ P := QuotientGroup.mk' P
  let V : Subgroup (B ⧸ P) := U.map (q.comp π)
  let r : U →* D := (ρ.comp U.subtype).codRestrict D (fun x => ⟨x.val,x.property,rfl⟩)
  let g : U →* V := ((q.comp π).comp U.subtype).codRestrict V
    (fun x => ⟨x.val,x.property,rfl⟩)
  have hr : Function.Surjective r := by
    intro d
    obtain ⟨x,hx,hxd⟩ := d.property
    exact ⟨⟨x,hx⟩,Subtype.ext hxd⟩
  have hg : Function.Surjective g := by
    intro v
    obtain ⟨x,hx,hxv⟩ := v.property
    exact ⟨⟨x,hx⟩,Subtype.ext hxv⟩
  have hk : r.ker≤g.ker := by
    intro x hx
    have hρ : ρ x.val=1 := congrArg Subtype.val (show r x=1 from hx)
    have hL := hker x.val x.property hρ
    apply MonoidHom.mem_ker.mpr
    apply Subtype.ext
    apply (QuotientGroup.eq_one_iff (N := P) (π x.val)).mpr
    exact ⟨x.val,hL,rfl⟩
  let lift : D →* V := r.liftOfSurjective hr ⟨g,hk⟩
  have hlift : Function.Surjective lift := by
    intro v
    obtain ⟨x,hx⟩ := hg v
    refine ⟨r x,?_⟩
    exact (MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ x).trans hx
  have hcap : Nat.card V≤Nat.card D := Nat.card_le_card_of_surjective lift hlift
  have hcard := card_map_mk_mul P X (Subgroup.map_mono hLU)
  have hV : X.map q=V := Subgroup.map_map U q π
  rw [hV] at hcard
  calc
    Nat.card (U.map π)=Nat.card V*Nat.card P := hcard.symm
    _ ≤ Nat.card D*Nat.card P := Nat.mul_le_mul_right _ hcap

end SymmetricSubgroupAsymptotics.MarkedC4.ActualLayerImageCard
