import SymmetricSubgroupAsymptotics.ActualFullWreathFamily
import SymmetricSubgroupAsymptotics.FiniteAbelianExtensionWholeLayerCount

/-! The literal preimage of a full-component quotient image is itself
full-component. A chosen local coordinate can be lifted to a prescribed
element, so quotient fullness is not mistaken for raw local fullness. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.ActualFullWreathPreimage
open PermutationalWreathProduct ActualFullWreathFamily

variable {R R' Q I : Type} [Group R] [Group R'] [Group Q] [MulAction Q I]
    (phi : R →* R') (hphi : Function.Surjective phi)

include hphi in
theorem mapBase_surjective :
    Function.Surjective (mapBase (Q := Q) (I := I) phi) := by
  intro w
  choose f hf using hphi
  refine ⟨⟨fun i => f (w.left i),w.right⟩,?_⟩
  apply PermutationalWreathProduct.ext
  · funext i
    exact hf (w.left i)
  · rfl

include hphi in
theorem exists_lift_prescribed (w : PermutationalWreathProduct R' Q I)
    (i : I) (r : R) (hr : phi r=w.left i) :
    ∃ v : PermutationalWreathProduct R Q I,mapBase phi v=w ∧ v.left i=r := by
  classical
  choose f hf using hphi
  let v : PermutationalWreathProduct R Q I :=
    ⟨fun j => if j=i then r else f (w.left j),w.right⟩
  refine ⟨v,?_,?_⟩
  · apply PermutationalWreathProduct.ext
    · funext j
      change phi (if j=i then r else f (w.left j))=w.left j
      split_ifs with hj
      · subst j
        exact hr
      · exact hf (w.left j)
    · rfl
  · simp only [v,ite_true]

def preimage (H : Family R' Q I) : Family R Q I := by
  refine ⟨H.val.comap (mapBase phi),?_,?_⟩
  · apply top_unique
    intro q _
    obtain ⟨h,hh⟩ := ActualFullWreathFamily.top_surjective H q
    obtain ⟨w,hw⟩ := mapBase_surjective phi hphi h.val
    refine ⟨w,?_,?_⟩
    · change mapBase phi w∈H.val
      rw [hw]
      exact h.property
    · exact (congrArg right hw).trans hh
  · intro i r
    obtain ⟨h,hfix,hcoord⟩ := H.property.2 i (phi r)
    obtain ⟨w,hw,hwi⟩ := exists_lift_prescribed phi hphi h.val i r hcoord.symm
    have hwmem : w∈H.val.comap (mapBase phi) := by
      change mapBase phi w∈H.val
      rw [hw]
      exact h.property
    refine ⟨⟨w,hwmem⟩,?_,hwi⟩
    change w.right • i=i
    have hright : w.right=h.val.right := congrArg right hw
    rw [hright]
    exact hfix

theorem preimage_subgroup (H : Family R' Q I) :
    (preimage phi hphi H).val=H.val.comap (mapBase phi) := rfl

def projection (H : Family R' Q I) : (preimage phi hphi H).val →* H.val :=
  (mapBase phi).subgroupComap H.val

theorem projection_surjective (H : Family R' Q I) :
    Function.Surjective (projection phi hphi H) :=
  (mapBase phi).subgroupComap_surjective_of_surjective H.val (mapBase_surjective phi hphi)

abbrev Fibre (H : Family R' Q I) :=
  {L : Family R Q I // ActualFullWreathFamily.localImage phi hphi L=H}

theorem fibre_subgroup_le (H : Family R' Q I) (L : Fibre phi hphi H) :
    L.val.val≤(preimage phi hphi H).val := by
  intro g hg
  change mapBase phi g∈H.val
  have himage : L.val.val.map (mapBase phi)=H.val := congrArg Subtype.val L.property
  rw [←himage]
  exact ⟨g,hg,rfl⟩

/-- The entire fixed-image fibre injects into the complete preimage
extension family; no lift or invariant-intersection choices are omitted. -/
def fibreCode (H : Family R' Q I) (L : Fibre phi hphi H) :
    FiniteAbelianExtensionWholeLayerCount.FullImage (projection phi hphi H) := by
  refine ⟨L.val.val.subgroupOf (preimage phi hphi H).val,?_⟩
  apply top_unique
  intro h _
  have himage : L.val.val.map (mapBase phi)=H.val := congrArg Subtype.val L.property
  have hm : h.val∈L.val.val.map (mapBase phi) := by rw [himage]; exact h.property
  obtain ⟨g,hg,he⟩ := hm
  refine ⟨⟨g,fibre_subgroup_le phi hphi H L hg⟩,hg,?_⟩
  exact Subtype.ext he

theorem fibreCode_injective (H : Family R' Q I) :
    Function.Injective (fibreCode phi hphi H) := by
  intro L M h
  apply Subtype.ext
  apply Subtype.ext
  apply le_antisymm
  · intro g hg
    have hm : (⟨g,fibre_subgroup_le phi hphi H L hg⟩ : (preimage phi hphi H).val)∈
        (fibreCode phi hphi H L).val := hg
    rw [h] at hm
    exact hm
  · intro g hg
    have hm : (⟨g,fibre_subgroup_le phi hphi H M hg⟩ : (preimage phi hphi H).val)∈
        (fibreCode phi hphi H M).val := hg
    rw [←h] at hm
    exact hm

end SymmetricSubgroupAsymptotics.ActualFullWreathPreimage
