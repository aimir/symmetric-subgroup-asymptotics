import SymmetricSubgroupAsymptotics.CFSGGTwoImageWeylWitness
import SymmetricSubgroupAsymptotics.CFSGSimpleProjectiveDescent

/-! Even order for the original simple pinned G₂ projective model.
The comparison is only with its actual image modulo that image's centre;
no recognition or natural-representation faithfulness is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoSerreMatrices
open CFSG.Models.Chevalley

 def modelToNaturalImage (K : Type) [Field K] : Model CartanMatrix.G₂ K→*naturalActionImage K where
  toFun g := ⟨foldedImageRepresentation K g,by
    change foldedImageRepresentation K g∈(naturalImageAction K).range
    rw [←action_ranges_eq K]
    exact ⟨g,rfl⟩⟩
  map_one' := Subtype.ext (map_one (foldedImageRepresentation K))
  map_mul' g h := Subtype.ext (map_mul (foldedImageRepresentation K) g h)

 theorem modelToNaturalImage_surjective (K : Type) [Field K] :
    Function.Surjective (modelToNaturalImage K) := by
  rintro ⟨g,hg⟩
  have h : g∈(foldedImageRepresentation K).range := by
    rw [action_ranges_eq]
    exact hg
  obtain ⟨x,hx⟩ := h
  exact ⟨x,Subtype.ext hx⟩

 theorem serreTypeGTwo_even_card (K : Type) [Field K]
    [IsSimpleGroup (Projective CartanMatrix.G₂ K)] :
    Even (Nat.card (Projective CartanMatrix.G₂ K)) := by
  let q := QuotientGroup.mk' (Subgroup.center (naturalActionImage K))
  have hne : q (imageLongWeyl K)≠1 := by
    intro h
    exact imageLongWeyl_not_center K ((QuotientGroup.eq_one_iff _).mp h)
  letI : Nontrivial (naturalActionImage K⧸Subgroup.center (naturalActionImage K)) :=
    ⟨⟨q (imageLongWeyl K),1,hne⟩⟩
  let e := CFSGSimpleProjectiveDescent.projectiveEquivOfSimple
    (modelToNaturalImage K) (modelToNaturalImage_surjective K)
  change Even (Nat.card (Model CartanMatrix.G₂ K⧸Subgroup.center (Model CartanMatrix.G₂ K)))
  rw [Nat.card_congr e.toEquiv]
  exact imageProjective_even_card K

 theorem typeGTwo_even_card (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.G2 q)] : Even (Nat.card (CFSG.Models.G2 q)) :=
  serreTypeGTwo_even_card q.Field

end SymmetricSubgroupAsymptotics.CFSGGTwoSerreMatrices
