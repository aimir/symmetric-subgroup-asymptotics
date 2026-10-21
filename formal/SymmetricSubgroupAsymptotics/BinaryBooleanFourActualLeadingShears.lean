import SymmetricSubgroupAsymptotics.BinaryPairPolynomialCoordinates
import SymmetricSubgroupAsymptotics.BinaryBooleanFourRepresentationLeadingMiddle
import SymmetricSubgroupAsymptotics.BinaryBooleanFourKernelLeadingClosure
import SymmetricSubgroupAsymptotics.BinaryFiveQuadraticPairMonomialWidth

/-! A head-five original translation submodule supplies five quadratic
leading shear vectors and all smaller supports in its actual coordinates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics

open BinaryBooleanFourPolynomialCoordinates BinaryElementaryPairMonomialWidth
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

private theorem quadratic_masks_are_missing : ∀ a ∈ quadraticMasks,
    ∃ j : Fin 6, BinaryFiveQuadraticPairMonomialWidth.missing j = a := by decide

variable {G : Type} [Group G] [MulAction G (Fin 16)]

set_option maxHeartbeats 2000000 in
theorem boolean_four_actual_translation_submodule_leading_shears
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) G (Fin 16)))
    (e : Equiv.Perm (Fin 16))
    (htranslations : ∀ i : Fin 4, ∃ g : G,
      ∀ j, g⁻¹ • e.symm j = e.symm (flipIndex i j))
    (hhead : 5 ≤ Module.finrank (ZMod 2)
      (W.toRepresentation.IntertwiningMap
        (Representation.trivial (ZMod 2) G (ZMod 2)))) :
    ∃ j : Fin 6, ∀ b : Fin 16,
      BinaryFiveQuadraticPairMonomialWidth.Allowed j (support b) →
      ∃ a : V, FiniteRowLeadingWeight.HasLeading a b ∧
        (fun x => evaluate a (e x)) ∈ W.toSubmodule := by
  let P : V ≃ₗ[ZMod 2] V :=
    (BinaryBooleanFourPolynomialCoordinates.reindex e).trans coordinates
  let C : W.toSubmodule →ₗ[ZMod 2] V := P.toLinearMap.comp W.toSubmodule.subtype
  have hC : Function.Injective C := by
    intro a b hab
    apply Subtype.ext
    apply P.injective
    change P a.val = P b.val at hab
    exact hab
  have hdiff (i : Fin 4) : ∃ g : G, ∀ v : W.toSubmodule,
      C (W.toRepresentation g v - v) = derivative i (C v) := by
    obtain ⟨g, hg⟩ := htranslations i
    refine ⟨g, ?_⟩
    intro v
    change evaluate (fun j => (v.val (g⁻¹ • e.symm j) - v.val (e.symm j))) =
      derivative i (evaluate (fun j => v.val (e.symm j)))
    rw [derivative_evaluate]
    congr 1
    funext j
    rw [hg]
    rfl
  obtain ⟨S, label, hspan, hleading, hinj⟩ :=
    boolean_four_representation_generators_quadratic_leading
      W.toRepresentation C hC hdiff hhead
  let Q := S.image label
  have hQ : ∀ a ∈ Q, (support a).card = 2 := by
    intro a ha
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ha
    exact (hleading v hv).2
  have hcard : 5 ≤ Q.card := by
    have hScard : 5 ≤ S.card := by
      obtain ⟨v, hv⟩ := ModuleGeneratedBy.of_finset_card_le S hspan S.card le_rfl
      exact hhead.trans (representationHead_finrank_le_generators W.toRepresentation v hv)
    rwa [Finset.card_image_of_injOn hinj]
  let K : Submodule (ZMod 2) V := W.toSubmodule.map P.toLinearMap
  have hactual : ∀ b ∈ Q, ∃ a ∈ K, FiniteRowLeadingWeight.HasLeading a b := by
    intro b hb
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
    refine ⟨C (W.toRepresentation.asModuleEquiv v), ?_, (hleading v hv).1⟩
    exact ⟨(W.toRepresentation.asModuleEquiv v).val,
      (W.toRepresentation.asModuleEquiv v).property, rfl⟩
  have hstable : ∀ i : Fin 4, ∀ a ∈ K, derivative i a ∈ K := by
    intro i a ha
    obtain ⟨f, hf, rfl⟩ := ha
    obtain ⟨g, hg⟩ := hdiff i
    have he := hg ⟨f, hf⟩
    refine ⟨(W.toRepresentation g ⟨f, hf⟩ - ⟨f, hf⟩).val,
      (W.toRepresentation g ⟨f, hf⟩ - ⟨f, hf⟩).property, ?_⟩
    exact he
  obtain ⟨m, hm, hcover⟩ := five_quadratic_masks_cover_except_one Q hQ hcard
  obtain ⟨j, hj⟩ := quadratic_masks_are_missing m hm
  refine ⟨j, ?_⟩
  intro b hb
  have hbK : ∃ a ∈ K, FiniteRowLeadingWeight.HasLeading a b := by
    rcases hb with hb | ⟨hcardb, hne⟩
    · exact five_quadratic_leading_vectors_give_small_supports K hstable Q hQ hcard hactual b hb
    · apply hactual b
      apply hcover b ((mem_quadraticMasks_iff b).mpr hcardb)
      intro he
      apply hne
      rw [he, hj]
  obtain ⟨a, ha, hlead⟩ := hbK
  refine ⟨a, hlead, ?_⟩
  obtain ⟨f, hf, he⟩ := ha
  have heval : (fun x => evaluate a (e x)) = f := by
    rw [← he]
    change (fun x => evaluate (evaluate (fun j => f (e.symm j))) (e x)) = f
    rw [evaluate_involutive]
    funext x
    rw [Equiv.symm_apply_apply]
  rwa [heval]

end SymmetricSubgroupAsymptotics
