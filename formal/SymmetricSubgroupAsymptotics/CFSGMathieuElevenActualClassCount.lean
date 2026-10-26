import SymmetricSubgroupAsymptotics.External.CFSG.Certificates.Mathieu11.Certificates.SplitClasses
import SymmetricSubgroupAsymptotics.CFSGMathieuElevenActualEquivalence

/-! The original ten conjugacy orbits are proved to cover the SAME
original a/b subgroup. Their class map is therefore surjective. The
pinned presentation inherits this bound only through the separately
proved actual equivalence and its existing simplicity hypothesis. No
class count, outer order, or model identification is supplied as input. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuElevenActualClassCount
open CFSG.Certificates.Mathieu11
open M11Certificates.ConjugacyClasses

theorem original_representative_cover (g : M11) :
    ∃ i : Fin 10, IsConj g (representativeM11 i) := by
  have hg : g ∈ ⋃ i : Fin 10,classOrbit i := by
    rw [classOrbit_iUnion_eq_univ]
    trivial
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hg
  exact ⟨i,by simpa only [classOrbit] using ConjAct.mem_orbit_conjAct.mp hi⟩

theorem original_class_card_le_ten : Nat.card (ConjClasses M11) ≤ 10 := by
  let f : Fin 10 → ConjClasses M11 := fun i => ConjClasses.mk (representativeM11 i)
  have hf : Function.Surjective f := by
    intro c
    obtain ⟨g,rfl⟩ := ConjClasses.mk_surjective c
    obtain ⟨i,hi⟩ := original_representative_cover g
    exact ⟨i,(ConjClasses.mk_eq_mk_iff_isConj.mpr hi).symm⟩
  exact (Nat.card_le_card_of_surjective f hf).trans_eq (Nat.card_fin 10)

theorem class_card_le_ten [IsSimpleGroup CFSG.Models.Presentations.M11.Model] :
    Nat.card (ConjClasses CFSG.Models.Presentations.M11.Model) ≤ 10 := by
  letI : Finite M11 := Finite.of_injective
    (fun g : M11 => (g : Perm11)) Subtype.val_injective
  letI : Finite (ConjClasses M11) :=
    Finite.of_surjective (ConjClasses.mk : M11 → ConjClasses M11) ConjClasses.mk_surjective
  let e := CFSGMathieuElevenActualEquivalence.actualEquivalence
  exact (Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
    (ConjClasses.map_surjective e.symm.surjective)).trans original_class_card_le_ten

end SymmetricSubgroupAsymptotics.CFSGMathieuElevenActualClassCount
