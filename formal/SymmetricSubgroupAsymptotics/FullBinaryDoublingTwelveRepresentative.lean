import SymmetricSubgroupAsymptotics.FullBinaryDoubling
import SymmetricSubgroupAsymptotics.Non2PreE7PairPayload
import SymmetricSubgroupAsymptotics.BinaryConjugacyTransport

/-! A literal full binary doubling determines an actual24point pair-action
representative, with the SAME point and group equivalences retained.
This is only a classification device; no width24 source is reused as a
width12 source. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise
namespace SymmetricSubgroupAsymptotics.FullBinaryDoublingTwelveRepresentative
open Non2UnipotentPrefixFiniteMenu
variable (U : Subgroup (Equiv.Perm (Fin 12)))

abbrev points : Fin 12 × ZMod 2 ≃ Fin 24 :=
  (Equiv.prodCongr (Equiv.refl (Fin 12)) (ZMod.finEquiv 2).symm.toEquiv).trans finProdFinEquiv
abbrev original := relabelSubgroup points (FullBinaryDoubling.group U)
abbrev originalEquiv : FullBinaryDoubling.group U ≃* original U :=
  BinaryPairFrame.sourceRelabelEquiv points

theorem original_action (g : FullBinaryDoubling.group U) (x : Fin 12 × ZMod 2) :
    (originalEquiv U g : Equiv.Perm (Fin 24)) (points x)=points (g.val x) := by
  change points (g.val (points.symm (points x)))=points (g.val x)
  rw [points.symm_apply_apply]

theorem original_transitive [MulAction.IsPretransitive U (Fin 12)] :
    MulAction.IsPretransitive (original U) (Fin 24) := by
  letI := FullBinaryDoubling.transitive U
  constructor
  intro x y
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (FullBinaryDoubling.group U) (points.symm x) (points.symm y)
  refine ⟨originalEquiv U g,?_⟩
  have h := original_action U g (points.symm x)
  rw [points.apply_symm_apply] at h
  change (originalEquiv U g : Equiv.Perm (Fin 24)) x=y
  rw [h]
  exact (congrArg points hg).trans (points.apply_symm_apply y)

structure Chart where
  index : PreE7PairActionClass 12
  pointEquiv : Fin 12 × ZMod 2 ≃ Fin 24
  groupEquiv : FullBinaryDoubling.group U ≃* preE7PairAction 12 index
  point_equivariant : ∀ g : FullBinaryDoubling.group U,∀ x,
    pointEquiv (g.val x)=(groupEquiv g : Equiv.Perm (Fin 24)) (pointEquiv x)

/-- Actual original point conjugacy constructs the classifier input. -/
def choose [MulAction.IsPretransitive U (Fin 12)] (hU : ¬IsPGroup 2 U) : Chart U := by
  apply Classical.choice
  have hn : ¬IsPGroup 2 (original U) := by
    intro h
    exact FullBinaryDoubling.not_binary U hU (h.of_equiv (originalEquiv U).symm)
  obtain ⟨i,c,hc⟩ := Non2TransitiveActionClass.representative_cover (original U) hn
    (original_transitive U)
  let e : Fin 12 × ZMod 2 ≃ Fin 24 := points.trans c
  let f : FullBinaryDoubling.group U ≃* i.representative :=
    (originalEquiv U).trans (actionConjugacyEquiv c hc)
  have hp : ∀ g : FullBinaryDoubling.group U,∀ x,
      e (g.val x)=(f g : Equiv.Perm (Fin 24)) (e x) := by
    intro g x
    change c (points (g.val x))=
      c ((originalEquiv U g : Equiv.Perm (Fin 24)) (c.symm (c (points x))))
    rw [c.symm_apply_apply]
    exact (congrArg c (original_action U g x)).symm
  let F : BinaryPairFrame i.representative (Fin 12) :=
    BinaryPairFrame.ofEquiv f (FullBinaryDoubling.frame U).top e (by
      intro g x
      change (e.symm ((f g : Equiv.Perm (Fin 24)) (e x))).1=
        (FullBinaryDoubling.topHom U g : Equiv.Perm (Fin 12)) x.1
      rw [←hp,e.symm_apply_apply]
      exact FullBinaryDoubling.top_spec U g x)
  have hpre : IsPreE7ActionClass 24 i := by
    intro d hd
    have hg := d.pairCount_ge_24
    change 2*d.pairCount=24 at hd
    omega
  let j : PreE7PairActionClass 12 := ⟨⟨i,hpre⟩,⟨F⟩⟩
  exact ⟨⟨j,e,f,hp⟩⟩

end SymmetricSubgroupAsymptotics.FullBinaryDoublingTwelveRepresentative
