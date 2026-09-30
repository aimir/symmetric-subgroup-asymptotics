import SymmetricSubgroupAsymptotics.BinaryPairSharedBinding
import SymmetricSubgroupAsymptotics.BinaryTopNormalRegistry

/-! Independently complete shared axis and top registries install actual
physical local certificates. The exceptional branch retains the literal
original normal, which is uniquely recovered when its top image is trivial. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X H I J ι : Type} [Group H] {w : ℕ}
    {U : Subgroup (Equiv.Perm X)} (F : BinaryPairFrame U (Fin w))
    (ρ : Representation (ZMod 2) H (Fin w → ZMod 2))
    (e : H ≃* F.top.range) (he : ∀ g v, ρ g v=F.coordinateTopAction (e g) v)
    (K : Subrepresentation ρ) (hK : K.toSubmodule=F.kernelSpace)
    (axes cuts fixed : I → Subrepresentation ρ)
    (hcuts : ∀ i, BinaryCoordinateCutData ρ K (axes i) (cuts i) (fixed i))

def sharedCost (i : I) : ℕ :=
  2*(Module.finrank (ZMod 2) (cuts i).toSubmodule-Module.finrank (ZMod 2) (axes i).toSubmodule)+
  4*(Module.finrank (ZMod 2) (fixed i).toSubmodule-Module.finrank (ZMod 2) (cuts i).toSubmodule)

include e he hK hcuts in
/-- The whole joint-state conclusion follows from independent finite
registries and local numerical cells. No original-normal count or desired
acceptance assertion is a premise. The physical width is `Nat.card X`. -/
theorem shared_complete_acceptance
    (haxes : ∀ W : Subrepresentation ρ, W.toSubmodule≤K.toSubmodule → ∃ i, axes i=W)
    (tops : J → BinaryTopKernelData H)
    (htops : ∀ T : Subgroup H, T.Normal → ∃ j, (tops j).kernel=T)
    (exceptional : I → Prop)
    (hcells : ∀ i j, (tops j).degree+sharedCost ρ axes cuts fixed i<Nat.card X ∨
      exceptional i ∧ (tops j).kernel=⊥)
    (generators : ι → U) (N : Subgroup U) [N.Normal] :
    (∃ C : BinaryPairLocalCertificate generators F.top N, C.width=Nat.card X) ∨
      ∃ i, exceptional i ∧ N=F.coordinateSubgroup (axes i).toSubmodule := by
  let W := F.sharedOriginalAxis ρ e he N
  have hW : W.toSubmodule≤K.toSubmodule := by
    rw [hK]
    exact F.ambientAxis_le_kernelSpace N
  obtain ⟨i,hi⟩ := haxes W hW
  let T := (N.map F.top.rangeRestrict).comap e.toMonoidHom
  haveI : (N.map F.top.rangeRestrict).Normal :=
    Subgroup.Normal.map inferInstance _ F.top.rangeRestrict_surjective
  obtain ⟨j,hj⟩ := htops T inferInstance
  have hcover : ((tops j).transport e).kernel=N.map F.top.rangeRestrict := by
    ext t
    change e.symm t∈(tops j).kernel ↔ t∈N.map F.top.rangeRestrict
    rw [hj]
    change e (e.symm t)∈N.map F.top.rangeRestrict ↔ _
    rw [e.apply_symm_apply]
  have haxis : F.top.ker⊓N=F.coordinateSubgroup (axes i).toSubmodule :=
    F.shared_axis_eq ρ e he N (axes i) hi.symm
  rcases hcells i j with hgap|⟨hbad,hbot⟩
  · let C := F.sharedKernelCut
      (F.sharedSubrepresentation ρ e he (axes i))
      (F.sharedSubrepresentation ρ e he (cuts i))
      (F.sharedSubrepresentation ρ e he (fixed i))
      (F.shared_cut ρ e he K (axes i) (cuts i) (fixed i) hK (hcuts i)) generators
    let E : BinaryTopQuotientCover F.top (N.map F.top.rangeRestrict) :=
      ⟨(tops j).degree,((tops j).transport e).hom,hcover⟩
    have hg : E.degree+2*C.cutDimension+4*C.fixedDimension<Nat.card X := by
      simpa only [E,C,sharedKernelCut,sharedSubrepresentation,sharedCost,Nat.add_assoc] using hgap
    exact Or.inl ⟨C.install E N haxis rfl (Nat.card X) hg,rfl⟩
  · have hT : N.map F.top.rangeRestrict=⊥ := by
      rw [← hcover,BinaryTopKernelData.transport_kernel,hbot,Subgroup.map_bot]
    have hN : F.top.ker⊓N=N := by
      simpa only [MonoidHom.ker_rangeRestrict] using
        binary_normal_eq_intersection_of_top_trivial F.top.rangeRestrict N hT
    exact Or.inr ⟨i,hbad,hN.symm.trans haxis⟩

include e he hK hcuts in
/-- The same complete-registry theorem while retaining any property of the
selected top-cover degree.  This is the interface needed when a later direct
recurrence must remember parity rather than merely the existence of a local
certificate. -/
theorem shared_complete_acceptance_with_cover_property
    (haxes : ∀ W : Subrepresentation ρ, W.toSubmodule≤K.toSubmodule → ∃ i, axes i=W)
    (tops : J → BinaryTopKernelData H)
    (htops : ∀ T : Subgroup H, T.Normal → ∃ j, (tops j).kernel=T)
    (P : ℕ → Prop) (hP : ∀ j, P (tops j).degree)
    (exceptional : I → Prop)
    (hcells : ∀ i j, (tops j).degree+sharedCost ρ axes cuts fixed i<Nat.card X ∨
      exceptional i ∧ (tops j).kernel=⊥)
    (generators : ι → U) (N : Subgroup U) [N.Normal] :
    (∃ C : BinaryPairLocalCertificate generators F.top N,
      C.width=Nat.card X ∧ P C.coverDegree) ∨
      ∃ i, exceptional i ∧ N=F.coordinateSubgroup (axes i).toSubmodule := by
  let W := F.sharedOriginalAxis ρ e he N
  have hW : W.toSubmodule≤K.toSubmodule := by
    rw [hK]
    exact F.ambientAxis_le_kernelSpace N
  obtain ⟨i,hi⟩ := haxes W hW
  let T := (N.map F.top.rangeRestrict).comap e.toMonoidHom
  haveI : (N.map F.top.rangeRestrict).Normal :=
    Subgroup.Normal.map inferInstance _ F.top.rangeRestrict_surjective
  obtain ⟨j,hj⟩ := htops T inferInstance
  have hcover : ((tops j).transport e).kernel=N.map F.top.rangeRestrict := by
    ext t
    change e.symm t∈(tops j).kernel ↔ t∈N.map F.top.rangeRestrict
    rw [hj]
    change e (e.symm t)∈N.map F.top.rangeRestrict ↔ _
    rw [e.apply_symm_apply]
  have haxis : F.top.ker⊓N=F.coordinateSubgroup (axes i).toSubmodule :=
    F.shared_axis_eq ρ e he N (axes i) hi.symm
  rcases hcells i j with hgap|⟨hbad,hbot⟩
  · let C := F.sharedKernelCut
      (F.sharedSubrepresentation ρ e he (axes i))
      (F.sharedSubrepresentation ρ e he (cuts i))
      (F.sharedSubrepresentation ρ e he (fixed i))
      (F.shared_cut ρ e he K (axes i) (cuts i) (fixed i) hK (hcuts i)) generators
    let E : BinaryTopQuotientCover F.top (N.map F.top.rangeRestrict) :=
      ⟨(tops j).degree,((tops j).transport e).hom,hcover⟩
    have hg : E.degree+2*C.cutDimension+4*C.fixedDimension<Nat.card X := by
      simpa only [E,C,sharedKernelCut,sharedSubrepresentation,sharedCost,Nat.add_assoc] using hgap
    let L := C.install E N haxis rfl (Nat.card X) hg
    exact Or.inl ⟨L,rfl,hP j⟩
  · have hT : N.map F.top.rangeRestrict=⊥ := by
      rw [← hcover,BinaryTopKernelData.transport_kernel,hbot,Subgroup.map_bot]
    have hN : F.top.ker⊓N=N := by
      simpa only [MonoidHom.ker_rangeRestrict] using
        binary_normal_eq_intersection_of_top_trivial F.top.rangeRestrict N hT
    exact Or.inr ⟨i,hbad,hN.symm.trans haxis⟩

end SymmetricSubgroupAsymptotics.BinaryPairFrame
