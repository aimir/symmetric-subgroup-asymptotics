import SymmetricSubgroupAsymptotics.BinaryCheckedTransport
import SymmetricSubgroupAsymptotics.BinaryConjugacyTransport
import SymmetricSubgroupAsymptotics.BinaryExceptional16T1086
import SymmetricSubgroupAsymptotics.GeneratedPairBindings.PilotAcceptance16T1086

/-! The sole shared width-sixteen transport residual is the exact axis
of the original checked 16T1086 carrier. Only its four-element axis is
compared; no original-normal or source-row enumeration is introduced. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.BinaryNormalTransport16T1086
open BinaryPairBinding16T1086
local instance normalTransportSourceTopGroup : Group SourceTop := BinaryTopSource056.group
def chart : CheckedPermutationCarrier 16 16 :=
  CheckedPermutationCarrier.ofCertificates BinaryChart16T1086.alphaCertificate
    BinaryChart16T1086.betaCertificate
    (Subgroup.closure (Set.range BinaryChart16T1086.quotientGenerators))
    (Subgroup.closure (Set.range BinaryChart16T1086.axisGenerators))
    (Subgroup.closure (Set.range BinaryChart16T1086.coverKernelGenerators))
    BinaryChart16T1086.alpha_range BinaryChart16T1086.beta_range
    BinaryChart16T1086.alpha_kernel BinaryChart16T1086.beta_kernel

theorem source_eq : chart.source=Original := by
  change Subgroup.closure (Set.range BinaryChart16T1086.alphaGenerators)=_
  have he : BinaryChart16T1086.alphaGenerators=BinaryActionData16.node1086Generators := by
    funext j
    apply Equiv.ext
    intro x
    revert x j
    decide +kernel
  rw [he]

/-- This change of subgroup type fixes every original physical permutation. -/
def originalSourceEquiv : Original ≃* chart.source :=
  (MulEquiv.subgroupCongr source_eq).symm

@[simp] theorem originalSourceEquiv_coe (x : Original) :
    (originalSourceEquiv x : Equiv.Perm (Fin 16))=x := rfl

@[simp] theorem originalSourceEquiv_symm_coe (x : chart.source) :
    (originalSourceEquiv.symm x : Equiv.Perm (Fin 16))=x := rfl

def axis : Subrepresentation physicalFrame.coordinateTopAction :=
  physicalFrame.sharedSubrepresentation BinaryKernelAxes097.action topEquiv action_eq
    (BinaryKernelAxes097.states 2)
abbrev originalNormal := physicalFrame.coordinateSubgroup axis.toSubmodule

private def originalAxisGenerator (j : Fin 2) : Original :=
  ⟨BinaryChart16T1086.axisGenerators j,by
    rw [← source_eq]
    have h : BinaryChart16T1086.axisGenerators j∈chart.axis :=
      Subgroup.subset_closure ⟨j,rfl⟩
    rw [← chart.alpha_kernel] at h
    obtain ⟨x,_,he⟩ := h
    have hx : (x : Equiv.Perm (Fin 16))∈chart.source := x.property
    exact he ▸ hx⟩
private def axisBits (j : Fin 2) (i : Fin 8) : ZMod 2 :=
  if Nat.testBit (if j.val=0 then 240 else 15) i.val then 1 else 0
private theorem axisBits_mem : ∀ j,axisBits j∈(BinaryKernelAxes097.charts 2).2.space := by
  decide +kernel
private theorem axis_action : ∀ j (p : Fin 8 × ZMod 2),
    physicalFrame.frame.symm ((originalAxisGenerator j : Equiv.Perm (Fin 16))
      (physicalFrame.frame p))=(p.1,p.2+axisBits j p.1) := by
  change ∀ (j : Fin 2) (p : Fin 8 × ZMod 2),
    frame.symm (BinaryChart16T1086.axisGenerators j (frame p))=
      (p.1,p.2+axisBits j p.1)
  decide +kernel

private theorem axis_le_original : chart.axis≤originalNormal.map Original.subtype := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j,rfl⟩
  refine ⟨originalAxisGenerator j,?_,rfl⟩
  apply physicalFrame.mem_coordinateSubgroup_of_action axis.toSubmodule
    (originalAxisGenerator j) (axisBits j) ?_ (axis_action j)
  change axisBits j∈(BinaryKernelAxes097.states 2).toSubmodule
  rw [BinaryKernelAxes097.states_space]
  exact axisBits_mem j

private theorem original_card : Nat.card originalNormal=4 := by
  have hk : axis.toSubmodule≤physicalFrame.kernelSpace := by
    rw [BinaryPairBinding16T1086.kernel_space]
    exact BinaryKernelAxes097.registry.le_kernel 2
  rw [physicalFrame.coordinateSubgroup_card axis.toSubmodule hk]
  change Nat.card (BinaryKernelAxes097.states 2).toSubmodule=4
  rw [BinaryKernelAxes097.states_space,(BinaryKernelAxes097.charts 2).2.card]
  decide +kernel

/-- The shared exceptional normal is exactly the literal chart axis. -/
theorem axis_eq : chart.axis=originalNormal.map Original.subtype := by
  have hc : Nat.card chart.axis=4 :=
    BinaryChart16T1086.axisCertificate.card_closure (by decide +kernel)
  have hm : Nat.card (originalNormal.map Original.subtype)=4 := by
    rw [← Nat.card_congr (originalNormal.equivMapOfInjective Original.subtype
      Subtype.val_injective).toEquiv,original_card]
  apply Subgroup.eq_of_le_of_card_ge axis_le_original
  rw [hc,hm]

theorem alpha_kernel_original :
    chart.alpha.ker.map chart.source.subtype=originalNormal.map Original.subtype :=
  chart.alpha_kernel.trans axis_eq

/-- The original quotient map, with no abstract replacement of its source. -/
def originalAlpha : Original →* chart.quotient :=
  chart.alpha.comp originalSourceEquiv.toMonoidHom

theorem originalAlpha_surjective : Function.Surjective originalAlpha :=
  chart.alpha_surjective.comp originalSourceEquiv.surjective

/-- Equality of the marked kernels inside the actual original action. -/
theorem originalAlpha_kernel : originalAlpha.ker=originalNormal := by
  ext x
  constructor
  · intro hx
    have ha : (x : Equiv.Perm (Fin 16))∈originalNormal.map Original.subtype := by
      rw [← alpha_kernel_original]
      exact ⟨originalSourceEquiv x,hx,rfl⟩
    obtain ⟨y,hy,he⟩ := ha
    exact (Subtype.ext he : y=x) ▸ hy
  · intro hx
    have ha : (x : Equiv.Perm (Fin 16))∈chart.alpha.ker.map chart.source.subtype := by
      rw [alpha_kernel_original]
      exact ⟨x,hx,rfl⟩
    obtain ⟨y,hy,he⟩ := ha
    have he' : y=originalSourceEquiv x := Subtype.ext he
    have hy' : originalSourceEquiv x∈chart.alpha.ker := he' ▸ hy
    change originalSourceEquiv x∈chart.alpha.ker
    exact hy'

/-- Complete original-normal coverage retains the checked transport
alternative with the same literal source and original axis. -/
theorem pair_or_transport (N : Subgroup Original) [N.Normal] :
    (∃ C : BinaryPairLocalCertificate generators physicalFrame.top N,C.width=16) ∨
      (chart.source=Original ∧ chart.axis=N.map Original.subtype) := by
  rcases BinaryPairAcceptance16T1086.accepted_or_exceptional N with h|⟨i,hi,rfl⟩
  · exact Or.inl h
  · change i=2 at hi
    subst i
    exact Or.inr ⟨source_eq,axis_eq⟩

/-- Reconstruction keeps the complete arbitrary original exterior. -/
theorem reconstruct_original_normal {E : Type*} [Group E]
    (H : Subgroup (chart.source×E))
    (haxis : ∀ x : chart.source,
      (x : Equiv.Perm (Fin 16))∈originalNormal.map Original.subtype → (x,1)∈H) :
    ((chart.transport H).map chart.carrierMap).comap chart.sourceMap=H :=
  chart.transport_reconstruct H (fun x hx => haxis x (axis_eq ▸ hx))

section OriginalExterior
variable {E : Type*} [Group E]

def originalSourceMap : Original × E →* chart.quotient × E :=
  originalAlpha.prodMap (MonoidHom.id E)

/-- Retain the full literal proper carrier, not its displayed block product. -/
def transportOriginal (H : Subgroup (Original × E)) : Subgroup (chart.carrier × E) :=
  (H.map originalSourceMap).comap chart.carrierMap

private theorem transport_through_sourceEquiv {w q : ℕ}
    (C : CheckedPermutationCarrier w q) {S : Type*} [Group S]
    (e : S ≃* C.source) (H : Subgroup (S × E)) :
    (H.map ((C.alpha.comp e.toMonoidHom).prodMap (MonoidHom.id E))).comap C.carrierMap =
      C.transport (H.map (e.prodCongr (MulEquiv.refl E)).toMonoidHom) := by
  have hm : (C.alpha.comp e.toMonoidHom).prodMap (MonoidHom.id E) =
      C.sourceMap.comp (e.prodCongr (MulEquiv.refl E)).toMonoidHom := by
    apply MonoidHom.ext
    rintro ⟨x,z⟩
    rfl
  rw [CheckedPermutationCarrier.transport,Subgroup.map_map]
  exact congrArg (fun f : S × E →* C.quotient × E =>
    (H.map f).comap C.carrierMap) hm

/-- The original-domain endpoint uses the very same two literal chart maps. -/
theorem transportOriginal_eq_chart (H : Subgroup (Original × E)) :
    transportOriginal H=chart.transport
      (H.map (originalSourceEquiv.prodCongr (MulEquiv.refl E)).toMonoidHom) :=
  transport_through_sourceEquiv chart originalSourceEquiv H

private theorem originalSourceMap_kernel_le (H : Subgroup (Original × E))
    (haxis : ∀ x : Original, x∈originalNormal → (x,1)∈H) :
    (originalSourceMap (E := E)).ker≤H := by
  rintro ⟨x,e⟩ hx
  have he : e=1 := congrArg Prod.snd hx
  have ha : originalAlpha x=1 := congrArg Prod.fst hx
  have hk : x∈originalAlpha.ker := ha
  rw [originalAlpha_kernel] at hk
  rw [he]
  exact haxis x hk

/-- Reconstruction now has the actual original subgroup as its domain. -/
theorem transportOriginal_reconstruct (H : Subgroup (Original × E))
    (haxis : ∀ x : Original, x∈originalNormal → (x,1)∈H) :
    ((transportOriginal H).map chart.carrierMap).comap originalSourceMap=H := by
  rw [transportOriginal,
    Subgroup.map_comap_eq_self_of_surjective chart.carrierMap_surjective,
    Subgroup.comap_map_eq_self (originalSourceMap_kernel_le H haxis)]

theorem transportOriginal_exterior (H : Subgroup (Original × E)) :
    (transportOriginal H).map (MonoidHom.snd chart.carrier E)=
      H.map (MonoidHom.snd Original E) := by
  apply le_antisymm
  · rintro e ⟨⟨x,e'⟩,hx,rfl⟩
    obtain ⟨⟨y,f⟩,hy,he⟩ := hx
    exact ⟨(y,f),hy,congrArg Prod.snd he⟩
  · rintro e ⟨⟨x,e'⟩,hx,rfl⟩
    obtain ⟨y,hy⟩ := chart.beta_surjective (originalAlpha x)
    exact ⟨(y,e'),⟨(x,e'),hx,Prod.ext hy.symm rfl⟩,rfl⟩

theorem transportOriginal_full_carrier (H : Subgroup (Original × E))
    (hfull : ∀ x : Original, ∃ e : E, (x,e)∈H) :
    ∀ y : chart.carrier, ∃ e : E, (y,e)∈transportOriginal H := by
  intro y
  obtain ⟨x,hx⟩ := originalAlpha_surjective (chart.beta y)
  obtain ⟨e,he⟩ := hfull x
  exact ⟨e,⟨(x,e),he,Prod.ext hx rfl⟩⟩

end OriginalExterior

section MarkedConjugacy
variable {U : Subgroup (Equiv.Perm (Fin 16))}
  (g : Equiv.Perm (Fin 16)) (hg : MulAut.conj g • U=Original)

/-- The source marking is exactly the same ambient permutation conjugacy. -/
def conjugateSourceEquiv : U ≃* chart.source :=
  (actionConjugacyEquiv g hg).trans originalSourceEquiv

@[simp] theorem conjugateSourceEquiv_coe (x : U) :
    (conjugateSourceEquiv g hg x : Equiv.Perm (Fin 16))=g*x*g⁻¹ := rfl

/-- The original axis is moved by that same permutation, never independently. -/
theorem axis_eq_of_conjugacy (N : Subgroup U)
    (hN : actionConjugacyNormal g hg N=originalNormal) :
    chart.axis=MulAut.conj g • (N.map U.subtype) := by
  rw [axis_eq,← hN]
  exact actionConjugacyNormal_ambient g hg N

variable {E : Type*} [Group E]

def transportConjugate (H : Subgroup (U × E)) : Subgroup (chart.carrier × E) :=
  transportOriginal (H.map
    ((actionConjugacyEquiv g hg).prodCongr (MulEquiv.refl E)).toMonoidHom)

@[simp] theorem conjugateSourceMap_apply (x : U) (e : E) :
    (originalSourceMap.comp
      ((actionConjugacyEquiv g hg).prodCongr (MulEquiv.refl E)).toMonoidHom) (x,e)=
      (chart.alpha (conjugateSourceEquiv g hg x),e) := rfl

theorem transportConjugate_exterior (H : Subgroup (U × E)) :
    (transportConjugate g hg H).map (MonoidHom.snd chart.carrier E)=
      H.map (MonoidHom.snd U E) := by
  rw [transportConjugate,transportOriginal_exterior,Subgroup.map_map]
  rfl

/-- The full exterior is untouched, and reconstruction uses the marked
ambient conjugacy and the actual original quotient map. -/
theorem transportConjugate_reconstruct (N : Subgroup U)
    (hN : actionConjugacyNormal g hg N=originalNormal)
    (H : Subgroup (U × E)) (haxis : ∀ x : U, x∈N → (x,1)∈H) :
    ((transportConjugate g hg H).map chart.carrierMap).comap
      (originalSourceMap.comp
        ((actionConjugacyEquiv g hg).prodCongr (MulEquiv.refl E)).toMonoidHom)=H := by
  have ha : ∀ x : Original, x∈originalNormal →
      (x,1)∈H.map
        ((actionConjugacyEquiv g hg).prodCongr (MulEquiv.refl E)).toMonoidHom := by
    intro x hx
    rw [← hN] at hx
    obtain ⟨y,hy,rfl⟩ := hx
    exact ⟨(y,1),haxis y hy,rfl⟩
  rw [transportConjugate,← Subgroup.comap_comap,transportOriginal_reconstruct _ ha]
  exact Subgroup.comap_map_eq_self_of_injective
    ((actionConjugacyEquiv g hg).prodCongr (MulEquiv.refl E)).injective H

end MarkedConjugacy

end SymmetricSubgroupAsymptotics.BinaryNormalTransport16T1086
