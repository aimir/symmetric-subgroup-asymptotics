import SymmetricSubgroupAsymptotics.BinaryCheckedTransport
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! A literal carrier entry acts on the original source subgroup. The source
identification fixes each physical permutation, the kernel is the specified
original normal, and every exterior coordinate and correlation is retained. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CheckedPermutationCarrier

variable {w q : ℕ} (C : CheckedPermutationCarrier w q)
    {U : Subgroup (Equiv.Perm (Fin w))} (hsource : C.source=U)

def originalSourceEquiv : U ≃* C.source :=
  (MulEquiv.subgroupCongr hsource).symm

@[simp] theorem originalSourceEquiv_coe (x : U) :
    (C.originalSourceEquiv hsource x : Equiv.Perm (Fin w))=x := rfl

/-- The actual chart quotient map, now on the original subgroup type. -/
def originalAlpha : U →* C.quotient :=
  C.alpha.comp (C.originalSourceEquiv hsource).toMonoidHom

theorem originalAlpha_surjective : Function.Surjective (C.originalAlpha hsource) :=
  C.alpha_surjective.comp (C.originalSourceEquiv hsource).surjective

/-- The equality of ambient axes identifies the exact original kernel. -/
theorem originalAlpha_kernel (N : Subgroup U)
    (haxis : C.axis=N.map U.subtype) : (C.originalAlpha hsource).ker=N := by
  ext x
  constructor
  · intro hx
    have ha : (x : Equiv.Perm (Fin w))∈N.map U.subtype := by
      rw [← haxis,← C.alpha_kernel]
      exact ⟨C.originalSourceEquiv hsource x,hx,rfl⟩
    obtain ⟨y,hy,he⟩ := ha
    exact (Subtype.ext he : y=x) ▸ hy
  · intro hx
    have ha : (x : Equiv.Perm (Fin w))∈C.alpha.ker.map C.source.subtype := by
      rw [C.alpha_kernel,haxis]
      exact ⟨x,hx,rfl⟩
    obtain ⟨y,hy,he⟩ := ha
    have he' : y=C.originalSourceEquiv hsource x := Subtype.ext he
    change C.originalSourceEquiv hsource x∈C.alpha.ker
    exact he' ▸ hy

/-- The original normal quotient is identified through the checked alpha
map, with its actual representatives retained. -/
def originalQuotientEquiv (N : Subgroup U) [N.Normal]
    (haxis : C.axis=N.map U.subtype) : U ⧸ N ≃* C.quotient :=
  (QuotientGroup.quotientMulEquivOfEq
    (C.originalAlpha_kernel hsource N haxis).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (C.originalAlpha hsource)
        (C.originalAlpha_surjective hsource))

@[simp] theorem originalQuotientEquiv_mk (N : Subgroup U) [N.Normal]
    (haxis : C.axis=N.map U.subtype) (x : U) :
    C.originalQuotientEquiv hsource N haxis (QuotientGroup.mk x)=
      C.alpha (C.originalSourceEquiv hsource x) := rfl

section Exterior
variable {E : Type*} [Group E]

def originalSourceMap : U × E →* C.quotient × E :=
  (C.originalAlpha hsource).prodMap (MonoidHom.id E)

@[simp] theorem originalSourceMap_apply (x : U) (e : E) :
    C.originalSourceMap hsource (x,e)=
      (C.alpha (C.originalSourceEquiv hsource x),e) := rfl

def transportOriginal (H : Subgroup (U × E)) : Subgroup (C.carrier × E) :=
  (H.map (C.originalSourceMap hsource)).comap C.carrierMap

private theorem originalSourceMap_kernel_le (N : Subgroup U)
    (haxis : C.axis=N.map U.subtype) (H : Subgroup (U × E))
    (hN : ∀ x : U, x∈N → (x,1)∈H) :
    (C.originalSourceMap (E := E) hsource).ker≤H := by
  rintro ⟨x,e⟩ hx
  have he : e=1 := congrArg Prod.snd hx
  have ha : C.originalAlpha hsource x=1 := congrArg Prod.fst hx
  have hk : x∈(C.originalAlpha hsource).ker := ha
  rw [C.originalAlpha_kernel hsource N haxis] at hk
  rw [he]
  exact hN x hk

/-- Both original quotient maps recover the whole original subgroup. -/
theorem transportOriginal_reconstruct (N : Subgroup U)
    (haxis : C.axis=N.map U.subtype) (H : Subgroup (U × E))
    (hN : ∀ x : U, x∈N → (x,1)∈H) :
    ((C.transportOriginal hsource H).map C.carrierMap).comap
      (C.originalSourceMap hsource)=H := by
  rw [transportOriginal,
    Subgroup.map_comap_eq_self_of_surjective C.carrierMap_surjective,
    Subgroup.comap_map_eq_self (C.originalSourceMap_kernel_le hsource N haxis H hN)]

/-- The exterior image is literally unchanged for every subgroup. -/
theorem transportOriginal_exterior (H : Subgroup (U × E)) :
    (C.transportOriginal hsource H).map (MonoidHom.snd C.carrier E)=
      H.map (MonoidHom.snd U E) := by
  apply le_antisymm
  · rintro e ⟨⟨x,e'⟩,hx,rfl⟩
    obtain ⟨⟨y,f⟩,hy,he⟩ := hx
    exact ⟨(y,f),hy,congrArg Prod.snd he⟩
  · rintro e ⟨⟨x,e'⟩,hx,rfl⟩
    obtain ⟨y,hy⟩ := C.beta_surjective (C.originalAlpha hsource x)
    exact ⟨(y,e'),⟨(x,e'),hx,Prod.ext hy.symm rfl⟩,rfl⟩

/-- Fullness is on the actual carrier, including its internal correlations. -/
theorem transportOriginal_full_carrier (H : Subgroup (U × E))
    (hfull : ∀ x : U, ∃ e : E, (x,e)∈H) :
    ∀ y : C.carrier, ∃ e : E, (y,e)∈C.transportOriginal hsource H := by
  intro y
  obtain ⟨x,hx⟩ := C.originalAlpha_surjective hsource (C.beta y)
  obtain ⟨e,he⟩ := hfull x
  exact ⟨e,⟨(x,e),he,Prod.ext hx rfl⟩⟩

theorem transportOriginal_injective (N : Subgroup U)
    (haxis : C.axis=N.map U.subtype) : Function.Injective
    (fun H : {H : Subgroup (U × E) // ∀ x : U, x∈N → (x,1)∈H} =>
      C.transportOriginal hsource H.1) := by
  intro H K he
  apply Subtype.ext
  have hh := congrArg (fun L : Subgroup (C.carrier × E) =>
    (L.map C.carrierMap).comap (C.originalSourceMap hsource)) he
  simpa only [C.transportOriginal_reconstruct hsource N haxis H.1 H.2,
    C.transportOriginal_reconstruct hsource N haxis K.1 K.2] using hh

end Exterior
end SymmetricSubgroupAsymptotics.CheckedPermutationCarrier
