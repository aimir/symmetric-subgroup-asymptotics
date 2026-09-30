import SymmetricSubgroupAsymptotics.BinaryCarrierKernelNaturalizedReflection

/-!
# Kernel-first carrier reflection across an index equivalence

The source-orbit sets of two labelled subgroups are only equivalent, not
definitionally equal.  This module extends kernel-first carrier naturality to
that situation.  It simultaneously reindexes the product and changes every
coordinate group, while replacement kernels are still recovered before the
dependent quotient groups are compared.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryCarrierIndexedKernelReflection

open SymmetricSubgroupAsymptotics
open BinaryCarrierKernelNaturalizedReflection

variable {ι₁ ι₂ : Type*} [Finite ι₁] [Finite ι₂]
  [DecidableEq ι₁] [DecidableEq ι₂]
  {U₁ P₁ Q₁ : ι₁ → Type*} {U₂ P₂ Q₂ : ι₂ → Type*}
  [∀ i, Group (U₁ i)] [∀ i, Group (P₁ i)] [∀ i, Group (Q₁ i)]
  [∀ i, Group (U₂ i)] [∀ i, Group (P₂ i)] [∀ i, Group (Q₂ i)]

/-- Reindex a dependent product without changing its fibres. -/
def indexedReindexEquiv (eI : ι₁ ≃ ι₂) :
    (∀ i, U₂ (eI i)) ≃* (∀ j, U₂ j) where
  toEquiv := Equiv.piCongrLeft U₂ eI
  map_mul' := by
    intro x y
    apply (Equiv.piCongrLeft U₂ eI).symm.injective
    funext i
    simp

/-- Reindex a dependent product and change every coordinate group. -/
def indexedProductEquiv (eI : ι₁ ≃ ι₂)
    (e : ∀ i, U₁ i ≃* U₂ (eI i)) :
    (∀ i, U₁ i) ≃* (∀ j, U₂ j) :=
  (MulEquiv.piCongrRight e).trans (indexedReindexEquiv eI)

@[simp] theorem indexedProductEquiv_apply
    (eI : ι₁ ≃ ι₂) (e : ∀ i, U₁ i ≃* U₂ (eI i))
    (x : ∀ i, U₁ i) (i : ι₁) :
    indexedProductEquiv eI e x (eI i) = e i (x i) :=
  by simp [indexedProductEquiv,indexedReindexEquiv]

/-- Coordinate axes commute with simultaneous index and group transport. -/
theorem carrierAxis_map_indexedProductEquiv
    (eI : ι₁ ≃ ι₂) (e : ∀ i, U₁ i ≃* U₂ (eI i))
    (H : Subgroup (∀ i, U₁ i)) (i : ι₁) :
    (carrierAxis H i).map (e i).toMonoidHom =
      carrierAxis (H.map (indexedProductEquiv eI e).toMonoidHom) (eI i) := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    change MonoidHom.mulSingle U₂ (eI i) (e i x) ∈
      H.map (indexedProductEquiv eI e).toMonoidHom
    refine Subgroup.mem_map.mpr
      ⟨MonoidHom.mulSingle U₁ i x,hx,?_⟩
    funext j
    obtain ⟨k,rfl⟩ := eI.surjective j
    by_cases hki : k = i
    · subst k
      simp
    · have hne : eI k ≠ eI i := fun h => hki (eI.injective h)
      simp [hne,hki]
  · intro hy
    change MonoidHom.mulSingle U₂ (eI i) y ∈
      H.map (indexedProductEquiv eI e).toMonoidHom at hy
    obtain ⟨z,hz,hzeq⟩ := Subgroup.mem_map.mp hy
    let x : U₁ i := (e i).symm y
    refine Subgroup.mem_map.mpr ⟨x,?_,(e i).apply_symm_apply y⟩
    change MonoidHom.mulSingle U₁ i x ∈ H
    convert hz using 1
    funext k
    apply (e k).injective
    have hk := congrFun hzeq (eI k)
    by_cases hki : k = i
    · subst k
      simpa [x] using hk.symm
    · have hne : eI k ≠ eI i := fun h => hki (eI.injective h)
      simpa [hne,hki] using hk.symm

/-- Product quotient maps commute with indexed coordinate transport. -/
theorem carrierProductMap_indexed_natural
    (eI : ι₁ ≃ ι₂)
    (alpha₁ : ∀ i, U₁ i →* Q₁ i)
    (alpha₂ : ∀ i, U₂ i →* Q₂ i)
    (eU : ∀ i, U₁ i ≃* U₂ (eI i))
    (eQ : ∀ i, Q₁ i ≃* Q₂ (eI i))
    (halpha : ∀ i,
      (eQ i).toMonoidHom.comp (alpha₁ i) =
        (alpha₂ (eI i)).comp (eU i).toMonoidHom)
    (x : ∀ i, U₁ i) :
    indexedProductEquiv eI eQ (carrierProductMap alpha₁ x) =
      carrierProductMap alpha₂ (indexedProductEquiv eI eU x) := by
  funext j
  obtain ⟨i,rfl⟩ := eI.surjective j
  simpa only [indexedProductEquiv_apply,carrierProductMap,
    MonoidHom.coe_mk,OneHom.coe_mk] using
    DFunLike.congr_fun (halpha i) (x i)

/-- Carrier transport is natural across an index equivalence. -/
theorem carrierTransport_indexed_natural
    (eI : ι₁ ≃ ι₂)
    (alpha₁ : ∀ i, U₁ i →* Q₁ i)
    (alpha₂ : ∀ i, U₂ i →* Q₂ i)
    (beta₁ : ∀ i, P₁ i →* Q₁ i)
    (beta₂ : ∀ i, P₂ i →* Q₂ i)
    (eU : ∀ i, U₁ i ≃* U₂ (eI i))
    (eP : ∀ i, P₁ i ≃* P₂ (eI i))
    (eQ : ∀ i, Q₁ i ≃* Q₂ (eI i))
    (halpha : ∀ i,
      (eQ i).toMonoidHom.comp (alpha₁ i) =
        (alpha₂ (eI i)).comp (eU i).toMonoidHom)
    (hbeta : ∀ i,
      (eQ i).toMonoidHom.comp (beta₁ i) =
        (beta₂ (eI i)).comp (eP i).toMonoidHom)
    (H : Subgroup (∀ i, U₁ i)) :
    (carrierTransport alpha₁ beta₁ H).map
        (indexedProductEquiv eI eP).toMonoidHom =
      carrierTransport alpha₂ beta₂
        (H.map (indexedProductEquiv eI eU).toMonoidHom) := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    change carrierProductMap beta₁ y ∈ H.map (carrierProductMap alpha₁) at hy
    obtain ⟨u,hu,huq⟩ := Subgroup.mem_map.mp hy
    change carrierProductMap beta₂ (indexedProductEquiv eI eP y) ∈
      (H.map (indexedProductEquiv eI eU).toMonoidHom).map
        (carrierProductMap alpha₂)
    refine Subgroup.mem_map.mpr
      ⟨indexedProductEquiv eI eU u,
        Subgroup.mem_map.mpr ⟨u,hu,rfl⟩,?_⟩
    calc
      carrierProductMap alpha₂ (indexedProductEquiv eI eU u) =
          indexedProductEquiv eI eQ (carrierProductMap alpha₁ u) :=
        (carrierProductMap_indexed_natural eI alpha₁ alpha₂ eU eQ halpha u).symm
      _ = indexedProductEquiv eI eQ (carrierProductMap beta₁ y) :=
        congrArg (indexedProductEquiv eI eQ) huq
      _ = carrierProductMap beta₂ (indexedProductEquiv eI eP y) :=
        carrierProductMap_indexed_natural eI beta₁ beta₂ eP eQ hbeta y
  · intro hx
    let y : ∀ i, P₁ i := (indexedProductEquiv eI eP).symm x
    refine Subgroup.mem_map.mpr
      ⟨y,?_,(indexedProductEquiv eI eP).apply_symm_apply x⟩
    change carrierProductMap beta₁ y ∈ H.map (carrierProductMap alpha₁)
    change carrierProductMap beta₂ x ∈
      (H.map (indexedProductEquiv eI eU).toMonoidHom).map
        (carrierProductMap alpha₂) at hx
    obtain ⟨v,hv,hvq⟩ := Subgroup.mem_map.mp hx
    obtain ⟨u,hu,huv⟩ := Subgroup.mem_map.mp hv
    refine Subgroup.mem_map.mpr ⟨u,hu,?_⟩
    apply (indexedProductEquiv eI eQ).injective
    calc
      indexedProductEquiv eI eQ (carrierProductMap alpha₁ u) =
          carrierProductMap alpha₂ (indexedProductEquiv eI eU u) :=
        carrierProductMap_indexed_natural eI alpha₁ alpha₂ eU eQ halpha u
      _ = carrierProductMap alpha₂ v := congrArg (carrierProductMap alpha₂) huv
      _ = carrierProductMap beta₂ x := hvq
      _ = carrierProductMap beta₂ (indexedProductEquiv eI eP y) := by
        rw [(indexedProductEquiv eI eP).apply_symm_apply]
      _ = indexedProductEquiv eI eQ (carrierProductMap beta₁ y) :=
        (carrierProductMap_indexed_natural eI beta₁ beta₂ eP eQ hbeta y).symm

/-- Target equality recovers the replacement kernels on matched indices. -/
theorem replacementKernels_indexed
    (eI : ι₁ ≃ ι₂)
    (alpha₁ : ∀ i, U₁ i →* Q₁ i)
    (alpha₂ : ∀ i, U₂ i →* Q₂ i)
    (beta₁ : ∀ i, P₁ i →* Q₁ i)
    (beta₂ : ∀ i, P₂ i →* Q₂ i)
    (eP : ∀ i, P₁ i ≃* P₂ (eI i))
    (H : Subgroup (∀ i, U₁ i)) (K : Subgroup (∀ i, U₂ i))
    (haxisH : ∀ i, carrierAxis H i = (alpha₁ i).ker)
    (haxisK : ∀ i, carrierAxis K i = (alpha₂ i).ker)
    (htarget :
      (carrierTransport alpha₁ beta₁ H).map
          (indexedProductEquiv eI eP).toMonoidHom =
        carrierTransport alpha₂ beta₂ K) :
    ∀ i, (beta₁ i).ker.map (eP i).toMonoidHom =
      (beta₂ (eI i)).ker := by
  intro i
  calc
    (beta₁ i).ker.map (eP i).toMonoidHom =
        (carrierAxis (carrierTransport alpha₁ beta₁ H) i).map
          (eP i).toMonoidHom := by
      rw [carrierAxis_carrierTransport_eq_ker alpha₁ beta₁ H haxisH i]
    _ = carrierAxis
          ((carrierTransport alpha₁ beta₁ H).map
            (indexedProductEquiv eI eP).toMonoidHom) (eI i) :=
      carrierAxis_map_indexedProductEquiv eI eP
        (carrierTransport alpha₁ beta₁ H) i
    _ = carrierAxis (carrierTransport alpha₂ beta₂ K) (eI i) :=
      congrArg (fun T => carrierAxis T (eI i)) htarget
    _ = (beta₂ (eI i)).ker :=
      carrierAxis_carrierTransport_eq_ker alpha₂ beta₂ K haxisK (eI i)

/-- Full kernel-first reflection across both an occurrence reindexing and
varying local carrier data. -/
theorem source_map_eq_of_ambientTransport_map_eq
    {D₁ D₂ : Type*} [Group D₁] [Group D₂]
    (eI : ι₁ ≃ ι₂)
    (alpha₁ : ∀ i, U₁ i →* Q₁ i)
    (alpha₂ : ∀ i, U₂ i →* Q₂ i)
    (beta₁ : ∀ i, P₁ i →* Q₁ i)
    (beta₂ : ∀ i, P₂ i →* Q₂ i)
    (eU : ∀ i, U₁ i ≃* U₂ (eI i))
    (eP : ∀ i, P₁ i ≃* P₂ (eI i))
    (H : Subgroup (∀ i, U₁ i)) (K : Subgroup (∀ i, U₂ i))
    (haxisH : ∀ i, carrierAxis H i = (alpha₁ i).ker)
    (haxisK : ∀ i, carrierAxis K i = (alpha₂ i).ker)
    (beta₂Surjective : ∀ i, Function.Surjective (beta₂ i))
    (naturalize : ∀ i,
      (beta₁ i).ker.map (eP i).toMonoidHom = (beta₂ (eI i)).ker →
        QuotientSquare (alpha₁ i) (alpha₂ (eI i))
          (beta₁ i) (beta₂ (eI i)) (eU i) (eP i))
    (embed₁ : (∀ i, P₁ i) →* D₁)
    (embed₂ : (∀ i, P₂ i) →* D₂)
    (embed₂Injective : Function.Injective embed₂)
    (eD : D₁ ≃* D₂)
    (hembed : eD.toMonoidHom.comp embed₁ =
      embed₂.comp (indexedProductEquiv eI eP).toMonoidHom)
    (htarget :
      ((carrierTransport alpha₁ beta₁ H).map embed₁).map eD.toMonoidHom =
        (carrierTransport alpha₂ beta₂ K).map embed₂) :
    H.map (indexedProductEquiv eI eU).toMonoidHom = K := by
  have htransport :
      (carrierTransport alpha₁ beta₁ H).map
          (indexedProductEquiv eI eP).toMonoidHom =
        carrierTransport alpha₂ beta₂ K := by
    apply Subgroup.map_injective (f := embed₂) embed₂Injective
    calc
      ((carrierTransport alpha₁ beta₁ H).map
          (indexedProductEquiv eI eP).toMonoidHom).map embed₂ =
          ((carrierTransport alpha₁ beta₁ H).map embed₁).map eD.toMonoidHom := by
        rw [Subgroup.map_map,Subgroup.map_map,hembed]
      _ = (carrierTransport alpha₂ beta₂ K).map embed₂ := htarget
  have hkernel := replacementKernels_indexed eI
    alpha₁ alpha₂ beta₁ beta₂ eP H K haxisH haxisK htransport
  let S : ∀ i, QuotientSquare (alpha₁ i) (alpha₂ (eI i))
      (beta₁ i) (beta₂ (eI i)) (eU i) (eP i) :=
    fun i => naturalize i (hkernel i)
  have haxisMapped : ∀ i, (alpha₂ i).ker ≤
      carrierAxis (H.map (indexedProductEquiv eI eU).toMonoidHom) i := by
    intro j
    obtain ⟨i,rfl⟩ := eI.surjective j
    rw [← (S i).alphaKer_map_eq,← haxisH i]
    exact (carrierAxis_map_indexedProductEquiv eI eU H i).le
  have hnatural :
      carrierTransport alpha₂ beta₂
          (H.map (indexedProductEquiv eI eU).toMonoidHom) =
        carrierTransport alpha₂ beta₂ K := by
    rw [← carrierTransport_indexed_natural eI
      alpha₁ alpha₂ beta₁ beta₂ eU eP
      (fun i => (S i).quotientEquiv)
      (fun i => (S i).alpha_intertwine)
      (fun i => (S i).beta_intertwine) H]
    exact htransport
  calc
    H.map (indexedProductEquiv eI eU).toMonoidHom =
        ((carrierTransport alpha₂ beta₂
          (H.map (indexedProductEquiv eI eU).toMonoidHom)).map
            (carrierProductMap beta₂)).comap (carrierProductMap alpha₂) :=
      (carrierTransport_reconstruct alpha₂ beta₂ beta₂Surjective
        (H.map (indexedProductEquiv eI eU).toMonoidHom) haxisMapped).symm
    _ = ((carrierTransport alpha₂ beta₂ K).map
          (carrierProductMap beta₂)).comap (carrierProductMap alpha₂) := by
      rw [hnatural]
    _ = K := carrierTransport_reconstruct alpha₂ beta₂ beta₂Surjective K
      (fun i => (haxisK i).ge)

end SymmetricSubgroupAsymptotics.BinaryCarrierIndexedKernelReflection

end
