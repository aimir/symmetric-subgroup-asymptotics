import SymmetricSubgroupAsymptotics.BinaryCarrierVaryingAxisRecovery

/-!
# Naturality of simultaneous carrier transport

Carrier transport is defined by one image and one preimage.  This file proves
that it commutes with arbitrary coordinatewise group equivalences which
intertwine the source and replacement quotient maps.  The index set is fixed;
an application first folds an occurrence reindexing into its dependent product
equivalences.

The statement keeps the replacement groups abstract.  In particular they may
be nonabelian proper subdirect carriers.  No fullness, commutativity, or
surjectivity hypothesis is used by the naturality proof.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryCarrierTransportNaturality

open SymmetricSubgroupAsymptotics

variable {ι : Type*}
  {U₁ U₂ P₁ P₂ Q₁ Q₂ : ι → Type*}
  [∀ i, Group (U₁ i)] [∀ i, Group (U₂ i)]
  [∀ i, Group (P₁ i)] [∀ i, Group (P₂ i)]
  [∀ i, Group (Q₁ i)] [∀ i, Group (Q₂ i)]

/-- Assemble coordinatewise group equivalences into one product
equivalence. -/
def productEquiv (e : ∀ i, U₁ i ≃* U₂ i) :
    (∀ i, U₁ i) ≃* (∀ i, U₂ i) :=
  MulEquiv.piCongrRight e

@[simp] theorem productEquiv_apply
    (e : ∀ i, U₁ i ≃* U₂ i) (x : ∀ i, U₁ i) (i : ι) :
  productEquiv e x i = e i (x i) := rfl

/-- Coordinate axes commute with a coordinatewise product equivalence.  This
is the kernel-recovery half of naturality and deliberately requires no
comparison of quotient groups. -/
theorem carrierAxis_map_productEquiv
    [DecidableEq ι]
    (e : ∀ i, U₁ i ≃* U₂ i)
    (H : Subgroup (∀ i, U₁ i)) (i : ι) :
    (carrierAxis H i).map (e i).toMonoidHom =
      carrierAxis (H.map (productEquiv e).toMonoidHom) i := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    change MonoidHom.mulSingle U₂ i (e i x) ∈
      H.map (productEquiv e).toMonoidHom
    refine Subgroup.mem_map.mpr
      ⟨MonoidHom.mulSingle U₁ i x,hx,?_⟩
    funext j
    by_cases hji : j = i
    · subst j
      simp [productEquiv_apply]
    · simp [productEquiv_apply,hji]
  · intro hy
    change MonoidHom.mulSingle U₂ i y ∈
      H.map (productEquiv e).toMonoidHom at hy
    obtain ⟨z,hz,hzeq⟩ := Subgroup.mem_map.mp hy
    let x : U₁ i := (e i).symm y
    refine Subgroup.mem_map.mpr ⟨x,?_,(e i).apply_symm_apply y⟩
    change MonoidHom.mulSingle U₁ i x ∈ H
    convert hz using 1
    funext j
    apply (e j).injective
    have hj := congrFun hzeq j
    by_cases hji : j = i
    · subst j
      simpa [x,productEquiv_apply] using hj.symm
    · simpa [productEquiv_apply,hji] using hj.symm

/-- Equality of two transported relations after a coordinatewise carrier
equivalence recovers the replacement kernels before the quotient types have
been aligned.  This is the noncircular input for varying identity cells. -/
theorem replacementKernels_map_eq_of_transport_map_eq
    [Finite ι] [DecidableEq ι]
    (alpha₁ : ∀ i, U₁ i →* Q₁ i)
    (alpha₂ : ∀ i, U₂ i →* Q₂ i)
    (beta₁ : ∀ i, P₁ i →* Q₁ i)
    (beta₂ : ∀ i, P₂ i →* Q₂ i)
    (eP : ∀ i, P₁ i ≃* P₂ i)
    (H₁ : Subgroup (∀ i, U₁ i))
    (H₂ : Subgroup (∀ i, U₂ i))
    (haxis₁ : ∀ i, carrierAxis H₁ i = (alpha₁ i).ker)
    (haxis₂ : ∀ i, carrierAxis H₂ i = (alpha₂ i).ker)
    (htransport :
      (carrierTransport alpha₁ beta₁ H₁).map
          (productEquiv eP).toMonoidHom =
        carrierTransport alpha₂ beta₂ H₂) :
    ∀ i, (beta₁ i).ker.map (eP i).toMonoidHom =
      (beta₂ i).ker := by
  intro i
  calc
    (beta₁ i).ker.map (eP i).toMonoidHom =
        (carrierAxis (carrierTransport alpha₁ beta₁ H₁) i).map
          (eP i).toMonoidHom := by
      rw [carrierAxis_carrierTransport_eq_ker alpha₁ beta₁ H₁
        haxis₁ i]
    _ = carrierAxis
          ((carrierTransport alpha₁ beta₁ H₁).map
            (productEquiv eP).toMonoidHom) i :=
      carrierAxis_map_productEquiv eP
        (carrierTransport alpha₁ beta₁ H₁) i
    _ = carrierAxis (carrierTransport alpha₂ beta₂ H₂) i :=
      congrArg (fun T => carrierAxis T i) htransport
    _ = (beta₂ i).ker :=
      carrierAxis_carrierTransport_eq_ker alpha₂ beta₂ H₂
        haxis₂ i

/-- Coordinatewise intertwining gives exact naturality of the simultaneous
product quotient map. -/
theorem carrierProductMap_natural
    (α₁ : ∀ i, U₁ i →* Q₁ i)
    (α₂ : ∀ i, U₂ i →* Q₂ i)
    (eU : ∀ i, U₁ i ≃* U₂ i)
    (eQ : ∀ i, Q₁ i ≃* Q₂ i)
    (hα : ∀ i,
      (eQ i).toMonoidHom.comp (α₁ i) =
        (α₂ i).comp (eU i).toMonoidHom)
    (x : ∀ i, U₁ i) :
    productEquiv eQ (carrierProductMap α₁ x) =
      carrierProductMap α₂ (productEquiv eU x) := by
  funext i
  exact DFunLike.congr_fun (hα i) (x i)

/-- Simultaneous carrier transport commutes with all compatible
coordinatewise group equivalences.  This retains the entire source relation
and every internal relation of each replacement group. -/
theorem carrierTransport_natural
    (α₁ : ∀ i, U₁ i →* Q₁ i)
    (α₂ : ∀ i, U₂ i →* Q₂ i)
    (β₁ : ∀ i, P₁ i →* Q₁ i)
    (β₂ : ∀ i, P₂ i →* Q₂ i)
    (eU : ∀ i, U₁ i ≃* U₂ i)
    (eP : ∀ i, P₁ i ≃* P₂ i)
    (eQ : ∀ i, Q₁ i ≃* Q₂ i)
    (hα : ∀ i,
      (eQ i).toMonoidHom.comp (α₁ i) =
        (α₂ i).comp (eU i).toMonoidHom)
    (hβ : ∀ i,
      (eQ i).toMonoidHom.comp (β₁ i) =
        (β₂ i).comp (eP i).toMonoidHom)
    (H : Subgroup (∀ i, U₁ i)) :
    (carrierTransport α₁ β₁ H).map (productEquiv eP).toMonoidHom =
      carrierTransport α₂ β₂
        (H.map (productEquiv eU).toMonoidHom) := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    change carrierProductMap β₁ y ∈ H.map (carrierProductMap α₁) at hy
    obtain ⟨u,hu,huq⟩ := Subgroup.mem_map.mp hy
    change carrierProductMap β₂ (productEquiv eP y) ∈
      (H.map (productEquiv eU).toMonoidHom).map (carrierProductMap α₂)
    refine Subgroup.mem_map.mpr
      ⟨productEquiv eU u,Subgroup.mem_map.mpr ⟨u,hu,rfl⟩,?_⟩
    calc
      carrierProductMap α₂ (productEquiv eU u) =
          productEquiv eQ (carrierProductMap α₁ u) :=
        (carrierProductMap_natural α₁ α₂ eU eQ hα u).symm
      _ = productEquiv eQ (carrierProductMap β₁ y) :=
        congrArg (productEquiv eQ) huq
      _ = carrierProductMap β₂ (productEquiv eP y) :=
        carrierProductMap_natural β₁ β₂ eP eQ hβ y
  · intro hx
    let y : ∀ i, P₁ i := (productEquiv eP).symm x
    refine Subgroup.mem_map.mpr ⟨y,?_,(productEquiv eP).apply_symm_apply x⟩
    change carrierProductMap β₁ y ∈ H.map (carrierProductMap α₁)
    change carrierProductMap β₂ x ∈
      (H.map (productEquiv eU).toMonoidHom).map (carrierProductMap α₂) at hx
    obtain ⟨v,hv,hvq⟩ := Subgroup.mem_map.mp hx
    obtain ⟨u,hu,huv⟩ := Subgroup.mem_map.mp hv
    refine Subgroup.mem_map.mpr ⟨u,hu,?_⟩
    apply (productEquiv eQ).injective
    calc
      productEquiv eQ (carrierProductMap α₁ u) =
          carrierProductMap α₂ (productEquiv eU u) :=
        carrierProductMap_natural α₁ α₂ eU eQ hα u
      _ = carrierProductMap α₂ v := congrArg (carrierProductMap α₂) huv
      _ = carrierProductMap β₂ x := hvq
      _ = carrierProductMap β₂ (productEquiv eP y) := by
        rw [(productEquiv eP).apply_symm_apply]
      _ = productEquiv eQ (carrierProductMap β₁ y) :=
        (carrierProductMap_natural β₁ β₂ eP eQ hβ y).symm

/-! ## Passage to an arbitrary displayed ambient group -/

/-- Naturality survives any compatible faithful (or nonfaithful) realization
of the replacement products in displayed ambient groups.  For literal carrier
words the two embeddings are `carrierReplacementEmbedding`, and `eD` is the
cell/point reindexing induced by the matched route skeleton. -/
theorem carrierTransport_map_natural
    {D₁ D₂ : Type*} [Group D₁] [Group D₂]
    (α₁ : ∀ i, U₁ i →* Q₁ i)
    (α₂ : ∀ i, U₂ i →* Q₂ i)
    (β₁ : ∀ i, P₁ i →* Q₁ i)
    (β₂ : ∀ i, P₂ i →* Q₂ i)
    (eU : ∀ i, U₁ i ≃* U₂ i)
    (eP : ∀ i, P₁ i ≃* P₂ i)
    (eQ : ∀ i, Q₁ i ≃* Q₂ i)
    (hα : ∀ i,
      (eQ i).toMonoidHom.comp (α₁ i) =
        (α₂ i).comp (eU i).toMonoidHom)
    (hβ : ∀ i,
      (eQ i).toMonoidHom.comp (β₁ i) =
        (β₂ i).comp (eP i).toMonoidHom)
    (embed₁ : (∀ i, P₁ i) →* D₁)
    (embed₂ : (∀ i, P₂ i) →* D₂)
    (eD : D₁ ≃* D₂)
    (hembed : eD.toMonoidHom.comp embed₁ =
      embed₂.comp (productEquiv eP).toMonoidHom)
    (H : Subgroup (∀ i, U₁ i)) :
    ((carrierTransport α₁ β₁ H).map embed₁).map eD.toMonoidHom =
      (carrierTransport α₂ β₂
        (H.map (productEquiv eU).toMonoidHom)).map embed₂ := by
  rw [Subgroup.map_map,hembed,← Subgroup.map_map]
  rw [carrierTransport_natural α₁ α₂ β₁ β₂ eU eP eQ hα hβ H]

/-! ## Reflection through a natural carrier square -/

/-- Equality of transported carrier relations after the replacement-group
equivalence recovers equality of the complete source relation after the
source-group equivalence.  Thus every cross-coordinate correlation survives
the change of route coordinates. -/
theorem source_map_eq_of_carrierTransport_map_eq
    [Finite ι] [DecidableEq ι]
    (α₁ : ∀ i, U₁ i →* Q₁ i)
    (α₂ : ∀ i, U₂ i →* Q₂ i)
    (β₁ : ∀ i, P₁ i →* Q₁ i)
    (β₂ : ∀ i, P₂ i →* Q₂ i)
    (eU : ∀ i, U₁ i ≃* U₂ i)
    (eP : ∀ i, P₁ i ≃* P₂ i)
    (eQ : ∀ i, Q₁ i ≃* Q₂ i)
    (hα : ∀ i,
      (eQ i).toMonoidHom.comp (α₁ i) =
        (α₂ i).comp (eU i).toMonoidHom)
    (hβ : ∀ i,
      (eQ i).toMonoidHom.comp (β₁ i) =
        (β₂ i).comp (eP i).toMonoidHom)
    (hβ₂ : ∀ i, Function.Surjective (β₂ i))
    (H : Subgroup (∀ i, U₁ i)) (K : Subgroup (∀ i, U₂ i))
    (haxisH : ∀ i, (α₂ i).ker ≤
      carrierAxis (H.map (productEquiv eU).toMonoidHom) i)
    (haxisK : ∀ i, (α₂ i).ker ≤ carrierAxis K i)
    (htarget :
      (carrierTransport α₁ β₁ H).map
          (productEquiv eP).toMonoidHom =
        carrierTransport α₂ β₂ K) :
    H.map (productEquiv eU).toMonoidHom = K := by
  have htransport :
      carrierTransport α₂ β₂
          (H.map (productEquiv eU).toMonoidHom) =
        carrierTransport α₂ β₂ K := by
    rw [← carrierTransport_natural
      α₁ α₂ β₁ β₂ eU eP eQ hα hβ H]
    exact htarget
  calc
    H.map (productEquiv eU).toMonoidHom =
        ((carrierTransport α₂ β₂
            (H.map (productEquiv eU).toMonoidHom)).map
          (carrierProductMap β₂)).comap (carrierProductMap α₂) :=
      (carrierTransport_reconstruct α₂ β₂ hβ₂
        (H.map (productEquiv eU).toMonoidHom) haxisH).symm
    _ = ((carrierTransport α₂ β₂ K).map
          (carrierProductMap β₂)).comap (carrierProductMap α₂) := by
      rw [htransport]
    _ = K := carrierTransport_reconstruct α₂ β₂ hβ₂ K haxisK

/-- Displayed-ambient form of the preceding reflection theorem.  A compatible
equivalence between displayed ambient groups is cancelled through the
faithful second embedding before reconstructing the exact source relation.
This includes nonabelian proper-subdirect replacement coordinates. -/
theorem source_map_eq_of_ambientTransport_map_eq
    [Finite ι] [DecidableEq ι]
    {D₁ D₂ : Type*} [Group D₁] [Group D₂]
    (α₁ : ∀ i, U₁ i →* Q₁ i)
    (α₂ : ∀ i, U₂ i →* Q₂ i)
    (β₁ : ∀ i, P₁ i →* Q₁ i)
    (β₂ : ∀ i, P₂ i →* Q₂ i)
    (eU : ∀ i, U₁ i ≃* U₂ i)
    (eP : ∀ i, P₁ i ≃* P₂ i)
    (eQ : ∀ i, Q₁ i ≃* Q₂ i)
    (hα : ∀ i,
      (eQ i).toMonoidHom.comp (α₁ i) =
        (α₂ i).comp (eU i).toMonoidHom)
    (hβ : ∀ i,
      (eQ i).toMonoidHom.comp (β₁ i) =
        (β₂ i).comp (eP i).toMonoidHom)
    (hβ₂ : ∀ i, Function.Surjective (β₂ i))
    (embed₁ : (∀ i, P₁ i) →* D₁)
    (embed₂ : (∀ i, P₂ i) →* D₂)
    (embed₂Injective : Function.Injective embed₂)
    (eD : D₁ ≃* D₂)
    (hembed : eD.toMonoidHom.comp embed₁ =
      embed₂.comp (productEquiv eP).toMonoidHom)
    (H : Subgroup (∀ i, U₁ i)) (K : Subgroup (∀ i, U₂ i))
    (haxisH : ∀ i, (α₂ i).ker ≤
      carrierAxis (H.map (productEquiv eU).toMonoidHom) i)
    (haxisK : ∀ i, (α₂ i).ker ≤ carrierAxis K i)
    (htarget :
      ((carrierTransport α₁ β₁ H).map embed₁).map
          eD.toMonoidHom =
        (carrierTransport α₂ β₂ K).map embed₂) :
    H.map (productEquiv eU).toMonoidHom = K := by
  apply source_map_eq_of_carrierTransport_map_eq
    α₁ α₂ β₁ β₂ eU eP eQ hα hβ hβ₂ H K haxisH haxisK
  apply Subgroup.map_injective (f := embed₂) embed₂Injective
  calc
    ((carrierTransport α₁ β₁ H).map
        (productEquiv eP).toMonoidHom).map embed₂ =
        ((carrierTransport α₁ β₁ H).map embed₁).map
          eD.toMonoidHom := by
      rw [Subgroup.map_map,Subgroup.map_map,hembed]
    _ = (carrierTransport α₂ β₂ K).map embed₂ := htarget

end SymmetricSubgroupAsymptotics.BinaryCarrierTransportNaturality

end
