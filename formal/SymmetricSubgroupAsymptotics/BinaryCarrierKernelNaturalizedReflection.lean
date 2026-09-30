import SymmetricSubgroupAsymptotics.BinaryCarrierTransportNaturality

/-!
# Reflection after replacement-kernel recovery

Across a varying carrier word the quotient types cannot be compared before
the retained replacement kernels have been recovered.  This file records the
noncircular order of operations.  Equality of the transported relations first
recovers every replacement kernel.  A local normalizer may then construct the
quotient equivalence and the two commuting quotient squares.  Only after that
construction do we invoke simultaneous carrier naturality and reconstruct the
complete correlated source.

The interface treats proper carriers and quotient-identity carriers uniformly.
A fixed proper carrier ignores the recovered-kernel argument and returns its
already fixed quotient square.  An identity carrier uses the recovered kernel
to identify its normal axis and descends the source-action equivalence to the
two quotient groups.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryCarrierKernelNaturalizedReflection

open SymmetricSubgroupAsymptotics
open BinaryCarrierTransportNaturality

variable {ι : Type*} [Finite ι] [DecidableEq ι]
  {U₁ U₂ P₁ P₂ Q₁ Q₂ : ι → Type*}
  [∀ i, Group (U₁ i)] [∀ i, Group (U₂ i)]
  [∀ i, Group (P₁ i)] [∀ i, Group (P₂ i)]
  [∀ i, Group (Q₁ i)] [∀ i, Group (Q₂ i)]

/-- The local datum constructed after the replacement kernels have been
identified.  It contains exactly the quotient equivalence and the two
commuting squares needed by simultaneous carrier naturality. -/
structure QuotientSquare
    {U₁ U₂ P₁ P₂ Q₁ Q₂ : Type*}
    [Group U₁] [Group U₂] [Group P₁] [Group P₂]
    [Group Q₁] [Group Q₂]
    (alpha₁ : U₁ →* Q₁) (alpha₂ : U₂ →* Q₂)
    (beta₁ : P₁ →* Q₁) (beta₂ : P₂ →* Q₂)
    (eU : U₁ ≃* U₂) (eP : P₁ ≃* P₂) where
  quotientEquiv : Q₁ ≃* Q₂
  alpha_intertwine :
    quotientEquiv.toMonoidHom.comp alpha₁ =
      alpha₂.comp eU.toMonoidHom
  beta_intertwine :
    quotientEquiv.toMonoidHom.comp beta₁ =
      beta₂.comp eP.toMonoidHom

/-- A kernel-first local naturalizer.  It is deliberately a function of the
recovered replacement-kernel equality, preventing a dependent quotient from
being chosen before its normal subgroup is known. -/
abbrev KernelNaturalizer
    (alpha₁ : ∀ i, U₁ i →* Q₁ i)
    (alpha₂ : ∀ i, U₂ i →* Q₂ i)
    (beta₁ : ∀ i, P₁ i →* Q₁ i)
    (beta₂ : ∀ i, P₂ i →* Q₂ i)
    (eU : ∀ i, U₁ i ≃* U₂ i)
    (eP : ∀ i, P₁ i ≃* P₂ i) :=
  ∀ i,
    (beta₁ i).ker.map (eP i).toMonoidHom = (beta₂ i).ker →
      QuotientSquare (alpha₁ i) (alpha₂ i)
        (beta₁ i) (beta₂ i) (eU i) (eP i)

namespace QuotientSquare

/-- The source square carries the first quotient kernel exactly onto the
second. -/
theorem alphaKer_map_eq
    {U₁ U₂ P₁ P₂ Q₁ Q₂ : Type*}
    [Group U₁] [Group U₂] [Group P₁] [Group P₂]
    [Group Q₁] [Group Q₂]
    {alpha₁ : U₁ →* Q₁} {alpha₂ : U₂ →* Q₂}
    {beta₁ : P₁ →* Q₁} {beta₂ : P₂ →* Q₂}
    {eU : U₁ ≃* U₂} {eP : P₁ ≃* P₂}
    (S : QuotientSquare alpha₁ alpha₂ beta₁ beta₂ eU eP) :
    alpha₁.ker.map eU.toMonoidHom = alpha₂.ker := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    change alpha₂ (eU x) = 1
    have h := DFunLike.congr_fun S.alpha_intertwine x
    change S.quotientEquiv (alpha₁ x) = alpha₂ (eU x) at h
    rw [hx,map_one] at h
    exact h.symm
  · intro hy
    let x : U₁ := eU.symm y
    refine ⟨x,?_,eU.apply_symm_apply y⟩
    change alpha₁ x = 1
    apply S.quotientEquiv.injective
    have h := DFunLike.congr_fun S.alpha_intertwine x
    change S.quotientEquiv (alpha₁ x) = alpha₂ (eU x) at h
    rw [eU.apply_symm_apply,hy] at h
    simpa using h

/-- A fixed proper carrier supplies its quotient square independently of the
recovered-kernel proof. -/
def refl
    {U P Q : Type*} [Group U] [Group P] [Group Q]
    (alpha : U →* Q) (beta : P →* Q) :
    QuotientSquare alpha alpha beta beta
      (MulEquiv.refl U) (MulEquiv.refl P) := by
  refine
    { quotientEquiv := MulEquiv.refl Q
      alpha_intertwine := ?_
      beta_intertwine := ?_ }
  · rfl
  · rfl

end QuotientSquare

/-- Kernel-first simultaneous reflection.  The complete source relation is
recovered after, and only after, every local quotient square has been built
from the replacement kernels exposed by target equality. -/
theorem source_map_eq_of_transport_map_eq
    (alpha₁ : ∀ i, U₁ i →* Q₁ i)
    (alpha₂ : ∀ i, U₂ i →* Q₂ i)
    (beta₁ : ∀ i, P₁ i →* Q₁ i)
    (beta₂ : ∀ i, P₂ i →* Q₂ i)
    (eU : ∀ i, U₁ i ≃* U₂ i)
    (eP : ∀ i, P₁ i ≃* P₂ i)
    (H : Subgroup (∀ i, U₁ i)) (K : Subgroup (∀ i, U₂ i))
    (haxisH : ∀ i, carrierAxis H i = (alpha₁ i).ker)
    (haxisK : ∀ i, carrierAxis K i = (alpha₂ i).ker)
    (beta₂Surjective : ∀ i, Function.Surjective (beta₂ i))
    (naturalize : KernelNaturalizer
      alpha₁ alpha₂ beta₁ beta₂ eU eP)
    (htarget :
      (carrierTransport alpha₁ beta₁ H).map
          (productEquiv eP).toMonoidHom =
        carrierTransport alpha₂ beta₂ K) :
    H.map (productEquiv eU).toMonoidHom = K := by
  have hkernel := replacementKernels_map_eq_of_transport_map_eq
    alpha₁ alpha₂ beta₁ beta₂ eP H K
    haxisH haxisK htarget
  let S : ∀ i, QuotientSquare (alpha₁ i) (alpha₂ i)
      (beta₁ i) (beta₂ i) (eU i) (eP i) :=
    fun i => naturalize i (hkernel i)
  have haxisMapped : ∀ i, (alpha₂ i).ker ≤
      carrierAxis (H.map (productEquiv eU).toMonoidHom) i := by
    intro i
    rw [← (S i).alphaKer_map_eq,← haxisH i]
    exact (carrierAxis_map_productEquiv eU H i).le
  exact BinaryCarrierTransportNaturality.source_map_eq_of_carrierTransport_map_eq
    alpha₁ alpha₂ beta₁ beta₂ eU eP
    (fun i => (S i).quotientEquiv)
    (fun i => (S i).alpha_intertwine)
    (fun i => (S i).beta_intertwine)
    beta₂Surjective H K haxisMapped
    (fun i => (haxisK i).ge) htarget

/-- Displayed-ambient form of kernel-first reflection.  The compatible
replacement-product square is cancelled through the faithful right-hand
embedding before any quotient equivalence is constructed. -/
theorem source_map_eq_of_ambientTransport_map_eq
    {D₁ D₂ : Type*} [Group D₁] [Group D₂]
    (alpha₁ : ∀ i, U₁ i →* Q₁ i)
    (alpha₂ : ∀ i, U₂ i →* Q₂ i)
    (beta₁ : ∀ i, P₁ i →* Q₁ i)
    (beta₂ : ∀ i, P₂ i →* Q₂ i)
    (eU : ∀ i, U₁ i ≃* U₂ i)
    (eP : ∀ i, P₁ i ≃* P₂ i)
    (H : Subgroup (∀ i, U₁ i)) (K : Subgroup (∀ i, U₂ i))
    (haxisH : ∀ i, carrierAxis H i = (alpha₁ i).ker)
    (haxisK : ∀ i, carrierAxis K i = (alpha₂ i).ker)
    (beta₂Surjective : ∀ i, Function.Surjective (beta₂ i))
    (naturalize : KernelNaturalizer
      alpha₁ alpha₂ beta₁ beta₂ eU eP)
    (embed₁ : (∀ i, P₁ i) →* D₁)
    (embed₂ : (∀ i, P₂ i) →* D₂)
    (embed₂Injective : Function.Injective embed₂)
    (eD : D₁ ≃* D₂)
    (hembed : eD.toMonoidHom.comp embed₁ =
      embed₂.comp (productEquiv eP).toMonoidHom)
    (htarget :
      ((carrierTransport alpha₁ beta₁ H).map embed₁).map
          eD.toMonoidHom =
        (carrierTransport alpha₂ beta₂ K).map embed₂) :
    H.map (productEquiv eU).toMonoidHom = K := by
  apply source_map_eq_of_transport_map_eq
    alpha₁ alpha₂ beta₁ beta₂ eU eP H K
    haxisH haxisK beta₂Surjective naturalize
  apply Subgroup.map_injective (f := embed₂) embed₂Injective
  calc
    ((carrierTransport alpha₁ beta₁ H).map
        (productEquiv eP).toMonoidHom).map embed₂ =
        ((carrierTransport alpha₁ beta₁ H).map embed₁).map
          eD.toMonoidHom := by
      rw [Subgroup.map_map,Subgroup.map_map,hembed]
    _ = (carrierTransport alpha₂ beta₂ K).map embed₂ := htarget

end SymmetricSubgroupAsymptotics.BinaryCarrierKernelNaturalizedReflection

end
