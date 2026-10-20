import SymmetricSubgroupAsymptotics.PGroupInducedHead
import SymmetricSubgroupAsymptotics.PrimeGridMiddleBound
import SymmetricSubgroupAsymptotics.FibreAntichainWidth

/-! The intrinsic head of every actual induced subrepresentation of a
finite p-group is bounded by the exact middle width of its actual p-grid. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics
open CoinducedLeadingCoordinates RepresentationLeadingAntichain

variable {k G V U : Type} [Field k] [Group G] [Finite G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup U] [Module k U]

theorem pGroup_coinduced_injective_coinvariant_middle
    (p : ℕ) [Fact p.Prime] (hG : IsPGroup p G)
    (H : Subgroup G) (rho : Representation k H V) (t : ℕ) (hindex : H.index=p^t)
    (tau : Representation k G U)
    (phi : tau.IntertwiningMap (Representation.coind H.subtype rho))
    (hphi : Function.Injective phi) :
    Module.finrank k tau.Coinvariants≤Module.finrank k V*primeGridMiddleWidth p t := by
  obtain ⟨D⟩ := pGroup_orderedCosetTransversal hG H t hindex
  let E := D.finRows
  let b := Module.finBasis k V
  let C : U →ₗ[k] (Fin (p^t*Module.finrank k V) → k) :=
    (coordinates H rho E.repr b).comp phi.toLinearMap
  have hfactor : ∀ x : G,∃ h : G,h∈H ∧ ∃ a : Fin (p^t),x=h*E.repr a :=
    fun x => E.factor x (Subgroup.mem_top x)
  have hC : Function.Injective C :=
    (coordinates_injective H rho E.repr b hfactor).comp hphi
  letI : FiniteDimensional k U := FiniteDimensional.of_injective C hC
  obtain ⟨leading,hseparated⟩ := coinvariant_labels_of_raising tau C hC
    (fullComparable (primeCosetFinComparable p t))
    (ThreeGroupHead.intertwiner_raising H rho E.repr b hfactor
      (primeCosetFinComparable p t) E.unique E.triangular tau phi)
  let fibre : Fin (Module.finrank k tau.Coinvariants) → Fin (Module.finrank k V) :=
    fun i => (finProdFinEquiv.symm (leading i)).2
  let point : Fin (Module.finrank k tau.Coinvariants) → PrimeCosetGrid p t :=
    fun i => (primeCosetGridCode p t).symm (finProdFinEquiv.symm (leading i)).1
  have hsep : ∀ i j,i≠j → fibre i=fibre j → ¬point i≤point j := by
    intro i j hij hf hp
    apply hseparated hij
    exact ⟨hf,(primeGrid_le_iff p t _ _).mp hp⟩
  have hcode : Function.Injective (fun i => (point i,fibre i)) := by
    intro i j h
    change (point i,fibre i)=(point j,fibre j) at h
    by_contra hij
    have hf : fibre i=fibre j := congrArg
      (fun z : PrimeCosetGrid p t×Fin (Module.finrank k V) => z.2) h
    have hp : point i=point j := congrArg
      (fun z : PrimeCosetGrid p t×Fin (Module.finrank k V) => z.1) h
    exact hsep i j hij hf (le_of_eq hp)
  have h := fibre_antichain_card_le Finset.univ point fibre (· ≤ ·)
    (primeGridMiddleWidth p t) hcode
    (primeGrid_antichain_card_le_middle p t (Fact.out : p.Prime).pos)
    (fun i _ j _ hij hf => hsep i j hij hf)
  simpa only [Finset.card_univ,Fintype.card_fin] using h

theorem pGroup_induced_subrepresentationHead_le_middle
    (p : ℕ) [Fact p.Prime] (hG : IsPGroup p G)
    (H : Subgroup G) (rho : Representation k H V) (t : ℕ) (hindex : H.index=p^t)
    (M : Subrepresentation (Representation.ind H.subtype rho)) :
    Module.finrank k (M.toRepresentation.IntertwiningMap (Representation.trivial k G k))≤
      Module.finrank k V*primeGridMiddleWidth p t := by
  let e := inducedElementCoinducedEquiv H rho
  let phi := e.toIntertwiningMap.comp (ThreeGroupHead.inclusion _ M)
  letI : FiniteDimensional k M.toSubmodule :=
    FiniteDimensional.of_injective phi.toLinearMap
      (e.toLinearEquiv.injective.comp Subtype.val_injective)
  rw [representationHead_finrank_eq_coinvariants]
  exact pGroup_coinduced_injective_coinvariant_middle p hG H rho t hindex
    M.toRepresentation phi (e.toLinearEquiv.injective.comp Subtype.val_injective)

end SymmetricSubgroupAsymptotics
