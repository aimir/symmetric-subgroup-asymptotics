import SymmetricSubgroupAsymptotics.TerminalRetractions
import SymmetricSubgroupAsymptotics.BinaryAbelianization

/-! Exact central-extension fibres retaining the original splitting annihilator. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

variable {X Y K A : Type*} [Group X] [Group Y] [AddCommGroup K] [Module (ZMod 2) K]
    [AddCommGroup A] [Module (ZMod 2) A]
    (π : X →* Y) (e : Multiplicative K ≃* π.ker)

private theorem restriction_zero_iff (f : Additive X →+ A) :
    f ∈ (terminalVectorRestriction π e (A := A)).ker ↔
      (MonoidHom.toAdditive π).ker ≤ f.ker := by
  constructor
  · intro hf x hx
    change π x.toMul = 1 at hx
    let k : K := (e.symm ⟨x.toMul,hx⟩).toAdd
    have he : terminalKernelInclusion π e (Multiplicative.ofAdd k) = x.toMul :=
      congrArg Subtype.val (e.apply_symm_apply _)
    have h := LinearMap.congr_fun hf k
    change f (Additive.ofMul (terminalKernelInclusion π e (Multiplicative.ofAdd k))) = 0 at h
    simpa only [he] using h
  · intro h
    apply LinearMap.ext
    intro k
    exact h (by change π (terminalKernelInclusion π e (Multiplicative.ofAdd k)) = 1; simp)

/-- Homomorphisms vanishing on the original kernel are exactly pullbacks
of homomorphisms on the actual complete quotient Y. -/
def terminalZeroRestrictionEquiv (hπ : Function.Surjective π) :
    (terminalVectorRestriction π e (A := A)).ker ≃ (Additive Y →+ A) :=
  (Equiv.subtypeEquivRight (restriction_zero_iff π e)).trans
    ((MonoidHom.toAdditive π).liftOfSurjective (by
      intro y
      obtain ⟨x,hx⟩ := hπ y.toMul
      exact ⟨Additive.ofMul x,hx⟩))

/-- Translation by one actual extension identifies the whole extension
fibre with the zero-restriction space, including every coboundary. -/
def terminalRetractionTranslateEquiv (W : Submodule (ZMod 2) K)
    (f₀ : TerminalRetractionFibre π e W) :
    TerminalRetractionFibre π e W ≃ (terminalVectorRestriction π e (A := K ⧸ W)).ker where
  toFun f := ⟨f.1-f₀.1,by change terminalVectorRestriction π e (f.1-f₀.1)=0; rw [map_sub,f.2,f₀.2,sub_self]⟩
  invFun g := ⟨g.1+f₀.1,by rw [map_add,show terminalVectorRestriction π e g.1=0 from g.2,f₀.2,zero_add]⟩
  left_inv f := Subtype.ext (sub_add_cancel _ _)
  right_inv g := Subtype.ext (add_sub_cancel_right _ _)

/-- Every nonempty fixed-intersection subgroup fibre is an actual torsor
for Hom(Y,K/W), via its quotient-coefficient retractions. -/
def terminalLiftFibreHomEquiv (hπ : Function.Surjective π)
    (hcentral : π.ker ≤ Subgroup.center X) (W : Submodule (ZMod 2) K)
    (H₀ : TerminalLiftFibre π e W) :
    TerminalLiftFibre π e W ≃ (Additive Y →+ K ⧸ W) :=
  (terminalRetractionEquiv π e hπ hcentral W).symm.trans
    ((terminalRetractionTranslateEquiv π e W
      ((terminalRetractionEquiv π e hπ hcentral W).symm H₀)).trans
      (terminalZeroRestrictionEquiv π e hπ))

/-- The fixed-intersection central fibre has its exact original character
exponent. No desired cardinality or abstract torsor count is assumed. -/
theorem terminalLiftFibre_card (hπ : Function.Surjective π)
    (hcentral : π.ker ≤ Subgroup.center X) [Finite Y] [Finite K]
    (W : Submodule (ZMod 2) K)
    (hW : W.dualAnnihilator ≤ terminalSplittingAnnihilator π e) :
    Nat.card (TerminalLiftFibre π e W) =
      2^(binaryCharacterRank Y * Module.finrank (ZMod 2) (K ⧸ W)) := by
  letI : Finite (K ⧸ W) := Finite.of_surjective W.mkQ W.mkQ_surjective
  obtain ⟨H₀⟩ := (terminalLiftFibre_nonempty_iff π e hπ hcentral W).mpr hW
  rw [Nat.card_congr (terminalLiftFibreHomEquiv π e hπ hcentral W H₀)]
  exact binaryAbelianizationHom_card Y

/-- All binary kernel subgroups are actual linear subspaces in the fixed chart. -/
def terminalKernelSubmoduleOrderIso :
    Submodule (ZMod 2) K ≃o Subgroup (Multiplicative K) :=
  (AddSubgroup.toZModSubmodule 2).symm.trans AddSubgroup.toSubgroup

/-- Partition all actual full-image subgroups by their unique original
kernel intersection. Admissibility is the actual retained-annihilator test. -/
def terminalAllLiftFibreEquiv (hπ : Function.Surjective π)
    (hcentral : π.ker ≤ Subgroup.center X) [FiniteDimensional (ZMod 2) K] :
    (Σ W : {W : Submodule (ZMod 2) K //
      W.dualAnnihilator ≤ terminalSplittingAnnihilator π e}, TerminalLiftFibre π e W.1) ≃
      {H : Subgroup X // H.map π = ⊤} := by
  let f : (Σ W : {W : Submodule (ZMod 2) K //
      W.dualAnnihilator ≤ terminalSplittingAnnihilator π e}, TerminalLiftFibre π e W.1) →
      {H : Subgroup X // H.map π = ⊤} := fun W => ⟨W.2.1,W.2.2.1⟩
  refine Equiv.ofBijective f ⟨?_,?_⟩
  · rintro ⟨W,H⟩ ⟨W',H'⟩ h
    have hH : H.1 = H'.1 := congrArg Subtype.val h
    have hW : W = W' := by
      apply Subtype.ext
      apply (terminalKernelSubmoduleOrderIso (K := K)).injective
      change W.1.toAddSubgroup.toSubgroup = W'.1.toAddSubgroup.toSubgroup
      rw [← H.2.2,← H'.2.2,hH]
    subst W'
    have hh : H = H' := Subtype.ext hH
    subst H'
    rfl
  · intro H
    let W := (terminalKernelSubmoduleOrderIso (K := K)).symm
      (H.1.comap (terminalKernelInclusion π e))
    have hW : H.1.comap (terminalKernelInclusion π e) = W.toAddSubgroup.toSubgroup :=
      ((terminalKernelSubmoduleOrderIso (K := K)).apply_symm_apply _).symm
    have ha : W.dualAnnihilator ≤ terminalSplittingAnnihilator π e :=
      (terminalLiftFibre_nonempty_iff π e hπ hcentral W).mp ⟨⟨H.1,H.2,hW⟩⟩
    exact ⟨⟨⟨W,ha⟩,⟨H.1,H.2,hW⟩⟩,rfl⟩

/-- Annihilator duality retains the original scalar splitting subspace. -/
def terminalAnnihilatorEquiv [FiniteDimensional (ZMod 2) K]
    (S : Submodule (ZMod 2) (Module.Dual (ZMod 2) K)) :
    {W : Submodule (ZMod 2) K // W.dualAnnihilator ≤ S} ≃
      {L : Submodule (ZMod 2) (Module.Dual (ZMod 2) K) // L ≤ S} where
  toFun W := ⟨W.1.dualAnnihilator,W.2⟩
  invFun L := ⟨L.1.dualCoannihilator,by
    simpa only [Subspace.dualCoannihilator_dualAnnihilator_eq] using L.2⟩
  left_inv W := Subtype.ext Subspace.dualAnnihilator_dualCoannihilator_eq
  right_inv L := Subtype.ext Subspace.dualCoannihilator_dualAnnihilator_eq

section FiniteCounts

variable [Finite X] [Finite Y] [Finite K]
attribute [local instance] Fintype.ofFinite

/-- Exact all-lifts count with the original kernel intersections retained. -/
theorem terminal_all_lifts_count (hπ : Function.Surjective π)
    (hcentral : π.ker ≤ Subgroup.center X) :
    Nat.card {H : Subgroup X // H.map π = ⊤} =
      ∑ W : {W : Submodule (ZMod 2) K //
        W.dualAnnihilator ≤ terminalSplittingAnnihilator π e},
        2^(binaryCharacterRank Y * Module.finrank (ZMod 2) (K ⧸ W.1)) := by
  rw [← Nat.card_congr (terminalAllLiftFibreEquiv π e hπ hcentral),Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro W _
  exact terminalLiftFibre_card π e hπ hcentral W.1 W.2

/-- The central-extension fibre formula on the actual retained annihilator.
The complete (possibly nonabelian) quotient Y is preserved throughout. -/
theorem terminal_all_lifts_count_annihilator (hπ : Function.Surjective π)
    (hcentral : π.ker ≤ Subgroup.center X) :
    Nat.card {H : Subgroup X // H.map π = ⊤} =
      ∑ L : {L : Submodule (ZMod 2) (Module.Dual (ZMod 2) K) //
        L ≤ terminalSplittingAnnihilator π e},
        2^(binaryCharacterRank Y * Module.finrank (ZMod 2) L.1) := by
  rw [terminal_all_lifts_count π e hπ hcentral]
  apply Fintype.sum_equiv (terminalAnnihilatorEquiv (terminalSplittingAnnihilator π e))
  intro W
  rw [(Subspace.quotEquivAnnihilator W.1).finrank_eq]
  rfl

end FiniteCounts

end SymmetricSubgroupAsymptotics
