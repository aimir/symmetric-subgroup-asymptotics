import SymmetricSubgroupAsymptotics.SmallFibreScaledClassPacketGap
import SymmetricSubgroupAsymptotics.ReeFFourFieldEightSmallFibreClassNumerics
import SymmetricSubgroupAsymptotics.CFSGReeFFourFieldEightProperIndexBand
import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalOuterBound
import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalIndexSquare
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport

/-! The original q8 small-fibre action pays the strong class cube gap
unless its SAME original simple factor has one factor and an actual
point-stabilizer K of index109..119. All other factor/degree forms are
paid by the original per-index wrapper. No exact Ree order is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SmallFibreReeFFourFieldEightClassResidual
open PrimitiveSocleRawStructure OriginalBlockClassBound CFSGReduction

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]

theorem subnormal_gap_or_same_short_index
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω), π (g • ω)=g • π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x, Nat.card (originalBlockFibre π x)=c)
    (E : NonaffineData (Top (A:=A) (X:=X)) X)
    (e : E.Simple ≃* CFSG.Models.ReeF4 1)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-2) ∨
      (E.factorCount=1 ∧ ∃ K : Subgroup E.Simple, K≠⊤ ∧
        Nat.card X=K.index ∧ 109≤K.index ∧ K.index<120) := by
  letI : IsSimpleGroup (CFSG.Models.ReeF4 1) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.ReeF4 1) := Finite.of_equiv E.Simple e.toEquiv
  let B := Nat.card (ConjClasses E.Simple)*Nat.card (Outer E.Simple)
  have hraw : B ≤ 8^26*3 := by
    have hclass : Nat.card (ConjClasses E.Simple) ≤ Nat.card E.Simple :=
      Nat.card_le_card_of_surjective ConjClasses.mk ConjClasses.mk_surjective
    calc
      B ≤ Nat.card E.Simple*Nat.card (Outer E.Simple) := Nat.mul_le_mul_right _ hclass
      _ ≤ 8^26*3 := by
        rw [Nat.card_congr e.toEquiv,outer_card_congr e]
        exact Nat.mul_le_mul
          (CFSGReeFFourWeightedFixedOrderUpper.original_ree_order_le 1)
          (CFSGReeFFourOriginalOuterBound.outer_card_le 1 (by omega))
  have hmap (K : Subgroup E.Simple) (hK : K≠⊤) : K.map e.toMonoidHom≠⊤ := by
    intro ht
    apply hK
    apply Subgroup.map_injective (f:=e.toMonoidHom) e.injective
    exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
  have hbudget (K : Subgroup E.Simple) (hK : K≠⊤) : B^3≤5^(K.index+1) := by
    have hi := CFSGReeFFourFieldEightPrimeIndex.proper_index_le
      (K.map e.toMonoidHom) (hmap K hK)
    have heq : (K.map e.toMonoidHom).index=K.index := K.index_map_equiv e
    rw [heq] at hi
    exact (Nat.pow_le_pow_left hraw 3).trans
      (ReeFFourFieldEightSmallFibreClassNumerics.component_cube_le_five_power K.index hi)
  have hsquare (ell : ℕ) (hell : LeastProperIndex E.Simple ell) :
      ell^2<Nat.card E.Simple := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSGReeFFourOriginalIndexSquare.original_index_square 1 (by omega) ell
      (leastProperIndex_of_mulEquiv e ell hell)
  rcases SmallFibreNonaffinePerIndexClassResidual.subnormal_gap_or_least_short_index
      π hπ c hc hsize E hbudget hsquare H hH with
      hgap | ⟨hk,ell,hell,K,hK,hdegree,hlo,hhi⟩
  · exact Or.inl hgap
  · have hband := CFSGReeFFourFieldEightProperIndexBand.proper_index_short_band_or_large
      (K.map e.toMonoidHom) (hmap K hK)
    have heq : (K.map e.toMonoidHom).index=K.index := K.index_map_equiv e
    rw [heq] at hband
    rcases hband with hshort | hlarge
    · exact Or.inr ⟨hk,K,hK,hdegree,hshort⟩
    · have hn : 218≤Nat.card X := by rw [hdegree]; exact hlarge
      have hscaled : 25*B^3≤3^Nat.card X :=
        (Nat.mul_le_mul_left 25 (Nat.pow_le_pow_left hraw 3)).trans
          (ReeFFourFieldEightSmallFibreClassNumerics.scaled_component_cube_le_three_power
            (Nat.card X) hn)
      have htop : ∀ L : Subgroup (Top (A:=A) (X:=X)), L.IsSubnormal →
          Nat.card (ConjClasses L)≤B := by
        intro L hL
        simpa only [hk,pow_one,Nat.factorial_one,mul_one] using
          E.subnormal_class_card_le_outer_wreath L hL
      have hlocal : ∀ x (L : Subgroup (Equiv.Perm (originalBlockFibre π x))),
          Nat.card (ConjClasses L)≤c := by
        rcases hc with rfl | rfl
        · exact fun x L => SmallPermutationClassBudgets.subgroup_class_card_le_two (hsize x).le L
        · exact fun x L => SmallPermutationClassBudgets.subgroup_class_card_le_three (hsize x).le L
      have hbound := SubnormalSmallFibreTopClassBound.subnormal_class_card_le_power_mul_top_budget
        π hπ c hlocal B htop H hH
      have hnum : (c^Nat.card X*B)^3≤5^(c*Nat.card X-2) := by
        rcases hc with rfl | rfl
        · exact SmallFibreScaledClassEnvelopeNumerics.binary_gap_of_scaled_cube
            (Nat.card X) B (by omega) hscaled
        · exact SmallFibreScaledClassEnvelopeNumerics.ternary_gap_of_scaled_cube
            (Nat.card X) B (by omega) hscaled
      have hcard := GaronziMarotiLargeBlockReduction.card_eq_blocks_mul_fibre π c hsize
      have h := (Nat.pow_le_pow_left hbound 3).trans hnum
      exact Or.inl (by simpa only [hcard,Nat.mul_comm (Nat.card X) c] using h)

end SymmetricSubgroupAsymptotics.SmallFibreReeFFourFieldEightClassResidual
