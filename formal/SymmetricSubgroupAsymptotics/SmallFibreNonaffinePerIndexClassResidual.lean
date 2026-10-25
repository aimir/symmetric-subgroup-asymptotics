import SymmetricSubgroupAsymptotics.SmallFibreNonaffineClassPacketResidual
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawChart
import SymmetricSubgroupAsymptotics.NonabelianSimpleProperIndex

/-! Select the actual least proper index from a proved per-index class
budget. The subgroup realizing that index and its square bound belong
to the SAME original simple factor. The returned short-index subgroup
also remains in that factor; no model labels or degree recognition are
introduced by this adapter. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SmallFibreNonaffinePerIndexClassResidual
open PrimitiveSocleRawStructure OriginalBlockClassBound

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]

theorem subnormal_gap_or_least_short_index
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω), π (g • ω)=g • π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x, Nat.card (originalBlockFibre π x)=c)
    (E : NonaffineData (Top (A := A) (X := X)) X)
    (hbudget : ∀ K : Subgroup E.Simple, K ≠ ⊤ →
      (Nat.card (ConjClasses E.Simple)*Nat.card (Outer E.Simple))^3 ≤ 5^(K.index+1))
    (hsquare : ∀ ell : ℕ, LeastProperIndex E.Simple ell → ell^2 < Nat.card E.Simple)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-2) ∨
      (E.factorCount=1 ∧ ∃ ell : ℕ, LeastProperIndex E.Simple ell ∧
        ∃ K : Subgroup E.Simple, K ≠ ⊤ ∧ Nat.card X=K.index ∧
          ell ≤ K.index ∧ K.index < 2*ell+2) := by
  obtain ⟨ell,hell⟩ := exists_leastProperIndex E.Simple
  have hb : 5 ≤ ell := nonabelianSimple_leastProperIndex_five_le
    (fun h => E.noncommutative (isMulCommutative_iff.mpr h)) hell.1
  obtain ⟨K₀,hK₀,hindex₀⟩ := hell.1
  have hbase : (Nat.card (ConjClasses E.Simple)*Nat.card (Outer E.Simple))^3 ≤
      5^(ell+1) := by
    have h := hbudget K₀ hK₀
    simpa only [hindex₀] using h
  rcases SmallFibreNonaffineClassPacketResidual.subnormal_gap_or_single_short_index
      π hπ c hc hsize E ell hb hell.2 (hsquare ell hell).le hbase H hH with
      hgap | ⟨hk,K,hK,hdegree,hlo,hhi⟩
  · exact Or.inl hgap
  · exact Or.inr ⟨hk,ell,hell,K,hK,hdegree,hlo,hhi⟩

end SymmetricSubgroupAsymptotics.SmallFibreNonaffinePerIndexClassResidual
