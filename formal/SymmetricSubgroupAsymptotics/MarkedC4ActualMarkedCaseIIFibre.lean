import SymmetricSubgroupAsymptotics.MarkedC4ActualMarkedRDTTransport
import SymmetricSubgroupAsymptotics.MarkedC4ActualNormalFFibrePeel

/-! Actual arbitrary-F Case-II marked fibre count. The RDT4.6 source
geometry is CONSTRUCTED from the same A with one global marking group. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualMarkedCaseIIFibre
open ActualGlobalMarkGeneratorRank ActualMarkedRDTSource ActualMarkedRDTTransport
open RDTNormalFInterface ActualNormalFMarkedPeel

theorem actual_fibre_le_reserve
    (lit : RDTTheorem46BinaryInput) (k s u : ℕ) (hk : 2≤k)
    (R : Fin s → Type) [∀ i,Group (R i)] [∀ i,Finite (R i)]
    (P : Fin u → Type) [∀ j,Group (P j)] [∀ j,Finite (P j)]
    (hR : ∀ i,IsPGroup 2 (R i)) (hP : ∀ j,IsPGroup 2 (P j))
    (hRcard : ∀ i,Nat.card (R i)≤2^k) (hPcard : ∀ j,Nat.card (P j)≤2^k)
    (r : ℕ) (A : Subgroup (((∀ i,R i) × (∀ j,P j)) × Marks r))
    (hfullR : ∀ i,Function.Surjective (physicalFactor R P r A i))
    (hfullP : Function.Surjective (tail R P r A))
    (Q : Type) [Group Q] [Finite Q] [Nontrivial Q]
    (hQ : IsPGroup 2 Q) (hQcard : Nat.card Q≤2^k)
    (F : Subgroup Q) (hF : F.Normal) (dN : ℕ)
    (hnormal : ∀ U : Subgroup A,U.Normal →
      U≤commutator A ⊓ (tail R P r A).ker →normalGen U≤dN)
    {e b w b₃ b₄ : ℝ}
    (hb₃ : 0≤b₃) (hb₄ : 0≤b₄) (hwidth : b₃+b₄=b-w)
    (hexcess : commutatorLog F+e*centralLog F≤w/2)
    (hzcap : centralLog F≤w/4)
    (hsource : (genRank A : ℝ)≤e*b₃/4+b₄/2+r)
    (hncap : (dN : ℝ)≤b₃/4) :
    (Nat.card (ActualIsolatedFreeEpimorphism.Family Q A) : ℝ)≤
      kappa3 lit k*(genRank A : ℝ)^kappa4 lit k*
        (2 : ℝ)^(markedF b r-markedF (b-w) r) := by
  have hsrc : (genRank (Source R P r A) : ℝ)≤e*b₃/4+b₄/2+r := by
    rw [genRank_eq]
    exact hsource
  have hraw := epimorphism_le_reserve lit k (s+r) u (Factors R P r A) P
    (factors_binary R P r A hR) hP (factors_card_le R P r A k hk hRcard) hPcard
    (Left R P r A) (left_subdirect R P r A hfullR)
    (Source R P r A) (source_tail_surjective R P r A hfullP)
    Q hQ hQcard F hF dN (normal_budget R P r A dN hnormal)
    hb₃ hb₄ (Nat.cast_nonneg r) hwidth hexcess hzcap hsrc hncap
  rw [genRank_eq] at hraw
  have hepi : Nat.card {f : A →* Q // Function.Surjective f}=
      Nat.card {f : Source R P r A →* Q // Function.Surjective f} :=
    Nat.card_congr (epiEquiv R P r A Q)
  have hactual : (Nat.card (ActualIsolatedFreeEpimorphism.Family Q A) : ℝ)≤
      Nat.card {f : A →* Q // Function.Surjective f} := by
    exact_mod_cast ActualIsolatedFreeEpimorphism.card_le Q A
  rw [hepi] at hactual
  exact hactual.trans hraw

end SymmetricSubgroupAsymptotics.MarkedC4.ActualMarkedCaseIIFibre
