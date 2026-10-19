import SymmetricSubgroupAsymptotics.MarkedC4ActualNormalFMarkedPeel
import SymmetricSubgroupAsymptotics.MarkedC4ActualIsolatedFreeEpimorphism

/-! One literal Case-II subgroup fibre is counted using the arbitrary F
selected by RDT5.7 and the exact ordinary RDT4.6 interface. The residual
group is the actual group, including its single global marking group. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualNormalFFibrePeel
open RDTNormalFInterface ActualNormalFMarkedPeel

theorem fibre_le_reserve
    (lit : RDTTheorem46BinaryInput) (k s u : ℕ)
    (R : Fin s → Type) [∀ i,Group (R i)] [∀ i,Finite (R i)]
    (P : Fin u → Type) [∀ j,Group (P j)] [∀ j,Finite (P j)]
    (hR : ∀ i,IsPGroup 2 (R i)) (hP : ∀ j,IsPGroup 2 (P j))
    (hRcard : ∀ i,Nat.card (R i)≤2^k) (hPcard : ∀ j,Nat.card (P j)≤2^k)
    (L : Subgroup (∀ i,R i))
    (hL : ∀ i,Function.Surjective ((Pi.evalMonoidHom R i).comp L.subtype))
    (G : Subgroup (L × (∀ j,P j)))
    (hG : Function.Surjective ((MonoidHom.snd L (∀ j,P j)).comp G.subtype))
    (Q : Type) [Group Q] [Finite Q] [Nontrivial Q]
    (hQ : IsPGroup 2 Q) (hQcard : Nat.card Q≤2^k)
    (F : Subgroup Q) (hF : F.Normal) (dN : ℕ)
    (hnormal : ∀ U : Subgroup G,U.Normal →
      U≤commutator G ⊓ ((MonoidHom.snd L (∀ j,P j)).comp G.subtype).ker →normalGen U≤dN)
    {e b w b₃ b₄ r : ℝ}
    (hb₃ : 0≤b₃) (hb₄ : 0≤b₄) (hr : 0≤r) (hwidth : b₃+b₄=b-w)
    (hexcess : commutatorLog F+e*centralLog F≤w/2)
    (hzcap : centralLog F≤w/4)
    (hsource : (genRank G : ℝ)≤e*b₃/4+b₄/2+r)
    (hncap : (dN : ℝ)≤b₃/4) :
    (Nat.card (ActualIsolatedFreeEpimorphism.Family Q G) : ℝ)≤
      kappa3 lit k*(genRank G : ℝ)^kappa4 lit k*
        (2 : ℝ)^(markedF b r-markedF (b-w) r) := by
  have hactual : (Nat.card (ActualIsolatedFreeEpimorphism.Family Q G) : ℝ)≤
      Nat.card {f : G →* Q // Function.Surjective f} := by
    exact_mod_cast ActualIsolatedFreeEpimorphism.card_le Q G
  exact hactual.trans (epimorphism_le_reserve lit k s u R P hR hP hRcard hPcard
    L hL G hG Q hQ hQcard F hF dN hnormal hb₃ hb₄ hr hwidth hexcess hzcap hsource hncap)

end SymmetricSubgroupAsymptotics.MarkedC4.ActualNormalFFibrePeel
