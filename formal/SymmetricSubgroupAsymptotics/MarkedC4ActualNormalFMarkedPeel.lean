import SymmetricSubgroupAsymptotics.MarkedC4RDTNormalFInterface
import SymmetricSubgroupAsymptotics.MarkedC4CaseIIPeel
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! Arbitrary-normal-F epimorphism adapter for the marked Case-II peel.
Constants are selected ONCE from the exact unmarked RDT4.6 hypothesis, using
only the fixed factor-order cutoff. All ranks and target invariants below
refer to the actual source and the actual F selected by Theorem 5.7. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualNormalFMarkedPeel
open RDTNormalFInterface

def kappa3 (lit : RDTTheorem46BinaryInput) (k : ℕ) : ℝ := Classical.choose (lit k)
def kappa4 (lit : RDTTheorem46BinaryInput) (k : ℕ) : ℝ :=
  Classical.choose (Classical.choose_spec (lit k))
theorem kappa3_pos (lit : RDTTheorem46BinaryInput) (k : ℕ) : 0<kappa3 lit k :=
  (Classical.choose_spec (Classical.choose_spec (lit k))).1
theorem kappa4_nonneg (lit : RDTTheorem46BinaryInput) (k : ℕ) : 0≤kappa4 lit k :=
  (Classical.choose_spec (Classical.choose_spec (lit k))).2.1

def centralLog {Q : Type} [Group Q] [Finite Q] (F : Subgroup Q) : ℝ :=
  Real.logb 2 (Nat.card (targetCentralizer F))
def commutatorLog {Q : Type} [Group Q] [Finite Q] (F : Subgroup Q) : ℝ :=
  Real.logb 2 (Nat.card (targetCommutator F))

private theorem card_power_eq_two_log {V : Type} [Group V] [Finite V] (d : ℕ) :
    (Nat.card V : ℝ)^d=(2 : ℝ)^(Real.logb 2 (Nat.card V)*(d : ℝ)) := by
  rw [Real.rpow_mul_natCast (by norm_num : (0 : ℝ)≤2),
    Real.rpow_logb (by norm_num : (0 : ℝ)<2) (by norm_num : (2 : ℝ)≠1)
      (show (0 : ℝ)<Nat.card V by exact_mod_cast Nat.card_pos)]

/-- The actual source and target retain the exact RDT4.6 geometry. Neither
F=Q nor centre/full-commutator bounds are required or inferred. -/
theorem epimorphism_le_reserve
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
    (Nat.card {f : G →* Q // Function.Surjective f} : ℝ)≤
      kappa3 lit k*(genRank G : ℝ)^kappa4 lit k*
        (2 : ℝ)^(markedF b r-markedF (b-w) r) := by
  have hraw := (Classical.choose_spec (Classical.choose_spec (lit k))).2.2
    s u R P hR hP hRcard hPcard L hL G hG Q hQ hQcard F hF dN hnormal
  change (Nat.card {f : G →* Q // Function.Surjective f} : ℝ)≤
    kappa3 lit k*(genRank G : ℝ)^kappa4 lit k*
      (Nat.card (targetCentralizer F) : ℝ)^genRank G*
      (Nat.card (targetCommutator F) : ℝ)^dN at hraw
  have hz0 : 0≤centralLog F := by
    apply Real.logb_nonneg (by norm_num : (1 : ℝ)<2)
    exact_mod_cast (Nat.succ_le_iff.mpr (Nat.card_pos (α := targetCentralizer F)))
  have hg0 : 0≤commutatorLog F := by
    apply Real.logb_nonneg (by norm_num : (1 : ℝ)<2)
    exact_mod_cast (Nat.succ_le_iff.mpr (Nat.card_pos (α := targetCommutator F)))
  have hcost := caseII_epimorphism_cost_le_markedF_reserve hz0 hg0 hb₃ hb₄ hr
    hwidth (by linarith) hzcap hsource hncap
  rw [card_power_eq_two_log,card_power_eq_two_log] at hraw
  have hrewrite :
      kappa3 lit k*(genRank G : ℝ)^kappa4 lit k*
        (2 : ℝ)^(centralLog F*(genRank G : ℝ))*
        (2 : ℝ)^(commutatorLog F*(dN : ℝ))=
      (kappa3 lit k*(genRank G : ℝ)^kappa4 lit k)*
        (2 : ℝ)^(centralLog F*(genRank G : ℝ)+commutatorLog F*(dN : ℝ)) := by
    rw [mul_assoc,← Real.rpow_add (by norm_num : (0 : ℝ)<2)]
  change (Nat.card {f : G →* Q // Function.Surjective f} : ℝ)≤
      kappa3 lit k*(genRank G : ℝ)^kappa4 lit k*
        (2 : ℝ)^(centralLog F*(genRank G : ℝ))*
        (2 : ℝ)^(commutatorLog F*(dN : ℝ)) at hraw
  rw [hrewrite] at hraw
  apply hraw.trans
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (le_of_lt (kappa3_pos lit k)) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ)≤2) hcost

end SymmetricSubgroupAsymptotics.MarkedC4.ActualNormalFMarkedPeel
