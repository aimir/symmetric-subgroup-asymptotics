import SymmetricSubgroupAsymptotics.MarkedC4ActualPhysicalTailRegrouping
import SymmetricSubgroupAsymptotics.MarkedC4ActualMarkedEpimorphismReserve

/-! Marked ordinary4.6 reserve for a SAME actual physical source and any
literal fully projecting tail. The R/P regrouping and all transports are
constructed, rather than supplied as a geometry/count callback. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualPhysicalEpiReserve
open ActualPhysicalTailRegrouping ActualNormalFMarkedPeel RDTNormalFInterface
open ActualGlobalMarkGeneratorRank ActualMarkedRDTSource
open ActualMarkZeroNormalRank

variable {t : ℕ} (F : Fin t → Type) [∀ i,Group (F i)] [∀ i,Finite (F i)]
  (S : Finset (Fin t)) (r : ℕ) (A : Subgroup ((∀ i,F i) × Marks r))

def tailHom : A →* ∀ j,P F S j where
  toFun a j := a.val.1 (rightLabel S j).val
  map_one' := rfl
  map_mul' _ _ := rfl

theorem rank_eq : genRank (ActualPhysicalTailRegrouping.Source F S (Marks r) A)=genRank A := by
  apply le_antisymm
  · exact genRank_le_of_surjective (ActualPhysicalTailRegrouping.sourceEquiv F S (Marks r) A).toMonoidHom
      (ActualPhysicalTailRegrouping.sourceEquiv F S (Marks r) A).surjective
  · exact genRank_le_of_surjective (ActualPhysicalTailRegrouping.sourceEquiv F S (Marks r) A).symm.toMonoidHom
      (ActualPhysicalTailRegrouping.sourceEquiv F S (Marks r) A).symm.surjective

theorem tail_inverse : (tailHom F S r A).comp
    (ActualPhysicalTailRegrouping.sourceEquiv F S (Marks r) A).symm.toMonoidHom=
      ActualMarkedRDTSource.tail (R F S) (P F S) r
        (ActualPhysicalTailRegrouping.Source F S (Marks r) A) := by
  apply MonoidHom.ext
  intro x
  obtain ⟨a,rfl⟩ := (ActualPhysicalTailRegrouping.sourceEquiv F S (Marks r) A).surjective x
  change tailHom F S r A ((ActualPhysicalTailRegrouping.sourceEquiv F S (Marks r) A).symm
    (ActualPhysicalTailRegrouping.sourceEquiv F S (Marks r) A a))=_
  rw [(ActualPhysicalTailRegrouping.sourceEquiv F S (Marks r) A).symm_apply_apply]
  rfl

theorem normal_budget (dN : ℕ)
    (hA : ∀ V : Subgroup A,V.Normal →V≤commutator A ⊓ (tailHom F S r A).ker →normalGen V≤dN) :
    ∀ U : Subgroup (ActualPhysicalTailRegrouping.Source F S (Marks r) A),U.Normal →
      U≤commutator (ActualPhysicalTailRegrouping.Source F S (Marks r) A) ⊓
        (ActualMarkedRDTSource.tail (R F S) (P F S) r
          (ActualPhysicalTailRegrouping.Source F S (Marks r) A)).ker →normalGen U≤dN := by
  intro U hUn hU
  letI : U.Normal := hUn
  let e := ActualPhysicalTailRegrouping.sourceEquiv F S (Marks r) A
  let q := e.symm.toMonoidHom
  have hq : Function.Surjective q := e.symm.surjective
  letI : (U.map q).Normal := Subgroup.Normal.map hUn q hq
  have hd : (commutator (ActualPhysicalTailRegrouping.Source F S (Marks r) A)).map q=commutator A := by
    rw [map_commutator_eq,q.range_eq_top_of_surjective hq]
    rfl
  have hV : U.map q≤commutator A ⊓ (tailHom F S r A).ker := by
    rintro a ⟨x,hx,rfl⟩
    constructor
    · rw [← hd]
      exact ⟨x,(hU hx).1,rfl⟩
    · have ht := (hU hx).2
      change (tailHom F S r A).comp q x=1
      rw [tail_inverse]
      exact ht
  have he : normalGen (U.map q)=normalGen U := by
    apply normalGen_map_eq q hq U
    intro x hx he
    apply e.symm.injective
    exact he.trans q.map_one.symm
  rw [← he]
  exact hA _ inferInstance hV

def epiEquiv (Q : Type) [Group Q] :
    {f : A →* Q // Function.Surjective f} ≃
      {f : ActualPhysicalTailRegrouping.Source F S (Marks r) A →* Q // Function.Surjective f} where
  toFun f := ⟨f.val.comp (ActualPhysicalTailRegrouping.sourceEquiv F S (Marks r) A).symm.toMonoidHom,
    f.property.comp (ActualPhysicalTailRegrouping.sourceEquiv F S (Marks r) A).symm.surjective⟩
  invFun f := ⟨f.val.comp (ActualPhysicalTailRegrouping.sourceEquiv F S (Marks r) A).toMonoidHom,
    f.property.comp (ActualPhysicalTailRegrouping.sourceEquiv F S (Marks r) A).surjective⟩
  left_inv f := by apply Subtype.ext; ext x; simp
  right_inv f := by apply Subtype.ext; ext x; simp

/-- All rank and normal-budget hypotheses refer to THIS actual source A.
The literal tail is split internally and the original marking stays once. -/
theorem actual_epi_le_reserve
    (lit : RDTTheorem46BinaryInput) (k : ℕ) (hk : 2≤k)
    (hbinary : ∀ i,IsPGroup 2 (F i)) (hcard : ∀ i,Nat.card (F i)≤2^k)
    (hfull : ∀ i,Function.Surjective (fun a : A => a.val.1 i))
    (htail : Function.Surjective (fun a : A => (fun i : RightLabels S => a.val.1 i.val)))
    (Q : Type) [Group Q] [Finite Q] [Nontrivial Q]
    (hQ : IsPGroup 2 Q) (hQcard : Nat.card Q≤2^k)
    (T : Subgroup Q) (hT : T.Normal) (dN : ℕ)
    (hnormal : ∀ U : Subgroup A,U.Normal →
      U≤commutator A ⊓ (tailHom F S r A).ker →normalGen U≤dN)
    {e b w b₃ b₄ : ℝ} (hb₃ : 0≤b₃) (hb₄ : 0≤b₄) (hwidth : b₃+b₄=b-w)
    (hexcess : commutatorLog T+e*centralLog T≤w/2) (hzcap : centralLog T≤w/4)
    (hsource : (genRank A : ℝ)≤e*b₃/4+b₄/2+r) (hncap : (dN : ℝ)≤b₃/4) :
    (Nat.card {f : A →* Q // Function.Surjective f} : ℝ)≤
      kappa3 lit k*(genRank A : ℝ)^kappa4 lit k*
        (2 : ℝ)^(markedF b r-markedF (b-w) r) := by
  have hs : (genRank (ActualPhysicalTailRegrouping.Source F S (Marks r) A) : ℝ)≤e*b₃/4+b₄/2+r := by
    rw [rank_eq]
    exact hsource
  have hbound := ActualMarkedEpimorphismReserve.actual_epi_le_reserve lit k _ _ hk
    (R F S) (P F S) (fun j => hbinary (leftLabel S j).val)
    (fun j => hbinary (rightLabel S j).val) (fun j => hcard (leftLabel S j).val)
    (fun j => hcard (rightLabel S j).val) r
    (ActualPhysicalTailRegrouping.Source F S (Marks r) A)
    (full_left F S (Marks r) A hfull) (full_right F S (Marks r) A htail)
    Q hQ hQcard T hT dN (normal_budget F S r A dN hnormal)
    hb₃ hb₄ hwidth hexcess hzcap hs hncap
  rw [rank_eq] at hbound
  rw [Nat.card_congr (epiEquiv F S r A Q)]
  exact hbound

end SymmetricSubgroupAsymptotics.MarkedC4.ActualPhysicalEpiReserve
