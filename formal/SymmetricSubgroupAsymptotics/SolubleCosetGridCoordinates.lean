import SymmetricSubgroupAsymptotics.SolubleOrderedCosetTransversal
import SymmetricSubgroupAsymptotics.PrimeCosetGridCoordinates

/-! Numeric row labels preserve the actual mixed-prime grid's lexicographic
order. Reindexing changes no original representative, subgroup or twist. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
open CoinducedLeadingCoordinates

def SolubleCosetShape.degree : SolubleCosetShape → ℕ
  | .unit => 1
  | .step s p r => s.degree*p^r

def SolubleCosetShape.code : (s : SolubleCosetShape) → s.Carrier ≃ Fin s.degree
  | .unit => primeCosetGridCode 2 0
  | .step s p r => ((Equiv.prodCongr s.code (primeCosetGridCode p r)).trans finProdFinEquiv)

private theorem row_label_lt_iff {m n : ℕ} (a b : Fin m) (i j : Fin n) :
    label a i<label b j ↔ a<b ∨ a=b ∧ i<j := by
  constructor
  · exact label_lt_cases
  · rintro (hab|⟨rfl,hij⟩)
    · exact label_row_lt hab i j
    · exact label_fibre_lt a hij

theorem SolubleCosetShape.code_lt_iff (s : SolubleCosetShape) (a b : s.Carrier) :
    s.code a<s.code b ↔ s.LT a b := by
  induction s with
  | unit =>
    change (0 : ℕ)<0 ↔ False
    simp
  | step s p r ih =>
    change label (s.code a.1) (primeCosetGridCode p r a.2)<
      label (s.code b.1) (primeCosetGridCode p r b.2) ↔
        s.LT a.1 b.1 ∨ a.1=b.1 ∧ primeCosetGridLT p r a.2 b.2
    rw [row_label_lt_iff,ih,primeCosetGridCode_lt_iff]
    simp only [Equiv.apply_eq_iff_eq]

theorem SolubleCosetShape.comparable_refl (s : SolubleCosetShape) :
    ∀ a : s.Carrier, s.Comparable a a := by
  induction s with
  | unit => intro a; trivial
  | step s p r ih =>
    intro a
    exact ⟨ih a.1,(primeCosetGridTuple_le_iff p r a.2 a.2).mp le_rfl⟩

def SolubleCosetShape.finComparable (s : SolubleCosetShape)
    (a b : Fin s.degree) : Prop := s.Comparable (s.code.symm a) (s.code.symm b)

def SolubleOrderedCosetChart.finRows
    {G : Type} [Group G] {H : Subgroup G} (D : SolubleOrderedCosetChart H) :
    OrderedCosetData H ⊤ (Fin D.shape.degree) (· < ·) D.shape.finComparable where
  le := D.data.le
  repr := fun a => D.data.repr (D.shape.code.symm a)
  mem := fun a => D.data.mem _
  factor := by
    intro y hy
    obtain ⟨h,hh,a,ha⟩ := D.data.factor y hy
    exact ⟨h,hh,D.shape.code a,by simpa only [Equiv.symm_apply_apply] using ha⟩
  unique := by
    intro a b hab
    apply D.shape.code.symm.injective
    exact D.data.unique _ _ hab
  triangular := by
    intro a b c hab hbc
    have hab' : D.shape.LT (D.shape.code.symm a) (D.shape.code.symm b) :=
      (D.shape.code_lt_iff _ _).mp (by simpa only [Equiv.apply_symm_apply] using hab)
    obtain ⟨h,hh,e,hec,he⟩ := D.data.triangular _ _ _ hab' hbc
    refine ⟨h,hh,D.shape.code e,?_,?_⟩
    · simpa only [Equiv.apply_symm_apply] using (D.shape.code_lt_iff _ _).mpr hec
    · simpa only [Equiv.symm_apply_apply] using he

end SymmetricSubgroupAsymptotics
