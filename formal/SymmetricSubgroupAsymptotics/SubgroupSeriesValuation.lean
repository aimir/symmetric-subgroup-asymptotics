import SymmetricSubgroupAsymptotics.ChiefTernaryWeights

/-! Exact relative-index valuations along original subgroup series.
These lemmas use actual group indices and their multiplicativity. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
variable {R:Type} [Group R] [Finite R]

theorem relativeIndex_ternary_add (B C D:Subgroup R) (hBC:B≤C) (hCD:C≤D) :
    (B.relIndex D).factorization 3=
      (B.relIndex C).factorization 3+(C.relIndex D).factorization 3 := by
  rw [←Subgroup.relIndex_mul_relIndex B C D hBC hCD,
    Nat.factorization_mul (show B.relIndex C≠0 from Subgroup.index_ne_zero_of_finite)
      (show C.relIndex D≠0 from Subgroup.index_ne_zero_of_finite)]
  rfl

theorem subgroupSeries_ternary_valuation_le_length :
    ∀ (n:ℕ) (f:Fin (n+1)→Subgroup R),Monotone f →
      (∀i:Fin n,((f i.castSucc).relIndex (f i.succ)).factorization 3≤1) →
      ((f 0).relIndex (f (Fin.last n))).factorization 3≤n := by
  intro n
  induction n with
  | zero =>
    intro f _ _
    simp
  | succ n ih =>
    intro f hf he
    let g : Fin (n+1)→Subgroup R := fun i=>f i.castSucc
    have hg : Monotone g := fun i j h=>hf h
    have hge (i:Fin n) : ((g i.castSucc).relIndex (g i.succ)).factorization 3≤1 :=
      he i.castSucc
    have hprefix := ih g hg hge
    have hlast := he (Fin.last n)
    have hle : f 0≤f (Fin.last n).castSucc := hf (Fin.zero_le _)
    have hle' : f (Fin.last n).castSucc≤f (Fin.last (n+1)) := hf (Fin.le_last _)
    have h := relativeIndex_ternary_add (f 0) (f (Fin.last n).castSucc)
      (f (Fin.last (n+1))) hle hle'
    change ((f 0).relIndex (f (Fin.last n).castSucc)).factorization 3≤n at hprefix
    change ((f (Fin.last n).castSucc).relIndex (f (Fin.last (n+1)))).factorization 3≤1 at hlast
    omega

end SymmetricSubgroupAsymptotics
