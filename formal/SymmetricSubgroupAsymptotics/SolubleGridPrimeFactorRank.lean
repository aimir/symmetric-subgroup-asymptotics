import SymmetricSubgroupAsymptotics.SolubleGridMiddleBound
import SymmetricSubgroupAsymptotics.TraceyExceptionalSolubleNumerics

/-! The actual mixed-prime coset-grid rank is exactly K of its actual
original degree, including repeated primes and rank-zero steps. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

theorem SolubleCosetShape.degree_pos (s : SolubleCosetShape) (hp : s.Primes) : 0<s.degree := by
  induction s with
  | unit => exact Nat.zero_lt_one
  | step s p r ih => exact mul_pos (ih hp.1) (pow_pos hp.2.pos r)

private theorem primePowerK (p r : ℕ) (hp : p.Prime) : traceyBinaryK (p^r)=r*(p-1) := by
  simp [traceyBinaryK,hp.factorization_pow]

theorem SolubleCosetShape.maxRank_eq_K (s : SolubleCosetShape) (hp : s.Primes) :
    s.maxRank=traceyBinaryK s.degree := by
  induction s with
  | unit => simp [SolubleCosetShape.maxRank,SolubleCosetShape.degree,traceyBinaryK]
  | step s p r ih =>
    rw [SolubleCosetShape.degree,traceyBinaryK_mul (s.degree_pos hp.1).ne'
      (pow_ne_zero _ hp.2.ne_zero),primePowerK p r hp.2,←ih hp.1]
    rfl

theorem SolubleOrderedCosetChart.degree_eq_index
    {G : Type} [Group G] {H : Subgroup G} (D : SolubleOrderedCosetChart H) :
    D.shape.degree=H.index := by
  calc
    D.shape.degree=Nat.card D.shape.Carrier := by
      have h := Nat.card_congr D.shape.code
      simpa only [Nat.card_fin] using h.symm
    _ = Nat.card (G⧸H) := Nat.card_congr
      (Equiv.ofBijective (fun a => (((D.data.repr a)⁻¹ : G) : G⧸H)) D.data.quotient_bijective)
    _ = H.index := rfl

end SymmetricSubgroupAsymptotics
