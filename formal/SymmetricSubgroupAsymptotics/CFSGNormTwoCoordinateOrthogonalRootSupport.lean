import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateBase
import SymmetricSubgroupAsymptotics.CFSGNormTwoPairingBounds

/-! A positive norm-two root supported on pairwise orthogonal simple
coordinates is itself one of those simple roots. This is a lattice
argument, with no root census or coefficient-field restriction. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOrthogonalRootSupport
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoPairingBounds
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)

include hs hp in
theorem positive_root_supported_on_orthogonal_simples (S : Set (Fin r))
    (horth : ∀i∈S,∀j∈S,i≠j→A j i=0)
    (k : Roots A) (hpos : ∀i,0≤k.val i) (hsupport : ∀i,i∉S→k.val i=0) :
    ∃i∈S,k=coordinateRoot A hd i := by
  have hk0 : k.val≠0 := by
    intro hz
    have hn := k.property
    rw [hz] at hn
    norm_num at hn
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hk0
  change k.val i≠0 at hi
  have his : i∈S := by
    by_contra hn
    exact hi (hsupport i hn)
  have hki : 1≤k.val i := by have hnonneg:=hpos i;omega
  have hpair : integerPairing A k.val (coordinateRoot A hd i).val=2*k.val i := by
    change integerPairing A k.val (Pi.single i (1:ℤ) : Fin r→ℤ)=_
    simp only [integerPairing,Matrix.toBilin'_apply',Matrix.mulVec_single_one,
      dotProduct,Matrix.col_apply]
    calc
      (∑j,k.val j*A j i)=k.val i*A i i := by
        apply Finset.sum_eq_single i
        · intro j _ hji
          by_cases hjs : j∈S
          · rw [horth i his j hjs (Ne.symm hji),mul_zero]
          · rw [hsupport j hjs,zero_mul]
        · intro hn
          exact False.elim (hn (Finset.mem_univ i))
      _=2*k.val i := by rw [hd];ring
  have hb := (root_pairing_bounds A hs hp k (coordinateRoot A hd i)).2
  have heq : integerPairing A k.val (coordinateRoot A hd i).val=2 := by
    rw [hpair] at hb
    rw [hpair]
    omega
  exact ⟨i,his,(root_pairing_eq_two_iff A hs hp k (coordinateRoot A hd i)).mp heq⟩

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOrthogonalRootSupport
