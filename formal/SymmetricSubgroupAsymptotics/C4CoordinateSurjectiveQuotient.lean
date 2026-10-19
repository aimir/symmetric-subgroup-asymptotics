import SymmetricSubgroupAsymptotics.FiniteAbelianExponentFourCoordinates

/-! An actual quotient of a subgroup of c cyclic-four coordinates embeds
in at most c cyclic-four coordinates. The original surjection is unchanged;
no splitting of the subgroup or its quotient is required. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.C4CoordinateSurjectiveQuotient
open C4SquareKernelCoordinates
variable {Z A : Type} [Group Z] [Group A] [Finite Z] [Finite A] {c : ℕ}

theorem exists_embedding (e : Z →* (Fin c → C4))
    (he : Function.Injective e) (q : Z →* A) (hq : Function.Surjective q) :
    ∃ r : ℕ, r≤c ∧ ∃ j : A →* (Fin r → C4), Function.Injective j := by
  letI : CommGroup Z :=
    { ‹Group Z› with mul_comm := fun x y => he (by rw [map_mul,map_mul,mul_comm]) }
  letI : CommGroup A :=
    { ‹Group A› with
      mul_comm := by
        intro x y
        obtain ⟨a,rfl⟩ := hq x
        obtain ⟨b,rfl⟩ := hq y
        rw [←map_mul,←map_mul,mul_comm] }
  have hz4 (z : Z) : z^4=1 := by
    apply he
    rw [map_pow,map_one]
    funext i
    change (e z i)^4=1
    have hfour : ∀ x : C4, x^4=1 := by decide +kernel
    exact hfour _
  have ha4 (a : A) : a^4=1 := by
    obtain ⟨z,rfl⟩ := hq a
    rw [←map_pow,hz4,map_one]
  obtain ⟨r,hr,j,hj⟩ := FiniteAbelianExponentFourCoordinates.exists_coordinates A ha4
  have hbound : 2^r≤2^c := by
    rw [←hr]
    exact (FiniteAbelianSquareKernelQuotient.card_square_kernel_le q hq).trans
      (C4SquareKernelCoordinates.square_kernel_card_le e he)
  exact ⟨r,(Nat.pow_le_pow_iff_right (by decide : 1<2)).mp hbound,j,hj⟩

end SymmetricSubgroupAsymptotics.C4CoordinateSurjectiveQuotient
