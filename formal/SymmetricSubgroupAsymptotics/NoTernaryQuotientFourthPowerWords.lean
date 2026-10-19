import SymmetricSubgroupAsymptotics.DerivedGeneratorWords
import SymmetricSubgroupAsymptotics.BinaryBySymmetricThree
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.NoTernaryQuotientFourthPowerWords

theorem of_generators {G I : Type} [Group G] [Finite G]
    (gs : I → G) (hgen : Subgroup.closure (Set.range gs)=⊤)
    (words : I → DerivedGeneratorWord I)
    (hw : ∀ i,gs i^4=(words i).eval gs) : NoTernaryQuotient G := by
  intro N _ hcard
  have hQcard : Nat.card (G ⧸ N)=3 := hcard
  let q := QuotientGroup.mk' N
  letI : IsMulCommutative (G ⧸ N) := (isCyclic_of_prime_card (p := 3) hcard).isMulCommutative
  have hder : commutator G≤N :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance
  have hgi (i : I) : q (gs i)=1 := by
    have h4 : q (gs i)^4=1 := by
      rw [← map_pow,hw i]
      exact (QuotientGroup.eq_one_iff (N := N) _).mpr (hder ((words i).eval_mem_commutator gs))
    have h3 : q (gs i)^3=1 := by
      simpa only [hQcard] using (pow_card_eq_one' (x := q (gs i)))
    calc
      q (gs i)=(q (gs i))^4 := by rw [show (4:ℕ)=3+1 from rfl,pow_succ,h3,one_mul]
      _=1 := h4
  have hk : Subgroup.closure (Set.range gs)≤q.ker := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    exact hgi i
  have hsub : Subsingleton (G ⧸ N) := by
    refine ⟨fun x y => ?_⟩
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective N x
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective N y
    exact (hk (hgen.symm ▸ Subgroup.mem_top a)).trans
      (hk (hgen.symm ▸ Subgroup.mem_top b)).symm
  letI := hsub
  have h1 : Nat.card (G ⧸ N)=1 := Nat.card_unique
  omega
end SymmetricSubgroupAsymptotics.NoTernaryQuotientFourthPowerWords
