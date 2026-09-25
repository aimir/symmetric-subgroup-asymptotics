import SymmetricSubgroupAsymptotics.InducedCoprimeHead

/-! The full general ternary envelope for an actual induced submodule.
The Gaussian branch uses the explicit published prime-power input;
the coprime branch is proved by Maschke, Frobenius, the actual Mackey
decomposition and the actual Sylow-orbit count. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics
attribute [local instance] inducedMackeyComponentAddCommGroup inducedMackeyComponentModule

theorem induced_coprime_orbit_head_bound (p : ℕ) [Fact p.Prime]
    {G V : Type} [Group G] [Finite G] [AddCommGroup V]
    [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
    (H P : Subgroup G) [NeZero (Nat.card P:ZMod p)]
    (ρ : Representation (ZMod p) H V)
    [Fintype (DoubleCoset.Quotient (H:Set G) (P:Set G))]
    (M : Subrepresentation (Representation.ind H.subtype ρ)) :
    Module.finrank (ZMod p)
      (primeActionCharacters p (representationGroupAction M.toRepresentation))≤
        Module.finrank (ZMod p) V*
          Fintype.card (DoubleCoset.Quotient (H:Set G) (P:Set G)) := by
  letI := induced_finiteDimensional H ρ
  have h := representationCharacterHead_le_coordinates
    (fun q=>inducedMackeyComponent H P ρ q)
    (M.toRepresentation.comp P.subtype)
    (fun q=>Representation.ind (inducedOrbitStabilizer H P q.out).subtype
      (inducedOrbitFibre H P ρ q.out))
    (fun _=>Module.finrank (ZMod p) V)
    (fun q S=>induced_coprime_submodule_head_le_fibre p
      (inducedOrbitStabilizer H P q.out) (inducedOrbitFibre H P ρ q.out) S)
    (inducedMackeySubmoduleCoordinate H P ρ M)
    (inducedMackeySubmoduleCoordinate_injective H P ρ M)
  apply (representationCharacterHead_le_restriction M.toRepresentation P.subtype).trans
  simpa only [Finset.sum_const,Finset.card_univ,Nat.nsmul_eq_mul,Nat.mul_comm] using h

theorem induced_coprime_primePower_head_bound (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hpq : p≠q)
    {G V : Type} [Group G] [Finite G] [AddCommGroup V]
    [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
    (H : Subgroup G) (ρ : Representation (ZMod p) H V)
    (M : Subrepresentation (Representation.ind H.subtype ρ)) :
    Module.finrank (ZMod p)
      (primeActionCharacters p (representationGroupAction M.toRepresentation))*
        q^H.index.factorization q≤Module.finrank (ZMod p) V*H.index := by
  let P : Sylow q G := Classical.choice inferInstance
  letI : Finite (DoubleCoset.Quotient (H:Set G) ((P:Subgroup G):Set G)) :=
    Finite.of_injective (inducedDoubleCosetOrbitEquiv H (P:Subgroup G))
      (inducedDoubleCosetOrbitEquiv H (P:Subgroup G)).injective
  letI : Fintype (DoubleCoset.Quotient (H:Set G) ((P:Subgroup G):Set G)) :=
    Fintype.ofFinite _
  letI : NeZero (Nat.card (P:Subgroup G):ZMod p) := by
    obtain ⟨r,hr⟩ := IsPGroup.iff_card.mp P.isPGroup'
    constructor
    rw [hr,Nat.cast_pow]
    apply pow_ne_zero
    intro hz
    exact hpq ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime)
      (Fact.out : q.Prime)).mp ((ZMod.natCast_eq_zero_iff _ _).mp hz))
  have hh := induced_coprime_orbit_head_bound p H (P:Subgroup G) ρ M
  obtain ⟨j,_,hkj,hs⟩ := inducedMackeySylow_indices H q P
  have hc : Fintype.card (DoubleCoset.Quotient (H:Set G) ((P:Subgroup G):Set G))*
      q^H.index.factorization q≤H.index := by
    calc
      _=∑r:DoubleCoset.Quotient (H:Set G) ((P:Subgroup G):Set G),
          q^H.index.factorization q := by simp
      _≤∑r,q^j r := Finset.sum_le_sum (fun r _=>
        Nat.pow_le_pow_right (Fact.out : q.Prime).pos (hkj r))
      _=H.index := hs
  calc
    _≤(Module.finrank (ZMod p) V*
        Fintype.card (DoubleCoset.Quotient (H:Set G) ((P:Subgroup G):Set G)))*
          q^H.index.factorization q := Nat.mul_le_mul_right _ hh
    _=Module.finrank (ZMod p) V*
        (Fintype.card (DoubleCoset.Quotient (H:Set G) ((P:Subgroup G):Set G))*
          q^H.index.factorization q) := by ring
    _≤Module.finrank (ZMod p) V*H.index := Nat.mul_le_mul_left _ hc

/-- The largest prime-power divisor of the prime-to-three part comes
from an actual prime other than three, with the original valuation.
The convention lpp(1)=1 is witnessed by q=2 when the support is empty. -/
theorem largestPrimePower_ordCompl_three_exists (s : ℕ) :
    ∃q : ℕ,q.Prime ∧ q≠3 ∧
      q^s.factorization q=largestPrimePower (ordCompl[3] s) := by
  let n := ordCompl[3] s
  by_cases hn : n.factorization.support.Nonempty
  · obtain ⟨q,hq,heq⟩ := Finset.sup_mem_of_nonempty
      (f:=fun q=>q^n.factorization q) hn
    have hq0 : n.factorization q≠0 := Finsupp.mem_support_iff.mp hq
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
    have hq3 : q≠3 := by
      intro h
      subst q
      simp [n,Nat.factorization_ordCompl] at hq0
    have hv : n.factorization q=s.factorization q := by
      simp [n,Nat.factorization_ordCompl,Finsupp.erase_ne hq3]
    refine ⟨q,hqp,hq3,?_⟩
    change _=max 1 (n.factorization.support.sup (fun q=>q^n.factorization q))
    rw [←heq,max_eq_right (Nat.one_le_pow _ _ hqp.pos),hv]
  · have he : n.factorization.support=∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have h2 : s.factorization 2=0 := by
      have hz : n.factorization 2=0 := by
        apply Finsupp.notMem_support_iff.mp
        rw [he]
        exact Finset.notMem_empty 2
      simpa [n,Nat.factorization_ordCompl] using hz
    refine ⟨2,by decide,by decide,?_⟩
    change _=max 1 (n.factorization.support.sup (fun q=>q^n.factorization q))
    rw [h2,pow_zero,he,Finset.sup_empty]
    rfl

/-- The coprime entry of the original E envelope, with the original
fibre dimension and original subgroup index. No literature input is
needed for this branch. -/
theorem inducedTernary_coprime_head_bound
    {G V : Type} [Group G] [Finite G] [AddCommGroup V]
    [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
    (H : Subgroup G) (ρ : Representation (ZMod 3) H V)
    (M : Subrepresentation (Representation.ind H.subtype ρ)) :
    (Module.finrank (ZMod 3)
      (primeActionCharacters 3 (representationGroupAction M.toRepresentation)):ℝ)≤
        (Module.finrank (ZMod 3) V:ℝ)*
          ((H.index:ℝ)/largestPrimePower (ordCompl[3] H.index)) := by
  obtain ⟨q,hq,hq3,hpow⟩ := largestPrimePower_ordCompl_three_exists H.index
  letI : Fact q.Prime := ⟨hq⟩
  have h := induced_coprime_primePower_head_bound 3 q hq3.symm H ρ M
  rw [hpow] at h
  have hl : (0:ℝ)<largestPrimePower (ordCompl[3] H.index) := by
    exact_mod_cast largestPrimePower_pos (ordCompl[3] H.index)
  rw [←mul_div_assoc]
  apply (le_div_iff₀ hl).mpr
  exact_mod_cast h

/-- Every actual induced ternary subrepresentation has head at most
its original fibre dimension times the literal E(index,3). The sole
external hypothesis is the published prime-power module theorem. -/
theorem inducedTernary_head_le_envelope
    (hTracey : TraceyPrimePowerModuleInput 3)
    {G V : Type} [Group G] [Finite G] [AddCommGroup V]
    [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
    (H : Subgroup G) (ρ : Representation (ZMod 3) H V)
    (M : Subrepresentation (Representation.ind H.subtype ρ)) :
    (Module.finrank (ZMod 3)
      (primeActionCharacters 3 (representationGroupAction M.toRepresentation)):ℝ)≤
        (Module.finrank (ZMod 3) V:ℝ)*traceyTernaryEnvelope H.index := by
  have hc := inducedTernary_coprime_head_bound H ρ M
  unfold traceyTernaryEnvelope
  split_ifs with hk
  · exact hc
  · rw [mul_min_of_nonneg _ _ (by positivity)]
    apply le_min _ hc
    exact_mod_cast inducedTernary_gaussian_head_bound hTracey H ρ M (Nat.pos_of_ne_zero hk)

end SymmetricSubgroupAsymptotics
