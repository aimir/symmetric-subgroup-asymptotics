import SymmetricSubgroupAsymptotics.PGroupPrimeIndexChain

/-! Iterate the actual cyclic subgroup steps to obtain a triangular
right transversal for an arbitrary subgroup of the original p-group.
The recursive grid records higher subgroup coordinates first. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {G ι : Type*} [Group G]

/-- All equations refer to the original ambient group and subgroup H.
The triangular field is proved by recursion, not a supplied p-group input. -/
structure OrderedCosetData (H K : Subgroup G) (ι : Type*)
    (lt comparable : ι → ι → Prop) where
  le : H ≤ K
  repr : ι → G
  mem : ∀ a, repr a ∈ K
  factor : ∀ y : G, y ∈ K → ∃ h : G, h ∈ H ∧ ∃ a : ι, y = h * repr a
  unique : ∀ a b, repr a * (repr b)⁻¹ ∈ H → a = b
  triangular : CosetTriangular H repr lt comparable

def OrderedCosetData.base (H : Subgroup G) :
    OrderedCosetData H H Unit (fun _ _ => False) (fun _ _ => True) where
  le := le_rfl
  repr := fun _ => 1
  mem := fun _ => H.one_mem
  factor := fun y hy => ⟨y, hy, (), (mul_one y).symm⟩
  unique := fun a b _ => Subsingleton.elim a b
  triangular := cosetTriangular_base H

/-- Preserve the actual transversal data at every original cyclic step. -/
def OrderedCosetData.step {p : ℕ} {H K L : Subgroup G}
    {lt comparable : ι → ι → Prop}
    (D : OrderedCosetData H K ι lt comparable) (S : PrimeIndexCosetStep p K L) :
    OrderedCosetData H L (Fin p × ι) (cosetStepLT lt) (cosetStepComparable comparable) where
  le := D.le.trans S.le
  repr := cosetStepRep D.repr S.generator
  mem := cosetStepRep_mem K L S.le D.repr S.generator D.mem S.generator_mem
  factor := cosetStepRep_factor H K L D.repr S.generator D.factor S.factor
  unique := cosetStepRep_unique H K D.le D.repr S.generator D.mem D.unique S.unique
  triangular := cosetTriangular_step H K D.repr S.generator lt comparable
    D.mem D.factor S.normalizes D.triangular

def PrimeCosetGrid (p : ℕ) : ℕ → Type
  | 0 => Unit
  | n + 1 => Fin p × PrimeCosetGrid p n

def primeCosetGridLT (p : ℕ) : (n : ℕ) → PrimeCosetGrid p n → PrimeCosetGrid p n → Prop
  | 0 => fun _ _ => False
  | n + 1 => cosetStepLT (primeCosetGridLT p n)

def primeCosetGridComparable (p : ℕ) :
    (n : ℕ) → PrimeCosetGrid p n → PrimeCosetGrid p n → Prop
  | 0 => fun _ _ => True
  | n + 1 => cosetStepComparable (primeCosetGridComparable p n)

instance primeCosetGridFintype (p n : ℕ) : Fintype (PrimeCosetGrid p n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (Fintype (Fin p × PrimeCosetGrid p n))

theorem primeCosetGrid_card (p n : ℕ) : Fintype.card (PrimeCosetGrid p n) = p ^ n := by
  induction n with
  | zero => simp [PrimeCosetGrid]
  | succ n ih =>
    change Fintype.card (Fin p × PrimeCosetGrid p n) = p ^ (n + 1)
    rw [Fintype.card_prod, Fintype.card_fin, ih, pow_succ, mul_comm]

variable {p : ℕ} [Fact p.Prime]

/-- The triangular property is installed from the original normal
prime-index steps, together with actual factorization and uniqueness. -/
theorem PrimeIndexSubgroupChain.orderedTransversal [Finite G] {H L : Subgroup G}
    (s : PrimeIndexSubgroupChain p H L) :
    Nonempty (OrderedCosetData H L (PrimeCosetGrid p s.length)
      (primeCosetGridLT p s.length) (primeCosetGridComparable p s.length)) := by
  have hiter : ∀ m ≤ s.length,
      Nonempty (OrderedCosetData H (s.subgroup m) (PrimeCosetGrid p m)
        (primeCosetGridLT p m) (primeCosetGridComparable p m)) := by
    intro m
    induction m with
    | zero =>
      intro _
      rw [s.first]
      exact ⟨OrderedCosetData.base H⟩
    | succ m ih =>
      intro hm
      obtain ⟨D⟩ := ih (by omega)
      obtain ⟨S⟩ := primeIndexCosetStep_exists (s.subgroup m) (s.subgroup (m + 1))
        (s.step_le m (by omega)) (s.step_normal m (by omega)) (s.step_index m (by omega))
      exact ⟨D.step S⟩
  simpa only [s.last] using hiter s.length le_rfl

/-- Every original subgroup inclusion of index p^t in a finite p-group
has the actual p-grid triangular transversal. No regular subgroup,
faithful replacement action, or externally supplied chain is assumed. -/
theorem pGroup_orderedPowerTransversal [Finite G] (hG : IsPGroup p G)
    (H L : Subgroup G) (hHL : H ≤ L) (t : ℕ) (hindex : H.relIndex L = p ^ t) :
    Nonempty (OrderedCosetData H L (PrimeCosetGrid p t)
      (primeCosetGridLT p t) (primeCosetGridComparable p t)) := by
  obtain ⟨s⟩ := pGroup_primeIndexSubgroupChain_exists hG H L hHL
  have hlen := s.length_eq hindex
  have ht := s.orderedTransversal
  rw [hlen] at ht
  exact ht

theorem pGroup_orderedCosetTransversal [Finite G] (hG : IsPGroup p G)
    (H : Subgroup G) (t : ℕ) (hindex : H.index = p ^ t) :
    Nonempty (OrderedCosetData H ⊤ (PrimeCosetGrid p t)
      (primeCosetGridLT p t) (primeCosetGridComparable p t)) :=
  pGroup_orderedPowerTransversal hG H ⊤ le_top t
    (by simpa only [Subgroup.relIndex_top_right] using hindex)

/-- Inversion turns the actual right transversal into a bijection with
the original left-coset point set. Normality of H is not required. -/
theorem OrderedCosetData.quotient_bijective {H : Subgroup G}
    {lt comparable : ι → ι → Prop} (D : OrderedCosetData H ⊤ ι lt comparable) :
    Function.Bijective (fun a : ι => (((D.repr a)⁻¹ : G) : G ⧸ H)) := by
  constructor
  · intro a b hab
    apply D.unique a b
    simpa only [inv_inv] using QuotientGroup.eq.mp hab
  · intro q
    refine Quotient.inductionOn q ?_
    intro g
    obtain ⟨h, hh, a, ha⟩ := D.factor g⁻¹ (Subgroup.mem_top _)
    refine ⟨a, QuotientGroup.eq.mpr ?_⟩
    have hg : g = (D.repr a)⁻¹ * h⁻¹ := by
      have he := congrArg Inv.inv ha
      simpa only [inv_inv, mul_inv_rev] using he
    simpa only [inv_inv, hg, mul_inv_cancel_left] using H.inv_mem hh

end SymmetricSubgroupAsymptotics
