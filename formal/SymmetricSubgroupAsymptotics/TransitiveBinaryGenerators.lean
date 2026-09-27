import SymmetricSubgroupAsymptotics.TransitiveBinaryNormalHead
import SymmetricSubgroupAsymptotics.PrimeFrattiniGenerators

/-! Actual short generating tuples for a faithful transitive binary group.
The character bound is derived from the all-normal theorem at the original
top subgroup. Frattini lifting then gives generators in that same group;
padding adds only identities. No generating-rank estimate is a premise. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

theorem transitiveBinary_primeCharacterRank_le_cumulative
    {X : Type} [Finite X] (k : ℕ) (U : Subgroup (Equiv.Perm X))
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (hdegree : Nat.card X = 2^k) :
    Module.finrank (ZMod 2) (PrimeCharacters 2 U) ≤ binaryCumulativeWidth k := by
  have hinj : Function.Injective (primeCharacterRestriction 2 (⊤ : Subgroup U)) := by
    intro χ ψ h
    ext x
    exact DFunLike.congr_fun (congrArg Subtype.val h)
      (Additive.ofMul (⟨x, Subgroup.mem_top _⟩ : (⊤ : Subgroup U)))
  exact ((primeCharacterRestriction 2 (⊤ : Subgroup U)).finrank_le_finrank_of_injective
    hinj).trans (transitiveBinary_normal_relativeHead_le_cumulative k U hU hdegree ⊤)

/-- Any original generating tuple can be padded by identities to a larger
prescribed length, without changing its generated subgroup. -/
theorem exists_generating_tuple_of_length_le {G : Type*} [Group G]
    {d a : ℕ} (g : Fin d → G) (hg : Subgroup.closure (Set.range g) = ⊤)
    (hda : d ≤ a) :
    ∃ f : Fin a → G, Subgroup.closure (Set.range f) = ⊤ := by
  classical
  let e : Fin d → Fin a := Fin.castLE hda
  have he : Function.Injective e := by
    intro i j hij
    apply Fin.ext
    exact congrArg (fun x : Fin a => x.val) hij
  let f : Fin a → G := Function.extend e g (fun _ => 1)
  refine ⟨f, top_unique ?_⟩
  rw [← hg]
  apply Subgroup.closure_mono
  rintro _ ⟨i, rfl⟩
  exact ⟨e i, he.extend_apply _ _ i⟩

/-- A tuple in the literal original permutation subgroup, of length
`sum_{j<k} choose(j,j/2)`, generates that entire subgroup. This includes
degree one, where the tuple is empty and the group is trivial. -/
theorem transitiveBinary_exists_generating_tuple
    {X : Type} [Finite X] (k : ℕ) (U : Subgroup (Equiv.Perm X))
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (hdegree : Nat.card X = 2^k) :
    ∃ g : Fin (binaryCumulativeWidth k) → U,
      Subgroup.closure (Set.range g) = ⊤ := by
  obtain ⟨g, hg⟩ := exists_primeFrattini_generating_tuple 2 hU
  exact exists_generating_tuple_of_length_le g hg
    (transitiveBinary_primeCharacterRank_le_cumulative k U hU hdegree)

end SymmetricSubgroupAsymptotics
