import SymmetricSubgroupAsymptotics.CFSGPrimeBinaryAbelianNormal
import Mathlib.Algebra.Group.Pi.Lemmas

/-! In the same prime-dimensional binary situation, an actual direct
product of noncommutative groups has at most one factor. A coordinate kernel
is irreducible by Clifford; the complementary coordinate would embed in
its cyclic linear centralizer. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical IsMulCommutative

namespace SymmetricSubgroupAsymptotics.CFSGPrimeBinaryProductFactors

variable {I S V : Type} [Finite I] [Group S] [Finite S]
  [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] [Finite V]

theorem factor_index_subsingleton
    (rho : Representation (ZMod 2) (I → S) V)
    (hrho : Representation.IsIrreducible rho) (hf : Function.Injective rho)
    (hd : (Module.finrank (ZMod 2) V).Prime)
    {p : ℕ} [Fact p.Prime] (hcard : Nat.card V - 1 = p)
    (hnc : ¬ IsMulCommutative S) : Subsingleton I := by
  by_contra hi
  letI : Nontrivial I := not_subsingleton_iff_nontrivial.mp hi
  have hs : ¬ Subsingleton S := by
    intro hS
    letI : Subsingleton S := hS
    exact hnc ⟨⟨fun _ _ => Subsingleton.elim _ _⟩⟩
  letI : Nontrivial S := not_subsingleton_iff_nontrivial.mp hs
  obtain ⟨i, j, hij⟩ := exists_pair_ne I
  obtain ⟨x, hx⟩ := exists_ne (1 : S)
  let fi : S →* (I → S) := MonoidHom.mulSingle (fun _ : I => S) i
  let fj : S →* (I → S) := MonoidHom.mulSingle (fun _ : I => S) j
  let N : Subgroup (I → S) := (Pi.evalMonoidHom (fun _ : I => S) i).ker
  have hN : N ≠ ⊥ := by
    intro hzero
    have hm : fj x ∈ N := by
      change (Pi.mulSingle j x : I → S) i = 1
      simp [Pi.mulSingle_apply, hij, Ne.symm hij]
    have he : fj x = 1 := by simpa only [hzero, Subgroup.mem_bot] using hm
    apply hx
    simpa only [fj, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same, Pi.one_apply]
      using congrFun he j
  letI : Representation.IsIrreducible (rho.comp N.subtype) :=
    CFSGCliffordBinaryPrimeDimension.normal_restriction_irreducible
      rho hrho hf hd N hN
  letI : IsCyclic (CFSGIrreducibleLinearCentralizer.linearCentralizer
      (rho.comp N.subtype)) :=
    CFSGIrreducibleLinearCentralizer.centralizer_isCyclic_of_prime_nonzero_card
      (rho.comp N.subtype) hcard
  have hc (d : fi.range) (n : N) : (d : I → S) * n = n * d := by
    obtain ⟨a, ha⟩ := d.2
    have hn : (n : I → S) i = 1 := MonoidHom.mem_ker.mp n.2
    apply funext
    intro k
    change (d : I → S) k * n.1 k = n.1 k * (d : I → S) k
    rw [← ha]
    by_cases hk : k = i
    · subst k
      simp only [hn, mul_one, one_mul]
    · simp [fi, hk]
  letI : IsCyclic fi.range := isCyclic_of_injective
    (CFSGPrimeBinaryAbelianNormal.commutingSubgroupHom rho N fi.range hc)
    (CFSGPrimeBinaryAbelianNormal.commutingSubgroupHom_injective rho hf N fi.range hc)
  have hfi : Function.Injective fi := by
    intro a b hab
    simpa only [fi, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same]
      using congrFun hab i
  letI : IsCyclic S := isCyclic_of_injective fi.rangeRestrict
    (fun a b hab => hfi (congrArg Subtype.val hab))
  exact hnc ⟨⟨fun a b => mul_comm a b⟩⟩

end SymmetricSubgroupAsymptotics.CFSGPrimeBinaryProductFactors
