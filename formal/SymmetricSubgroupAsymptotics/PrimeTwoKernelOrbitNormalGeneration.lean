import SymmetricSubgroupAsymptotics.PrimeTwoAxisConjugateNormalGeneration

/-! A genuine two-element orbit of actual prime-cyclic coordinate kernels
provides its own axis seed. Equal kernel cardinalities follow from the
actual ambient conjugator; joint coordinate faithfulness then gives one
normal generator of the SAME original normal subgroup. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimeTwoKernelOrbitNormalGeneration

theorem normalGen_le_one_of_two_kernel_orbit
    {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (p : ℕ) [Fact p.Prime] (f g : N →* Multiplicative (ZMod p))
    (hjoint : Function.Injective (fun u : N => (f u,g u))) (h : G)
    (hne : f.ker ≠ g.ker)
    (hfg : f.ker.map (MulAut.conjNormal h).toMonoidHom = g.ker)
    (hgf : g.ker.map (MulAut.conjNormal h).toMonoidHom = f.ker) :
    MarkedC4.normalGen N ≤ 1 := by
  letI : Finite N := Finite.of_injective (fun u : N => (f u,g u)) hjoint
  let a : MulAut N := MulAut.conjNormal h
  have hcard : Nat.card f.ker = Nat.card g.ker := by
    calc
      Nat.card f.ker = Nat.card (f.ker.map a.toMonoidHom) :=
        Nat.card_congr (a.subgroupMap f.ker).toEquiv
      _ = Nat.card g.ker := congrArg (fun K : Subgroup N => Nat.card K) hfg
  have hnotle : ¬ g.ker ≤ f.ker := by
    intro hle
    exact hne (Subgroup.eq_of_le_of_card_ge hle hcard.le).symm
  obtain ⟨x,hgx,hfx⟩ := Set.not_subset.mp hnotle
  have hfx' : f x ≠ 1 := hfx
  have hgx' : g x = 1 := hgx
  have hyf : f (a x) = 1 := by
    change a x ∈ f.ker
    rw [←hgf]
    exact ⟨x,hgx,rfl⟩
  have hyg : g (a x) ≠ 1 := by
    intro hgy
    have hy1 : a x = 1 := hjoint (by
      change (f (a x),g (a x)) = (f 1,g 1)
      rw [hyf,hgy,map_one,map_one])
    have hx1 : x = 1 := a.injective (hy1.trans (map_one a).symm)
    exact hfx' (by rw [hx1,map_one])
  exact PrimeTwoAxisConjugateNormalGeneration.normalGen_le_one_of_actual_conjugate_axes
    N p f g hjoint x hfx' hgx' h hyf hyg

end SymmetricSubgroupAsymptotics.PrimeTwoKernelOrbitNormalGeneration
