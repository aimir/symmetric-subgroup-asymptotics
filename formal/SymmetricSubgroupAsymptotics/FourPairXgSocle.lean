import SymmetricSubgroupAsymptotics.FourPairXgMinimalLines

/-! Identify the actual Xg socle from its two minimal lines. The
centralizer proof uses two point images and sixteen kernel translations,
not an enumeration of the group or of Sym(8). -/
set_option autoImplicit false
noncomputable section
open scoped IsMulCommutative
namespace SymmetricSubgroupAsymptotics
namespace FourPairXgSocle
open FourPairXgCyclicKernelWords FourPairXgMinimalLines

private theorem basis_comm_checked : ∀ i j : Fin 4,
    sourceBasis i * sourceBasis j = sourceBasis j * sourceBasis i := by
  decide +kernel

instance kernel_commutative : IsMulCommutative kernel := by
  apply Subgroup.isMulCommutative_closure
  rintro x ⟨i, rfl⟩ y ⟨j, rfl⟩
  exact basis_comm_checked i j

def translation (i j : Fin 4) : Source :=
  sourceBasis 0 ^ (i.val % 2) * sourceBasis 1 ^ (i.val / 2) *
    sourceBasis 2 ^ (j.val % 2) * sourceBasis 3 ^ (j.val / 2)

theorem translation_mem (i j : Fin 4) : translation i j ∈ kernel := by
  have hb : ∀ k, sourceBasis k ∈ kernel :=
    fun k => Subgroup.subset_closure (Set.mem_range_self k)
  exact kernel.mul_mem (kernel.mul_mem
    (kernel.mul_mem (kernel.pow_mem (hb 0) _) (kernel.pow_mem (hb 1) _))
    (kernel.pow_mem (hb 2) _)) (kernel.pow_mem (hb 3) _)

private theorem translation_zero_checked : ∀ i j : Fin 4,
    ((translation i j : Source) : Equiv.Perm (Fin 8)) 0 = ⟨i.val, by omega⟩ := by
  decide +kernel
private theorem translation_four_checked : ∀ i j : Fin 4,
    ((translation i j : Source) : Equiv.Perm (Fin 8)) 4 = ⟨4+j.val, by omega⟩ := by
  decide +kernel
private theorem first_half_checked : ∀ x : Fin 8,
    (sourceBasis 2 : Equiv.Perm (Fin 8)) x = x → x.val < 4 := by
  decide +kernel
private theorem second_half_checked : ∀ x : Fin 8,
    (sourceBasis 0 : Equiv.Perm (Fin 8)) x = x → 4 ≤ x.val := by
  decide +kernel
private theorem orbit_checked : ∀ x : Fin 8, ∃ i j : Fin 4,
    (translation i j : Equiv.Perm (Fin 8)) (if x.val < 4 then 0 else 4) = x := by
  decide +kernel

/-- The independent regular translations on the two literal quartets
have no extra centralizer even inside the original permutation group. -/
theorem kernel_selfCentralizing : Subgroup.centralizer (kernel : Set Source) ≤ kernel := by
  intro g hg
  have hc : ∀ k ∈ kernel, k*g = g*k := Subgroup.mem_centralizer_iff.mp hg
  have hb : ∀ k, sourceBasis k ∈ kernel :=
    fun k => Subgroup.subset_closure (Set.mem_range_self k)
  have hfirst : ((g : Equiv.Perm (Fin 8)) 0).val < 4 := by
    apply first_half_checked
    have h := congrArg (fun z : Source => (z : Equiv.Perm (Fin 8)) 0) (hc _ (hb 2))
    simpa only [Subgroup.coe_mul, Equiv.Perm.mul_apply, sourceBasis,
      sourceGenerators, closureGenerators, generators, basis] using h
  have hsecond : 4 ≤ ((g : Equiv.Perm (Fin 8)) 4).val := by
    apply second_half_checked
    have h := congrArg (fun z : Source => (z : Equiv.Perm (Fin 8)) 4) (hc _ (hb 0))
    simpa only [Subgroup.coe_mul, Equiv.Perm.mul_apply, sourceBasis,
      sourceGenerators, closureGenerators, generators, basis] using h
  let i : Fin 4 := ⟨((g : Equiv.Perm (Fin 8)) 0).val, hfirst⟩
  let j : Fin 4 := ⟨((g : Equiv.Perm (Fin 8)) 4).val - 4, by omega⟩
  let h := translation i j
  have hm : h ∈ kernel := translation_mem i j
  have h0 : (h : Equiv.Perm (Fin 8)) 0 = (g : Equiv.Perm (Fin 8)) 0 := by
    rw [translation_zero_checked]
  have h4 : (h : Equiv.Perm (Fin 8)) 4 = (g : Equiv.Perm (Fin 8)) 4 := by
    rw [translation_four_checked]
    apply Fin.ext
    dsimp [j]
    omega
  have he : g = h := by
    apply Subtype.ext
    ext x
    obtain ⟨p, q, hx⟩ := orbit_checked x
    let k := translation p q
    let z : Fin 8 := if x.val < 4 then 0 else 4
    have hk : k ∈ kernel := translation_mem p q
    have hgz : (g : Equiv.Perm (Fin 8)) z = (h : Equiv.Perm (Fin 8)) z := by
      dsimp [z]
      split <;> first | exact h0.symm | exact h4.symm
    have hgk := congrArg (fun a : Source => (a : Equiv.Perm (Fin 8)) z) (hc k hk)
    have hhk : k*h = h*k :=
      congrArg Subtype.val (mul_comm (⟨k, hk⟩ : kernel) ⟨h, hm⟩)
    have hhkz := congrArg (fun a : Source => (a : Equiv.Perm (Fin 8)) z) hhk
    change (k : Equiv.Perm (Fin 8)) ((g : Equiv.Perm (Fin 8)) z) =
      (g : Equiv.Perm (Fin 8)) ((k : Equiv.Perm (Fin 8)) z) at hgk
    change (k : Equiv.Perm (Fin 8)) ((h : Equiv.Perm (Fin 8)) z) =
      (h : Equiv.Perm (Fin 8)) ((k : Equiv.Perm (Fin 8)) z) at hhkz
    change (k : Equiv.Perm (Fin 8)) z = x at hx
    rw [← hx, ← hgk, hgz, hhkz]
  exact he.symm ▸ hm

theorem socle_eq_kernel : finiteGroupSocle Source = kernel :=
  le_antisymm
    ((finiteGroupSocle_le_centralizer_of_abelian_normal kernel).trans kernel_selfCentralizing)
    kernel_le_socle

/-- One actual kernel vector normally generates the whole original Xg socle. -/
theorem socle_one : SocleNormalGeneratorBound Source 1 :=
  ⟨fun _ => sourceBasis 0, kernel_cyclic.trans socle_eq_kernel.symm⟩

end FourPairXgSocle
end SymmetricSubgroupAsymptotics
