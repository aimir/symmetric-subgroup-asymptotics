import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeSixS3ProductSource

/-!
# The finite algebra certificate for the degree-six `S₃ × S₃` cell

This file supplies the two fixed-group facts required by
`DegreeSixS3Product.Algebra`.  All maps are defined explicitly.  Finite
verification is used only for identities in the displayed groups `S₃`,
`A₃`, and `S₃ × S₃`; normal-subgroup coverage is then proved uniformly from
commutators rather than by enumerating subgroups.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical commutatorElement

namespace SymmetricSubgroupAsymptotics
namespace DegreeSixS3Product

private abbrev S3 := OddMarkerGroup
private abbrev C3 := Multiplicative (ZMod 3)

/-- A fixed transposition used to generate both alternating coordinates by
commutators. -/
private def transposition : S3 := Equiv.swap (0 : Fin 3) 1

/-- A fixed positive three-cycle. -/
private def rotation : S3 :=
  Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2

/-- Explicit ternary coordinates on the literal alternating kernel. -/
def kernelCoordinate : oddMarkerSign.ker →* C3 where
  toFun g :=
    if (g : S3) = 1 then 1
    else if (g : S3) = rotation then Multiplicative.ofAdd 1
    else Multiplicative.ofAdd 2
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

private theorem first_mem_kernel (v : derivedBase) :
    (v : G).1 ∈ oddMarkerSign.ker := by
  rw [MonoidHom.mem_ker]
  have hv := MonoidHom.mem_ker.mp v.2
  change (oddMarkerSign (v : G).1, oddMarkerSign (v : G).2) = (1, 1) at hv
  exact congrArg Prod.fst hv

private theorem second_mem_kernel (v : derivedBase) :
    (v : G).2 ∈ oddMarkerSign.ker := by
  rw [MonoidHom.mem_ker]
  have hv := MonoidHom.mem_ker.mp v.2
  change (oddMarkerSign (v : G).1, oddMarkerSign (v : G).2) = (1, 1) at hv
  exact congrArg Prod.snd hv

/-- First alternating coordinate of the full derived base. -/
def firstKernel : derivedBase →* oddMarkerSign.ker where
  toFun v := ⟨(v : G).1, first_mem_kernel v⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

/-- Second alternating coordinate of the full derived base. -/
def secondKernel : derivedBase →* oddMarkerSign.ker where
  toFun v := ⟨(v : G).2, second_mem_kernel v⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

/-- The sum of the two explicit ternary coordinates, written
multiplicatively.  Independent conjugation by the two sign factors makes
its conjugates separate all of `A₃ × A₃`. -/
def character : derivedBase →* C3 :=
  (kernelCoordinate.comp firstKernel) *
    (kernelCoordinate.comp secondKernel)

private theorem oddKernel_commute (x y : oddMarkerSign.ker) :
    x * y = y * x := by
  decide +kernel +revert

private theorem pairedKernelCoordinate_separating
    (x y : oddMarkerSign.ker)
    (h : ∀ q r : S3,
      kernelCoordinate (MulAut.conjNormal q x) *
        kernelCoordinate (MulAut.conjNormal r y) = 1) :
    x = 1 ∧ y = 1 := by
  revert x y
  decide +kernel

private theorem prod_commutator (a b c d : S3) :
    ⁅(a, b), (c, d)⁆ = (⁅a, c⁆, ⁅b, d⁆) := by
  rfl

set_option maxRecDepth 8192 in
/-- Every alternating permutation is one commutator with the fixed
transposition. -/
private theorem kernel_commutator_witness (a : S3)
    (ha : a ∈ oddMarkerSign.ker) :
    ∃ s : S3, ⁅s, transposition⁆ = a := by
  revert a
  decide +kernel

set_option maxRecDepth 8192 in
/-- Against an arbitrary nonidentity permutation, commutators and their
 inverses cover the alternating kernel. -/
private theorem nontrivial_commutator_witness (a : S3) (ha : a ≠ 1)
    (k : S3) (hk : k ∈ oddMarkerSign.ker) :
    ∃ s : S3, ⁅s, a⁆ = k ∨ ⁅s, a⁆⁻¹ = k := by
  revert a k
  decide +kernel

/-- The first derived subgroup is exactly the two alternating factors. -/
theorem derivedSeries_one_eq : derivedSeries G 1 = derivedBase := by
  apply le_antisymm
  · rw [derivedSeries_one]
    exact Abelianization.commutator_subset_ker
      (oddMarkerSign.prodMap oddMarkerSign)
  · intro x hx
    have hx' := MonoidHom.mem_ker.mp hx
    change (oddMarkerSign x.1, oddMarkerSign x.2) = (1, 1) at hx'
    have hx1 : x.1 ∈ oddMarkerSign.ker := by
      rw [MonoidHom.mem_ker]
      exact congrArg Prod.fst hx'
    have hx2 : x.2 ∈ oddMarkerSign.ker := by
      rw [MonoidHom.mem_ker]
      exact congrArg Prod.snd hx'
    obtain ⟨s, hs⟩ := kernel_commutator_witness x.1 hx1
    obtain ⟨t, ht⟩ := kernel_commutator_witness x.2 hx2
    have hmem : ⁅(s, t), (transposition, transposition)⁆ ∈ derivedSeries G 1 :=
      (by
        rw [derivedSeries_one]
        exact Subgroup.commutator_mem_commutator
          (Subgroup.mem_top _) (Subgroup.mem_top _))
    simpa only [prod_commutator, hs, ht, Prod.eta] using hmem

set_option maxRecDepth 8192 in
private theorem derivedBase_selfCentralizing :
    ∀ q : G, (∀ v ∈ derivedBase, q * v = v * q) → q ∈ derivedBase := by
  intro q hq
  simp only [derivedBase, MonoidHom.mem_ker] at hq ⊢
  revert q
  decide +kernel +revert

set_option maxRecDepth 8192 in
private theorem derivedBase_commutative :
    ∀ v ∈ derivedBase, ∀ w ∈ derivedBase, v * w = w * v := by
  intro v hv w hw
  have hv1 : v.1 ∈ oddMarkerSign.ker := by
    rw [MonoidHom.mem_ker]
    exact congrArg Prod.fst (MonoidHom.mem_ker.mp hv)
  have hv2 : v.2 ∈ oddMarkerSign.ker := by
    rw [MonoidHom.mem_ker]
    exact congrArg Prod.snd (MonoidHom.mem_ker.mp hv)
  have hw1 : w.1 ∈ oddMarkerSign.ker := by
    rw [MonoidHom.mem_ker]
    exact congrArg Prod.fst (MonoidHom.mem_ker.mp hw)
  have hw2 : w.2 ∈ oddMarkerSign.ker := by
    rw [MonoidHom.mem_ker]
    exact congrArg Prod.snd (MonoidHom.mem_ker.mp hw)
  apply Prod.ext
  · exact congrArg Subtype.val
      (oddKernel_commute ⟨v.1, hv1⟩ ⟨w.1, hw1⟩)
  · exact congrArg Subtype.val
      (oddKernel_commute ⟨v.2, hv2⟩ ⟨w.2, hw2⟩)

private def diagonalTransposition : G := (transposition, transposition)

set_option maxRecDepth 8192 in
private theorem diagonalTransposition_fixedPointFree :
    ∀ v ∈ derivedBase,
      diagonalTransposition * v * diagonalTransposition⁻¹ = v → v = 1 := by
  intro v hv hfixed
  simp only [derivedBase, MonoidHom.mem_ker] at hv
  revert v
  decide +kernel +revert

private theorem derivedBase_absorbing (W : Subgroup G) (hW : W.Normal)
    (hWV : W ≤ derivedBase) :
    W ≤ ⁅derivedSeries G 0, W⁆ := by
  apply DerivedHead.absorbing_of_fixedPointFree 0 diagonalTransposition
  · rw [derivedSeries_zero]
    exact Subgroup.mem_top _
  · rw [derivedSeries_one_eq]
    exact derivedBase_commutative
  · rw [derivedSeries_one_eq]
    exact diagonalTransposition_fixedPointFree
  · exact hW
  · exact hWV.trans derivedSeries_one_eq.ge

set_option maxRecDepth 8192 in
private theorem character_separating :
    ∀ v : derivedBase,
      (∀ q : G, character (MulAut.conjNormal q v) = 1) → v = 1 := by
  intro v h
  let x : oddMarkerSign.ker := firstKernel v
  let y : oddMarkerSign.ker := secondKernel v
  have hxy : ∀ q r : S3,
      kernelCoordinate (MulAut.conjNormal q x) *
        kernelCoordinate (MulAut.conjNormal r y) = 1 := by
    intro q r
    simpa [character, x, y, firstKernel, secondKernel,
      MulAut.conjNormal_apply] using h (q, r)
  obtain ⟨hx, hy⟩ := pairedKernelCoordinate_separating x y hxy
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg Subtype.val hx
  · exact congrArg Subtype.val hy

/-- The concrete ternary cyclic-dual target on `A₃ × A₃`. -/
def target : DerivedHead.DerivedCyclicTarget G derivedBase 0 3 where
  derived_eq := by simpa only [Nat.zero_add] using derivedSeries_one_eq
  character := character
  self_centralizing := derivedBase_selfCentralizing
  absorbing := derivedBase_absorbing
  separating := character_separating

private theorem commutator_mem_normal (N : Subgroup G) (hN : N.Normal)
    {x : G} (hx : x ∈ N) (g : G) : ⁅g, x⁆ ∈ N := by
  rw [commutatorElement_def]
  exact N.mul_mem (hN.conj_mem _ hx g) (N.inv_mem hx)

private theorem mem_leftProjection_ker (x : G) :
    x ∈ leftProjection.ker ↔
      x.1 = 1 ∧ x.2 ∈ oddMarkerSign.ker := by
  change (x.1, oddMarkerSign x.2) = (1, 1) ↔
    x.1 = 1 ∧ oddMarkerSign x.2 = 1
  simp only [Prod.mk.injEq]

private theorem mem_rightProjection_ker (x : G) :
    x ∈ rightProjection.ker ↔
      x.2 = 1 ∧ x.1 ∈ oddMarkerSign.ker := by
  change (x.2, oddMarkerSign x.1) = (1, 1) ↔
    x.2 = 1 ∧ oddMarkerSign x.1 = 1
  simp only [Prod.mk.injEq]

private theorem leftProjection_ker_le_of_second_ne_one
    (N : Subgroup G) (hN : N.Normal) (a b : S3)
    (hab : (a, b) ∈ N) (hb : b ≠ 1) :
    leftProjection.ker ≤ N := by
  rintro ⟨u, v⟩ huv
  rw [mem_leftProjection_ker] at huv
  rcases huv with ⟨hu, hv⟩
  change u = 1 at hu
  subst u
  obtain ⟨s, hs | hs⟩ := nontrivial_commutator_witness b hb v hv
  · have hc : (1, ⁅s, b⁆) ∈ N := by
      simpa only [prod_commutator, commutatorElement_one_left] using
        commutator_mem_normal N hN hab (1, s)
    simpa only [hs] using hc
  · have hc : (1, ⁅s, b⁆) ∈ N := by
      simpa only [prod_commutator, commutatorElement_one_left] using
        commutator_mem_normal N hN hab (1, s)
    simpa [hs] using N.inv_mem hc

private theorem rightProjection_ker_le_of_first_ne_one
    (N : Subgroup G) (hN : N.Normal) (a b : S3)
    (hab : (a, b) ∈ N) (ha : a ≠ 1) :
    rightProjection.ker ≤ N := by
  rintro ⟨u, v⟩ huv
  rw [mem_rightProjection_ker] at huv
  rcases huv with ⟨hv, hu⟩
  change v = 1 at hv
  subst v
  obtain ⟨s, hs | hs⟩ := nontrivial_commutator_witness a ha u hu
  · have hc : (⁅s, a⁆, 1) ∈ N := by
      simpa only [prod_commutator, commutatorElement_one_left] using
        commutator_mem_normal N hN hab (s, 1)
    simpa only [hs] using hc
  · have hc : (⁅s, a⁆, 1) ∈ N := by
      simpa only [prod_commutator, commutatorElement_one_left] using
        commutator_mem_normal N hN hab (s, 1)
    simpa [hs] using N.inv_mem hc

/-- Every nontrivial normal subgroup contains one of the two displayed
alternating-coordinate kernels. -/
theorem normal_cover (N : Subgroup G) (hN : N.Normal) (hNb : N ≠ ⊥) :
    ∃ j : Bool, (projection j).ker ≤ N := by
  obtain ⟨⟨⟨a, b⟩, hab⟩, hn⟩ :=
    (Subgroup.ne_bot_iff_exists_ne_one).mp hNb
  have hab1 : (a, b) ≠ (1 : G) := fun h => hn (Subtype.ext h)
  by_cases ha : a = 1
  · have hb : b ≠ 1 := by
      intro hb
      exact hab1 (Prod.ext ha hb)
    refine ⟨false, ?_⟩
    simpa only [projection] using
      leftProjection_ker_le_of_second_ne_one N hN a b hab hb
  · refine ⟨true, ?_⟩
    simpa only [projection] using
      rightProjection_ker_le_of_first_ne_one N hN a b hab ha

/-- The closed finite algebra package used by the degree-six source. -/
def algebra : Algebra where
  target := target
  normal_cover := normal_cover

end DegreeSixS3Product
end SymmetricSubgroupAsymptotics

end
