import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameTop15TopCertificate
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameTop16TopCertificate
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameTop17TopCertificate
import SymmetricSubgroupAsymptotics.BinaryPairFrameGenerators
import SymmetricSubgroupAsymptotics.BinaryPairFrameFourMonolith
import SymmetricSubgroupAsymptotics.Non2PreE7NaturalS4Group

/-! Shared actual central-monolith coordinates for Y3, Y4 and Y5.
Row0/1/2 are the original retained top15/16/17. The first two five-generator
lists are padded only by identity. No graph or normal census is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FourPairY345CentralFrames

def pointFrame : Fin 4 × ZMod 2 ≃ Fin 8 :=
  (Equiv.prodCongr (Equiv.refl (Fin 4)) (ZMod.finEquiv 2).symm.toEquiv).trans
    finProdFinEquiv

def generators (k : Fin 3) : Fin 6 → Equiv.Perm (Fin 8) :=
  ![![PrimitiveAffineEightFrameTop15TopCertificate.generators 0,
       PrimitiveAffineEightFrameTop15TopCertificate.generators 1,
       PrimitiveAffineEightFrameTop15TopCertificate.generators 2,
       PrimitiveAffineEightFrameTop15TopCertificate.generators 3,
       PrimitiveAffineEightFrameTop15TopCertificate.generators 4,1],
    ![PrimitiveAffineEightFrameTop16TopCertificate.generators 0,
       PrimitiveAffineEightFrameTop16TopCertificate.generators 1,
       PrimitiveAffineEightFrameTop16TopCertificate.generators 2,
       PrimitiveAffineEightFrameTop16TopCertificate.generators 3,
       PrimitiveAffineEightFrameTop16TopCertificate.generators 4,1],
    PrimitiveAffineEightFrameTop17TopCertificate.generators] k

def source (k : Fin 3) : Subgroup (Equiv.Perm (Fin 8)) :=
  Subgroup.closure (Set.range (generators k))

def cycleTop : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3

def generatorTops (k : Fin 3) : Fin 6 → Equiv.Perm (Fin 4) :=
  if k = 2 then ![1,1,1,1,cycleTop,Equiv.swap 0 1]
  else ![1,1,1,cycleTop,Equiv.swap 0 1,1]

private theorem frame_checked : ∀ (k : Fin 3) (j : Fin 6) (i : Fin 4) (b : ZMod 2),
    (pointFrame.symm (generators k j (pointFrame (i,b)))).1 = generatorTops k j i := by
  decide +kernel

def pairFrame (k : Fin 3) : BinaryPairFrame (source k) (Fin 4) :=
  BinaryPairFrame.ofGenerators pointFrame (generators k) (generatorTops k)
    (fun j x => frame_checked k j x.1 x.2)

def originalGenerator (k : Fin 3) (j : Fin 6) : source k :=
  ⟨generators k j,Subgroup.subset_closure (Set.mem_range_self j)⟩

private theorem top_generator (k : Fin 3) (j : Fin 6) :
    (pairFrame k).top (originalGenerator k j) = generatorTops k j :=
  BinaryPairFrame.ofGenerators_top_generator pointFrame (generators k) (generatorTops k)
    (fun j x => frame_checked k j x.1 x.2) j

def cycleElement (k : Fin 3) : source k :=
  originalGenerator k (if k = 2 then 4 else 3)
def transpositionElement (k : Fin 3) : source k :=
  originalGenerator k (if k = 2 then 5 else 4)

private theorem cycle_top (k : Fin 3) : (pairFrame k).top (cycleElement k) = cycleTop := by
  rw [cycleElement,top_generator]
  fin_cases k <;> rfl
private theorem transposition_top (k : Fin 3) :
    (pairFrame k).top (transpositionElement k) = Equiv.swap 0 1 := by
  rw [transpositionElement,top_generator]
  fin_cases k <;> rfl

def actualKlein (k : Fin 3) : Subgroup (pairFrame k).top.range :=
  NaturalS4.klein.comap (pairFrame k).top.range.subtype
instance actualKlein_normal (k : Fin 3) : (actualKlein k).Normal :=
  Subgroup.Normal.comap NaturalS4.klein_normal (pairFrame k).top.range.subtype

theorem actualKlein_binary (k : Fin 3) : IsPGroup 2 (actualKlein k) := by
  intro g
  refine ⟨1,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change ((g : (pairFrame k).top.range) : Equiv.Perm (Fin 4)) ^ 2 = 1
  exact NaturalS4.kleinSet_sq _ g.property

def uWord (k : Fin 3) : source k :=
  cycleElement k ^ 2 * (transpositionElement k * cycleElement k ^ 2 *
    (transpositionElement k)⁻¹)
def vWord (k : Fin 3) : source k := cycleElement k ^ 2

private theorem u_top (k : Fin 3) : (pairFrame k).top (uWord k) = NaturalS4.c1 := by
  simp only [uWord,map_mul,map_pow,map_inv,cycle_top,transposition_top]
  apply Equiv.ext
  intro i
  revert i
  decide +kernel
private theorem v_top (k : Fin 3) : (pairFrame k).top (vWord k) = NaturalS4.c2 := by
  rw [vWord,map_pow,cycle_top]
  apply Equiv.ext
  intro i
  revert i
  decide +kernel

def kleinU (k : Fin 3) : actualKlein k :=
  ⟨(pairFrame k).top.rangeRestrict (uWord k), by
    change (pairFrame k).top (uWord k) ∈ NaturalS4.klein
    rw [u_top]
    decide +kernel⟩
def kleinV (k : Fin 3) : actualKlein k :=
  ⟨(pairFrame k).top.rangeRestrict (vWord k), by
    change (pairFrame k).top (vWord k) ∈ NaturalS4.klein
    rw [v_top]
    decide +kernel⟩

private theorem u_action (k : Fin 3) : ∀ (x : Fin 4 → ZMod 2) (i : Fin 4),
    (pairFrame k).coordinateTopAction (kleinU k) x i = x (![1,0,3,2] i) := by
  intro x i
  change x (((pairFrame k).top (uWord k))⁻¹ i) = _
  rw [u_top]
  have h : ∀ i : Fin 4, NaturalS4.c1⁻¹ i = ![1,0,3,2] i := by decide +kernel
  rw [h]
private theorem v_action (k : Fin 3) : ∀ (x : Fin 4 → ZMod 2) (i : Fin 4),
    (pairFrame k).coordinateTopAction (kleinV k) x i = x (![2,3,0,1] i) := by
  intro x i
  change x (((pairFrame k).top (vWord k))⁻¹ i) = _
  rw [v_top]
  have h : ∀ i : Fin 4, NaturalS4.c2⁻¹ i = ![2,3,0,1] i := by decide +kernel
  rw [h]

def flipKernel (k : Fin 3) (j : Fin 3) : (pairFrame k).top.ker :=
  ⟨originalGenerator k ⟨j.val,by omega⟩, by
    rw [MonoidHom.mem_ker,top_generator]
    fin_cases k <;> fin_cases j <;> rfl⟩

private theorem separation_checked : ∀ (k : Fin 3) (i j : Fin 4), i ≠ j →
    ∃ a : Fin 3,
      (pointFrame.symm (generators k ⟨a.val,by omega⟩ (pointFrame (i,0)))).2 ≠
      (pointFrame.symm (generators k ⟨a.val,by omega⟩ (pointFrame (j,0)))).2 := by
  decide +kernel

theorem kernel_bits_separate (k : Fin 3) : ∀ i j : Fin 4, i ≠ j →
    ∃ a : (pairFrame k).top.ker, (pairFrame k).bits a i ≠ (pairFrame k).bits a j := by
  intro i j hne
  obtain ⟨a,ha⟩ := separation_checked k i j hne
  exact ⟨flipKernel k a,ha⟩

def constantWord (k : Fin 3) : source k :=
  if k = 2 then originalGenerator k 0 * originalGenerator k 1 *
    originalGenerator k 2 * originalGenerator k 3
  else originalGenerator k 0 * originalGenerator k 2

def constantKernel (k : Fin 3) : (pairFrame k).top.ker :=
  ⟨constantWord k, by
    apply MonoidHom.mem_ker.mpr
    fin_cases k
    · change (pairFrame 0).top (originalGenerator 0 0 * originalGenerator 0 2) = 1
      rw [map_mul,top_generator,top_generator]
      rfl
    · change (pairFrame 1).top (originalGenerator 1 0 * originalGenerator 1 2) = 1
      rw [map_mul,top_generator,top_generator]
      rfl
    · change (pairFrame 2).top (originalGenerator 2 0 * originalGenerator 2 1 *
        originalGenerator 2 2 * originalGenerator 2 3) = 1
      simp only [map_mul,top_generator]
      rfl⟩

def constantPermutation (k : Fin 3) : Equiv.Perm (Fin 8) :=
  if k = 2 then generators k 0 * generators k 1 * generators k 2 * generators k 3
  else generators k 0 * generators k 2

private theorem constantWord_val (k : Fin 3) :
    ((constantWord k : source k) : Equiv.Perm (Fin 8)) = constantPermutation k := by
  fin_cases k <;> rfl

private theorem constant_bits_checked : ∀ (k : Fin 3) (i : Fin 4),
    (pointFrame.symm (constantPermutation k (pointFrame (i,0)))).2 = 1 := by
  decide +kernel

theorem constant_bits (k : Fin 3) : ∀ i : Fin 4,
    (pairFrame k).bits (constantKernel k) i = 1 := by
  intro i
  change (pointFrame.symm (((constantWord k : source k) : Equiv.Perm (Fin 8))
    (pointFrame (i,0)))).2 = 1
  rw [constantWord_val]
  exact constant_bits_checked k i

/-- Complete original-normal monolith theorem for all three actual models.
The central quotient homomorphism is bound separately by its graph test. -/
theorem constant_mem_every_nontrivial_normal (k : Fin 3)
    (N : Subgroup (source k)) (hN : N.Normal) (hne : N ≠ ⊥) :
    (constantKernel k : source k) ∈ N :=
  (pairFrame k).constantFlip_mem_every_nontrivial_normal
    (actualKlein k) (actualKlein_binary k) (kleinU k) (kleinV k)
    (u_action k) (v_action k) (constantKernel k) (constant_bits k)
    (kernel_bits_separate k) N hN hne


private theorem closure_padded (g : Fin 5 → Equiv.Perm (Fin 8)) :
    Subgroup.closure (Set.range (![g 0,g 1,g 2,g 3,g 4,1] : Fin 6 → Equiv.Perm (Fin 8))) =
      Subgroup.closure (Set.range g) := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    fin_cases j
    · exact Subgroup.subset_closure (Set.mem_range_self (0 : Fin 5))
    · exact Subgroup.subset_closure (Set.mem_range_self (1 : Fin 5))
    · exact Subgroup.subset_closure (Set.mem_range_self (2 : Fin 5))
    · exact Subgroup.subset_closure (Set.mem_range_self (3 : Fin 5))
    · exact Subgroup.subset_closure (Set.mem_range_self (4 : Fin 5))
    · exact Subgroup.one_mem _
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    apply Subgroup.subset_closure
    refine ⟨⟨j.val,by omega⟩,?_⟩
    fin_cases j <;> rfl

/-- Exact original retained top15 (canonical index14 / entry8,39). -/
theorem source_eq_top15 : source 0 = Subgroup.closure
    (Set.range PrimitiveAffineEightFrameTop15TopCertificate.generators) :=
  closure_padded _
/-- Exact original retained top16 (canonical index15 / entry8,40). -/
theorem source_eq_top16 : source 1 = Subgroup.closure
    (Set.range PrimitiveAffineEightFrameTop16TopCertificate.generators) :=
  closure_padded _
/-- Exact original retained top17 (canonical index16 / entry8,44). -/
theorem source_eq_top17 : source 2 = Subgroup.closure
    (Set.range PrimitiveAffineEightFrameTop17TopCertificate.generators) := rfl

end SymmetricSubgroupAsymptotics.FourPairY345CentralFrames

end
