import SymmetricSubgroupAsymptotics.BinaryPairRepresentation
import SymmetricSubgroupAsymptotics.BinaryPairSubgroupCuts
import SymmetricSubgroupAsymptotics.Non2LiftBound

/-!
# Quotient an original kernel chart by an arbitrary original normal subgroup

Given an original extension chart `Q → B` and an arbitrary normal subgroup
`N ◁ Q`, this file constructs the literal descended extension

`Q/N → Q/(ker π ⊔ N)`.

Its kernel is the exact section `ker π / (ker π ∩ N)`, with the quotient
module and conjugation action constructed from the original chart.  There is
no assumption `N ≤ ker π`, no splitting, and no replacement of either
original quotient by an abstract isomorphic group.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace OriginalKernelModuleChart

variable {p : ℕ} {Q B : Type} [Group Q] [Group B]
variable (π : Q →* B) (A : Rep (ZMod p) B)
variable (E : OriginalKernelModuleChart π A)
variable (N : Subgroup Q) [N.Normal]

private def sameKernelEquiv {G C D : Type*} [Group G] [Group C] [Group D]
    (f : G →* C) (g : G →* D) (hf : Function.Surjective f)
    (hg : Function.Surjective g) (hk : f.ker = g.ker) : C ≃* D :=
  (QuotientGroup.liftEquiv f.ker hf rfl).symm.trans
    (QuotientGroup.liftEquiv f.ker hg hk)

@[simp] private theorem sameKernelEquiv_apply {G C D : Type*}
    [Group G] [Group C] [Group D] (f : G →* C) (g : G →* D)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hk : f.ker = g.ker) (x : G) :
    sameKernelEquiv f g hf hg hk (f x) = g x := by
  change (QuotientGroup.liftEquiv f.ker hg hk)
    ((QuotientGroup.liftEquiv f.ker hf rfl).symm (f x)) = _
  rw [← QuotientGroup.liftEquiv_mk f.ker hf rfl x, MulEquiv.symm_apply_apply]
  rfl

/-- The original kernel in its supplied additive coordinates. -/
def kernelCoordinates : π.ker →* Multiplicative A := E.equiv.symm

/-- The literal image of `N ∩ ker π` in the original kernel module. -/
def normalSpace : Submodule (ZMod p) A :=
  sectionSubgroupImage (E.kernelCoordinates π A) (N.subgroupOf π.ker)

/-- The exact additive section `ker π / (ker π ∩ N)`. -/
abbrev sectionModule := A ⧸ E.normalSpace π A N

/-- The quotient map from the literal original kernel to its section. -/
def sectionMap : π.ker →* Multiplicative (E.sectionModule π A N) :=
  sectionSubgroupCutMap (E.kernelCoordinates π A) (N.subgroupOf π.ker)

omit [N.Normal] in
theorem sectionMap_surjective : Function.Surjective (E.sectionMap π A N) :=
  sectionSubgroupCutMap_surjective (E.kernelCoordinates π A)
    E.equiv.symm.surjective (N.subgroupOf π.ker)

omit [N.Normal] in
/-- The section map kills exactly the original physical intersection. -/
theorem sectionMap_ker : (E.sectionMap π A N).ker = N.subgroupOf π.ker := by
  apply sectionSubgroupCutMap_ker
  intro k hk
  have hk1 : k = 1 := by
    apply E.equiv.symm.injective
    exact (MonoidHom.mem_ker.mp hk).trans (map_one E.equiv.symm).symm
  exact hk1.symm ▸ (N.subgroupOf π.ker).one_mem

/-- Conjugation on the exact kernel section, factored through the literal
top `Q/(ker π ⊔ N)`. -/
def sectionRepresentation :
    Rep (ZMod p) (Q ⧸ (π.ker ⊔ N)) :=
  Rep.of (normalSectionTopRepresentation π.ker N (E.sectionMap π A N)
    (E.sectionMap_surjective π A N) (E.sectionMap_ker π A N))

@[simp] theorem sectionRepresentation_apply (g : Q) (k : π.ker) :
    (E.sectionRepresentation π A N).ρ (QuotientGroup.mk' (π.ker ⊔ N) g)
        (E.sectionMap π A N k).toAdd =
      (E.sectionMap π A N (MulAut.conjNormal g k)).toAdd :=
  normalSectionTopRepresentation_apply π.ker N (E.sectionMap π A N)
    (E.sectionMap_surjective π A N) (E.sectionMap_ker π A N) g k

/-- The actual quotient `Q/N` maps onto its actual acting top. -/
def base : (Q ⧸ N) →* Q ⧸ (π.ker ⊔ N) :=
  QuotientGroup.lift N (QuotientGroup.mk' (π.ker ⊔ N)) (by
    rw [QuotientGroup.ker_mk']
    exact le_sup_right)

@[simp] theorem base_apply (q : Q) :
    base π N (QuotientGroup.mk' N q) = QuotientGroup.mk' (π.ker ⊔ N) q := rfl

theorem base_surjective : Function.Surjective (base π N) := by
  intro b
  obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective (π.ker ⊔ N) b
  exact ⟨QuotientGroup.mk' N q, rfl⟩

/-- The original kernel maps onto the kernel of the descended top map. -/
def quotientKernelMap : π.ker →* (base π N).ker where
  toFun k := ⟨QuotientGroup.mk' N (k : Q), by
    rw [MonoidHom.mem_ker, base_apply]
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_sup_left k.property)⟩
  map_one' := by
    apply Subtype.ext
    exact map_one _
  map_mul' a b := by
    apply Subtype.ext
    exact map_mul _ _ _

theorem quotientKernelMap_surjective : Function.Surjective (quotientKernelMap π N) := by
  intro q
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective N q.val
  have hub : QuotientGroup.mk' (π.ker ⊔ N) u = 1 := by
    rw [← base_apply π N u, hu]
    exact q.property
  obtain ⟨k, hk, n, hn, hkn⟩ := Subgroup.mem_sup_of_normal_right.mp
    ((QuotientGroup.eq_one_iff _).mp hub)
  refine ⟨⟨k, hk⟩, ?_⟩
  apply Subtype.ext
  change QuotientGroup.mk' N k = q.val
  rw [← hu, ← hkn, map_mul]
  have hnq : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff _).mpr hn
  rw [hnq, mul_one]

theorem quotientKernelMap_ker :
    (quotientKernelMap π N).ker = N.subgroupOf π.ker := by
  ext k
  rw [MonoidHom.mem_ker, Subtype.ext_iff]
  change QuotientGroup.mk' N (k : Q) = 1 ↔ (k : Q) ∈ N
  exact QuotientGroup.eq_one_iff _

/-- The additive kernel section and the actual descended group kernel are
the same quotient of the same literal original kernel. -/
def kernelEquiv : Multiplicative (E.sectionModule π A N) ≃* (base π N).ker :=
  sameKernelEquiv (E.sectionMap π A N) (quotientKernelMap π N)
    (E.sectionMap_surjective π A N) (quotientKernelMap_surjective π N)
    ((E.sectionMap_ker π A N).trans (quotientKernelMap_ker π N).symm)

@[simp] theorem kernelEquiv_apply (k : π.ker) :
    E.kernelEquiv π A N (E.sectionMap π A N k) = quotientKernelMap π N k :=
  sameKernelEquiv_apply _ _ _ _ _ k

/-- The exact original quotient-kernel chart for every original normal axis. -/
def quotientChart :
    OriginalKernelModuleChart (k := ZMod p) (base π N) (E.sectionRepresentation π A N) where
  equiv := E.kernelEquiv π A N
  conjugate q a := by
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective N q
    obtain ⟨k, hk⟩ := E.sectionMap_surjective π A N (Multiplicative.ofAdd a)
    have ha : (E.sectionMap π A N k).toAdd = a := congrArg Multiplicative.toAdd hk
    rw [← ha, base_apply, E.sectionRepresentation_apply]
    have he (l : π.ker) :
        (E.kernelEquiv π A N (E.sectionMap π A N l) : Q ⧸ N) =
          QuotientGroup.mk' N (l : Q) :=
      congrArg Subtype.val (E.kernelEquiv_apply π A N l)
    calc
      _ = QuotientGroup.mk' N (MulAut.conjNormal u k : Q) :=
        he (MulAut.conjNormal u k)
      _ = QuotientGroup.mk' N u * QuotientGroup.mk' N (k : Q) *
          (QuotientGroup.mk' N u)⁻¹ := by
        change QuotientGroup.mk' N (u * (k : Q) * u⁻¹) = _
        simp only [map_mul, map_inv]
      _ = _ := congrArg (fun z : Q ⧸ N =>
        QuotientGroup.mk' N u * z * (QuotientGroup.mk' N u)⁻¹) (he k).symm

end OriginalKernelModuleChart
end SymmetricSubgroupAsymptotics
