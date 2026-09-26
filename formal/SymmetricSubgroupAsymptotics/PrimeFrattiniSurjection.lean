import SymmetricSubgroupAsymptotics.PrimeFrattini
import SymmetricSubgroupAsymptotics.PrimeRelativeCharacters

/-! Surjections preserve the actual prime-evaluation kernel, and therefore
preserve the original Frattini subgroup of a finite p-group. The restricted
maps retain the original ambient conjugation. No extension is assumed split. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime]
variable {G H : Type*} [Group G] [Group H]

/-- Every homomorphism preserves the kernel of evaluation on all actual
prime-field characters. -/
theorem primeAbelianizationGroupMap_ker_map_le (β : G →* H) :
    ((primeAbelianizationGroupMap p G).ker).map β ≤
      (primeAbelianizationGroupMap p H).ker := by
  rintro _ ⟨g,hg,rfl⟩
  change primeAbelianizationMap p H (Additive.ofMul (β g))=0
  ext ψ
  exact congrArg (fun x : PrimeAbelianization p G => x (ψ.comp β.toAdditive))
    (show primeAbelianizationMap p G (Additive.ofMul g)=0 from hg)

/-- An onto original map sends the complete evaluation kernel onto the
complete target evaluation kernel. The correction is an actual element of
ker β, obtained by separation in the source evaluation space. -/
theorem primeAbelianizationGroupMap_ker_map (β : G →* H)
    (hβ : Function.Surjective β) :
    ((primeAbelianizationGroupMap p G).ker).map β =
      (primeAbelianizationGroupMap p H).ker := by
  apply le_antisymm (primeAbelianizationGroupMap_ker_map_le p β)
  intro h hh
  obtain ⟨g,rfl⟩ := hβ h
  let f : Additive β.ker →+ PrimeAbelianization p G :=
    (primeAbelianizationMap p G).comp β.ker.subtype.toAdditive
  let S : Submodule (ZMod p) (PrimeAbelianization p G) := f.range.toZModSubmodule p
  have hgS : primeAbelianizationMap p G (Additive.ofMul g) ∈ S := by
    apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff S _).mp
    intro ℓ hℓ
    let χ : PrimeCharacters p G := ℓ.toAddMonoidHom.comp (primeAbelianizationMap p G)
    have hχ : χ ∈ (primeCharacterRestriction p β.ker).ker := by
      apply LinearMap.mem_ker.mpr
      apply Subtype.ext
      ext n
      change ℓ (primeAbelianizationMap p G (Additive.ofMul (n : G)))=0
      exact (Submodule.mem_dualAnnihilator _).mp hℓ _ ⟨Additive.ofMul n,rfl⟩
    rw [primeCharacterRestriction_ker p β hβ] at hχ
    obtain ⟨ψ,hψ⟩ := hχ
    calc
      ℓ (primeAbelianizationMap p G (Additive.ofMul g)) = χ (Additive.ofMul g) := rfl
      _ = ψ (Additive.ofMul (β g)) :=
        (DFunLike.congr_fun hψ (Additive.ofMul g)).symm
      _ = 0 := congrArg (fun x : PrimeAbelianization p H => x ψ)
        (show primeAbelianizationMap p H (Additive.ofMul (β g))=0 from hh)
  obtain ⟨n,hn⟩ := hgS
  have hn' : primeAbelianizationMap p G (Additive.ofMul (n.toMul : G)) =
      primeAbelianizationMap p G (Additive.ofMul g) := hn
  refine ⟨g*(n.toMul : G)⁻¹,?_,?_⟩
  · change primeAbelianizationMap p G
      (Additive.ofMul g + -Additive.ofMul (n.toMul : G))=0
    rw [map_add,map_neg,hn',add_neg_cancel]
  · rw [map_mul,map_inv,show β (n.toMul : G)=1 from n.toMul.2]
    simp

/-- The map on the two literal evaluation kernels is the original map on
underlying elements. -/
def primeEvaluationKernelMap (β : G →* H) :
    (primeAbelianizationGroupMap p G).ker →*
      (primeAbelianizationGroupMap p H).ker where
  toFun n := ⟨β (n : G),primeAbelianizationGroupMap_ker_map_le p β ⟨n,n.2,rfl⟩⟩
  map_one' := Subtype.ext (map_one β)
  map_mul' _ _ := Subtype.ext (map_mul β _ _)

@[simp] theorem primeEvaluationKernelMap_coe (β : G →* H)
    (n : (primeAbelianizationGroupMap p G).ker) :
    (primeEvaluationKernelMap p β n : H)=β (n : G) := rfl

theorem primeEvaluationKernelMap_surjective (β : G →* H)
    (hβ : Function.Surjective β) : Function.Surjective (primeEvaluationKernelMap p β) := by
  intro n
  have hn : (n : H) ∈ ((primeAbelianizationGroupMap p G).ker).map β := by
    rw [primeAbelianizationGroupMap_ker_map p β hβ]
    exact n.2
  obtain ⟨g,hg,he⟩ := hn
  exact ⟨⟨g,hg⟩,Subtype.ext he⟩

/-- Equivariance is for conjugation by the entire original source and its
actual image, not just conjugation inside the two kernels. -/
theorem primeEvaluationKernelMap_conj (β : G →* H) (g : G)
    (n : (primeAbelianizationGroupMap p G).ker) :
    primeEvaluationKernelMap p β (MulAut.conjNormal g n) =
      MulAut.conjNormal (β g) (primeEvaluationKernelMap p β n) := by
  apply Subtype.ext
  change β (g*(n : G)*g⁻¹)=β g*β (n : G)*(β g)⁻¹
  simp only [map_mul,map_inv]

/-- The actual Frattini subgroups are preserved onto by a surjection from
a finite p-group. The target p-group structure follows from this same map. -/
theorem pGroup_map_frattini [Finite G] (β : G →* H)
    (hβ : Function.Surjective β) (hG : IsPGroup p G) :
    (frattini G).map β=frattini H := by
  letI : Finite H := Finite.of_surjective β hβ
  simpa only [primeAbelianizationGroupMap_ker p G hG,
    primeAbelianizationGroupMap_ker p H (hG.of_surjective β hβ)] using
    primeAbelianizationGroupMap_ker_map p β hβ

/-- The literal restricted Frattini map, available for any onto group map. -/
def frattiniSurjectionMap (β : G →* H) (hβ : Function.Surjective β) :
    frattini G →* frattini H where
  toFun n := ⟨β (n : G),frattini_le_comap_frattini_of_surjective hβ n.2⟩
  map_one' := Subtype.ext (map_one β)
  map_mul' _ _ := Subtype.ext (map_mul β _ _)

@[simp] theorem frattiniSurjectionMap_coe (β : G →* H) (hβ : Function.Surjective β)
    (n : frattini G) : (frattiniSurjectionMap β hβ n : H)=β (n : G) := rfl

theorem frattiniSurjectionMap_surjective [Finite G] (β : G →* H)
    (hβ : Function.Surjective β) (hG : IsPGroup p G) :
    Function.Surjective (frattiniSurjectionMap β hβ) := by
  intro n
  have hn : (n : H) ∈ (frattini G).map β := by
    rw [pGroup_map_frattini p β hβ hG]
    exact n.2
  obtain ⟨g,hg,he⟩ := hn
  exact ⟨⟨g,hg⟩,Subtype.ext he⟩

theorem frattiniSurjectionMap_conj (β : G →* H) (hβ : Function.Surjective β)
    (g : G) (n : frattini G) :
    frattiniSurjectionMap β hβ (MulAut.conjNormal g n) =
      MulAut.conjNormal (β g) (frattiniSurjectionMap β hβ n) := by
  apply Subtype.ext
  change β (g*(n : G)*g⁻¹)=β g*β (n : G)*(β g)⁻¹
  simp only [map_mul,map_inv]

end SymmetricSubgroupAsymptotics
