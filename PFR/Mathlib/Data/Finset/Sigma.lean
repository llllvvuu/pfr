import Mathlib.Data.Finset.Sigma

section Finset

variable {ι Ω: Type*} {κ : ι → Type*}

theorem Finset.iInter_sigma (S : Finset ι) (T : ∀ i, Finset (κ i)) (f : ∀ i, κ i → Set Ω) :
    ⋂ i ∈ S, ⋂ j : T i, f i j = ⋂ ij ∈ (Finset.sigma S T), f ij.1 ij.2 := by
  ext
  simp_rw [Set.mem_iInter]
  constructor
  . exact fun h ij hij ↦ h ij.fst (mem_sigma.mp hij).left
      ({ val := ij.snd, property := (mem_sigma.mp hij).right } : T ij.fst)
  . exact fun h i hi j ↦ h (Sigma.mk i j) (mem_sigma.mpr (And.intro hi j.property ))

end Finset
