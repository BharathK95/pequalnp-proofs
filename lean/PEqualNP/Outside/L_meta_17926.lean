import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17926

theorem main_proof :
    ∀ (x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ))) (x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool),
      (∀ (x3 x4 x5 x6 : Finset (Fin (13 : ℕ))), x3 ⊆ x4 → x5 ⊆ x6 → x2 x3 x5 = Bool.true → x2 x4 x6 = Bool.true) →
      (∀ (x4 x5 : Fin (13 : ℕ)), x4 ∈ x1 x5 → x2 {x4} {x5} = Bool.true) →
      x2 Finset.univ ∅ = Bool.false →
      (∀ (x6 : Fin (13 : ℕ)), x2 (x1 x6)ᶜ {x6} = Bool.false) →
      ∀ (x7 x8 : Finset (Fin (13 : ℕ))), x8.card ≤ (1 : ℕ) →
        (x2 x7 x8 = Bool.true ↔ ∃ x10 ∈ x7, ∃ x11 ∈ x8, x10 ∈ x1 x11) := by
  intro L f hmono hpos hemp hneg A B hB
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hB with h0 | h1
  · have hBe : B = ∅ := Finset.card_eq_zero.mp h0
    subst hBe
    constructor
    · intro ht
      have hbad := hmono A Finset.univ ∅ ∅ (Finset.subset_univ A) (Finset.Subset.refl ∅) ht
      rw [hemp] at hbad
      cases hbad
    · rintro ⟨_, _, l, hl, _⟩
      exact absurd hl (Finset.notMem_empty l)
  · obtain ⟨l, rfl⟩ := Finset.card_eq_one.mp h1
    constructor
    · intro ht
      by_contra hnone
      have hsub : A ⊆ (L l)ᶜ := by
        intro p hp
        rw [Finset.mem_compl]
        intro hpL
        exact hnone ⟨p, hp, l, Finset.mem_singleton_self l, hpL⟩
      have hbad := hmono A (L l)ᶜ {l} {l} hsub (Finset.Subset.refl {l}) ht
      rw [hneg l] at hbad
      cases hbad
    · rintro ⟨p, hp, l', hl', hpL⟩
      have hl : l' = l := Finset.mem_singleton.mp hl'
      rw [hl] at hpL
      exact hmono {p} A {l} {l} (Finset.singleton_subset_iff.mpr hp) (Finset.Subset.refl {l}) (hpos p l hpL)

end PEqualNP.Outside.L_meta_17926

theorem PEqualNP.Outside.L_meta_17926 : (∀ (x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ))) (x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool), (∀ (x3 x4 x5 x6 : Finset (Fin (13 : ℕ))), x3 ⊆ x4 → x5 ⊆ x6 → x2 x3 x5 = Bool.true → x2 x4 x6 = Bool.true) → (∀ (x4 x5 : Fin (13 : ℕ)), x4 ∈ x1 x5 → x2 {x4} {x5} = Bool.true) → x2 Finset.univ ∅ = Bool.false → (∀ (x6 : Fin (13 : ℕ)), x2 (x1 x6)ᶜ {x6} = Bool.false) → ∀ (x7 x8 : Finset (Fin (13 : ℕ))), x8.card ≤ (1 : ℕ) → (x2 x7 x8 = Bool.true ↔ ∃ x10 ∈ x7, ∃ x11 ∈ x8, x10 ∈ x1 x11)) := by
  exact PEqualNP.Outside.L_meta_17926.main_proof
