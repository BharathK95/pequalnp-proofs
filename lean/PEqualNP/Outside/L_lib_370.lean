import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_370

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def stepList (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem length_foldl_stepList (gs : List Gate) (xs : List Bool) :
    (gs.foldl stepList xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, stepList, List.length_append, List.length_cons, List.length_nil]
    omega

theorem getD_oneEach {n m : ℕ} (u : Fin n) (v : Fin m) (w : ℕ) :
    (oneEach u v).getD w false = (decide (w = u.val) || decide (w = n + v.val)) := by
  simp only [oneEach, List.getD_eq_getElem?_getD]
  by_cases h1 : w < n
  · rw [List.getElem?_append_left (by simp [h1]), List.getElem?_ofFn]
    simp only [h1, dite_true, Option.getD_some]
    have hne : w ≠ n + v.val := by omega
    simp [Fin.ext_iff, hne]
  · by_cases h2 : w < n + m
    · rw [List.getElem?_append_right (by simp; omega)]
      simp only [List.length_ofFn, List.getElem?_ofFn]
      have hsub : w - n < m := by omega
      simp only [hsub, dite_true, Option.getD_some]
      have hne : w ≠ u.val := by omega
      have heq : (w - n = v.val) ↔ (w = n + v.val) := by omega
      simp [Fin.ext_iff, hne, heq]
    · rw [List.getElem?_eq_none (by simp; omega)]
      have hne1 : w ≠ u.val := by omega
      have hne2 : w ≠ n + v.val := by omega
      simp [hne1, hne2]

theorem len_oneEach {n m : ℕ} (u : Fin n) (v : Fin m) : (oneEach u v).length = n + m := by
  simp [oneEach]

noncomputable def remapWire {n n' m m' : ℕ} (e : Fin m → Fin n) (f : Fin m' → Fin n')
    (G : ℕ) (w : ℕ) : ℕ :=
  open Classical in
  if w < n then
    if h : ∃ u : Fin m, (e u).val = w then (Classical.choose h).val else m + m' + G
  else if w < n + n' then
    if h : ∃ v : Fin m', n + (f v).val = w then m + (Classical.choose h).val else m + m' + G
  else
    m + m' + (w - (n + n'))

noncomputable def remapGate {n n' m m' : ℕ} (e : Fin m → Fin n) (f : Fin m' → Fin n')
    (G : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (remapWire e f G)⟩

theorem foldl_remap_eq {n n' m m' : ℕ} (e : Fin m → Fin n) (f : Fin m' → Fin n')
    (he : Function.Injective e) (hf : Function.Injective f) (G : ℕ)
    (gs : List Gate) (acc1 acc2 : List Bool) (k : ℕ)
    (h1 : acc1.length = n + n' + k) (h2 : acc2.length = m + m' + k)
    (hG : k + gs.length ≤ G)
    (hinv : ∀ w, acc1.getD w false = acc2.getD (remapWire e f G w) false) :
    ∀ w, (gs.foldl stepList acc1).getD w false =
      ((gs.map (remapGate e f G)).foldl stepList acc2).getD (remapWire e f G w) false := by
  induction gs generalizing acc1 acc2 k with
  | nil => exact hinv
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons]
    have hval : g.op.eval (g.inputs.map fun i => acc1.getD i false) =
        (remapGate e f G g).op.eval ((remapGate e f G g).inputs.map fun i => acc2.getD i false) := by
      simp only [remapGate, List.map_map, Function.comp_def]
      congr 1
      apply List.map_congr_left
      intro i _
      exact hinv i
    apply ih (stepList acc1 g) (stepList acc2 (remapGate e f G g)) (k + 1)
    · simp only [stepList, List.length_append, List.length_cons, List.length_nil]; omega
    · simp only [stepList, List.length_append, List.length_cons, List.length_nil]; omega
    · simp only [List.length_cons] at hG; omega
    · intro w
      by_cases hw_lt : w < n + n' + k
      · have hr_lt : remapWire e f G w < m + m' + k ∨ m + m' + G ≤ remapWire e f G w := by
          unfold remapWire
          split_ifs with c1 c2 c3 c4
          · left; have := (Classical.choose c2).isLt; omega
          · right; omega
          · left; have := (Classical.choose c4).isLt; omega
          · right; omega
          · left; omega
        have hl : (stepList acc1 g).getD w false = acc1.getD w false := by
          simp only [stepList, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : w < acc1.length)]
        rw [hl, hinv w]
        rcases hr_lt with hlt | hge
        · simp only [stepList, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : remapWire e f G w < acc2.length)]
        · have hstep_len : (stepList acc2 (remapGate e f G g)).length = m + m' + k + 1 := by
            simp only [stepList, List.length_append, List.length_cons, List.length_nil]; omega
          simp only [List.length_cons] at hG
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : acc2.length ≤ remapWire e f G w)]
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : (stepList acc2 (remapGate e f G g)).length ≤ remapWire e f G w)]
      · by_cases hw_eq : w = n + n' + k
        · subst hw_eq
          have hr_eq : remapWire e f G (n + n' + k) = m + m' + k := by
            unfold remapWire
            have c1 : ¬ (n + n' + k < n) := by omega
            have c2 : ¬ (n + n' + k < n + n') := by omega
            simp only [c1, c2, ite_false]
            omega
          rw [hr_eq]
          simp only [stepList, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega : acc1.length ≤ n + n' + k), h1, Nat.sub_self]
          rw [List.getElem?_append_right (by omega : acc2.length ≤ m + m' + k), h2, Nat.sub_self]
          simp only [List.getElem?_cons_zero, Option.getD_some]
          simpa only [List.getD_eq_getElem?_getD] using hval
        · have hr_gt : m + m' + k + 1 ≤ remapWire e f G w := by
            unfold remapWire
            have c1 : ¬ (w < n) := by omega
            have c2 : ¬ (w < n + n') := by omega
            simp only [c1, c2, ite_false]
            omega
          have h1s : (stepList acc1 g).length = n + n' + k + 1 := by
            simp only [stepList, List.length_append, List.length_cons, List.length_nil]; omega
          have h2s : (stepList acc2 (remapGate e f G g)).length = m + m' + k + 1 := by
            simp only [stepList, List.length_append, List.length_cons, List.length_nil]; omega
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]

theorem main_proof : ∀ (n n' m m' s : ℕ) (A : Fin n → Fin n' → Bool) (e : Fin m → Fin n) (f : Fin m' → Fin n'),
    Function.Injective e → Function.Injective f → RepSizeAtMost A s →
    RepSizeAtMost (fun u v => A (e u) (f v)) s := by
  intro n n' m m' s A e f he hf ⟨C, hmon, hsz, hrep⟩
  let G := C.gates.length
  let C' : Circuit := ⟨C.gates.map (remapGate e f G), remapWire e f G C.output⟩
  refine ⟨C', ?_, ?_, ?_⟩
  · intro g hg
    simp only [C', List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    have hm := hmon g0 hg0
    exact ⟨hm.1, by simp [remapGate, hm.2]⟩
  · simpa [C', Circuit.size] using hsz
  · intro u v
    have hbase : ∀ w, (oneEach (e u) (f v)).getD w false =
        (oneEach u v).getD (remapWire e f G w) false := by
      intro w
      rw [getD_oneEach, getD_oneEach]
      unfold remapWire
      by_cases h1 : w < n
      · simp only [h1, ite_true]
        split_ifs with hex
        · have hspec : (e (Classical.choose hex)).val = w := Classical.choose_spec hex
          have hne1 : w ≠ n + (f v).val := by omega
          have hne2 : (Classical.choose hex).val ≠ m + v.val := by
            have := (Classical.choose hex).isLt; omega
          simp only [hne1, hne2, decide_false, Bool.or_false]
          have hiff : w = (e u).val ↔ (Classical.choose hex).val = u.val := by
            constructor
            · intro h; rw [← hspec] at h; exact congrArg Fin.val (he (Fin.ext h))
            · intro h; rw [← hspec, Fin.ext h]
          simp [hiff]
        · have hne1 : w ≠ (e u).val := fun h => hex ⟨u, h.symm⟩
          have hne2 : w ≠ n + (f v).val := by omega
          have hne3 : m + m' + G ≠ u.val := by have := u.isLt; omega
          have hne4 : m + m' + G ≠ m + v.val := by have := v.isLt; omega
          simp [hne1, hne2, hne3, hne4]
      · simp only [h1, ite_false]
        by_cases h2 : w < n + n'
        · simp only [h2, ite_true]
          split_ifs with hex
          · have hspec : n + (f (Classical.choose hex)).val = w := Classical.choose_spec hex
            have hne1 : w ≠ (e u).val := by have := (e u).isLt; omega
            have hne2 : m + (Classical.choose hex).val ≠ u.val := by have := u.isLt; omega
            simp only [hne1, hne2, decide_false, Bool.false_or]
            have hiff : w = n + (f v).val ↔ m + (Classical.choose hex).val = m + v.val := by
              constructor
              · intro h
                have hfv : (f (Classical.choose hex)).val = (f v).val := by omega
                have := hf (Fin.ext hfv)
                simp [this]
              · intro h
                have hv : Classical.choose hex = v := Fin.ext (by omega)
                rw [← hspec, hv]
            simp [hiff]
          · have hne1 : w ≠ (e u).val := by have := (e u).isLt; omega
            have hne2 : w ≠ n + (f v).val := fun h => hex ⟨v, h.symm⟩
            have hne3 : m + m' + G ≠ u.val := by have := u.isLt; omega
            have hne4 : m + m' + G ≠ m + v.val := by have := v.isLt; omega
            simp [hne1, hne2, hne3, hne4]
        · simp only [h2, ite_false]
          have hne1 : w ≠ (e u).val := by have := (e u).isLt; omega
          have hne2 : w ≠ n + (f v).val := by have := (f v).isLt; omega
          have hne3 : m + m' + (w - (n + n')) ≠ u.val := by have := u.isLt; omega
          have hne4 : m + m' + (w - (n + n')) ≠ m + v.val := by have := v.isLt; omega
          simp [hne1, hne2, hne3, hne4]
    have hfold := foldl_remap_eq e f he hf G C.gates (oneEach (e u) (f v)) (oneEach u v) 0
      (by simp [len_oneEach]) (by simp [len_oneEach]) (by simp [G]) hbase C.output
    have hev : C'.eval (oneEach u v) = C.eval (oneEach (e u) (f v)) := hfold.symm
    rw [hev, hrep]

end PEqualNP.Outside.L_lib_370

theorem PEqualNP.Outside.L_lib_370 : (∀ (n n' m m' s : ℕ) (A : Fin n → Fin n' → Bool) (e : Fin m → Fin n) (f : Fin m' → Fin n'), Function.Injective e → Function.Injective f → PEqualNP.Represents.RepSizeAtMost A s → PEqualNP.Represents.RepSizeAtMost (fun u v => A (e u) (f v)) s) := by
  exact PEqualNP.Outside.L_lib_370.main_proof
