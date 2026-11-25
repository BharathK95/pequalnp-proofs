import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17164

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.Represents

def stepList (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def wireVal (C : Circuit) (xs : List Bool) (w : ℕ) : Bool :=
  (C.wires xs).getD w false

theorem length_foldl_stepList (gs : List Gate) (xs : List Bool) :
    (gs.foldl stepList xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, stepList, List.length_append, List.length_cons, List.length_nil]
    omega

theorem getD_foldl_stepList_lt (gs : List Gate) (xs : List Bool) (w : ℕ) (hw : w < xs.length) :
    (gs.foldl stepList xs).getD w false = xs.getD w false := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : w < (stepList xs g).length := by
      simp only [stepList, List.length_append, List.length_cons, List.length_nil]; omega
    rw [ih (stepList xs g) hlt]
    simp only [stepList, List.getD_eq_getElem?_getD, List.getElem?_append_left hw]

theorem wireVal_lt (C : Circuit) (xs : List Bool) (w : ℕ) (hw : w < xs.length) :
    wireVal C xs w = xs.getD w false :=
  getD_foldl_stepList_lt C.gates xs w hw

theorem wireVal_ge (C : Circuit) (xs : List Bool) (w : ℕ) (hw : xs.length + C.gates.length ≤ w) :
    wireVal C xs w = false := by
  change (C.gates.foldl stepList xs).getD w false = false
  have hlen : (C.gates.foldl stepList xs).length = xs.length + C.gates.length :=
    length_foldl_stepList C.gates xs
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

theorem wireVal_gate_eq (C : Circuit) (xs : List Bool) (j : ℕ) (hj : j < C.gates.length)
    (hback : ∀ i ∈ (gateAt C j).inputs, i < xs.length + j) :
    wireVal C xs (xs.length + j) =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => wireVal C xs i) := by
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
    have h1 := List.take_append_drop j C.gates
    have h2 : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [← h2, h1]
  have hgate : gateAt C j = C.gates[j] := by
    simp [gateAt, List.getD_eq_getElem?_getD, hj]
  rw [hgate] at hback ⊢
  let pre := (C.gates.take j).foldl stepList xs
  have hpre_len : pre.length = xs.length + j := by
    simp [pre, length_foldl_stepList, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have hw : C.wires xs = (C.gates.drop (j + 1)).foldl stepList (stepList pre C.gates[j]) := by
    change C.gates.foldl stepList xs = _
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  have hlt_step : xs.length + j < (stepList pre C.gates[j]).length := by
    simp only [stepList, List.length_append, List.length_cons, List.length_nil, hpre_len]; omega
  have hval : wireVal C xs (xs.length + j) = (stepList pre C.gates[j]).getD (xs.length + j) false := by
    unfold wireVal
    rw [hw]
    exact getD_foldl_stepList_lt _ _ _ hlt_step
  rw [hval]
  have hlast : (stepList pre C.gates[j]).getD (xs.length + j) false =
      C.gates[j].op.eval (C.gates[j].inputs.map fun i => pre.getD i false) := by
    simp only [stepList, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega), hpre_len, Nat.sub_self]
    simp
  rw [hlast]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi_lt : i < pre.length := by rw [hpre_len]; exact hback i hi
  have hi_step : i < (stepList pre C.gates[j]).length := by
    simp only [stepList, List.length_append, List.length_cons, List.length_nil]; omega
  unfold wireVal
  rw [hw, getD_foldl_stepList_lt _ _ _ hi_step]
  simp only [stepList, List.getD_eq_getElem?_getD, List.getElem?_append_left hi_lt]

theorem gateOp_eval_mono (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (a b : List Bool) (hlen : a.length = b.length)
    (hle : ∀ i < a.length, a.getD i false = true → b.getD i false = true) :
    op.eval a = true → op.eval b = true := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl
  · intro ha
    simp only [GateOp.eval, List.all_eq_true, id_eq] at ha ⊢
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    have hi_a : i < a.length := by omega
    have hai : a.getD i false = true := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi_a, Option.getD_some]
      exact ha a[i] (List.getElem_mem hi_a)
    have hbi := hle i hi_a hai
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] using hbi
  · intro ha
    simp only [GateOp.eval, List.any_eq_true, id_eq] at ha ⊢
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hx
    have hi_b : i < b.length := by omega
    have hai : a.getD i false = true := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, hget]
    have hbi := hle i hi hai
    refine ⟨b[i], List.getElem_mem hi_b, ?_⟩
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi_b] using hbi

theorem wireVal_mono (C : Circuit) (hmono : Monotone2 C) (xs ys : List Bool)
    (hlen : xs.length = ys.length)
    (hle : ∀ i < xs.length, xs.getD i false = true → ys.getD i false = true) :
    ∀ w, wireVal C xs w = true → wireVal C ys w = true := by
  have hstep : ∀ (gs : List Gate), (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) →
      ∀ (a b : List Bool), a.length = b.length →
      (∀ w, a.getD w false = true → b.getD w false = true) →
      ∀ w, (gs.foldl stepList a).getD w false = true → (gs.foldl stepList b).getD w false = true := by
    intro gs hgs
    induction gs with
    | nil => intro a b _ hab w hw; exact hab w hw
    | cons g gs ih =>
      intro a b hab_len hab w hw
      simp only [List.foldl_cons] at hw ⊢
      apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) (stepList a g) (stepList b g)
      · simp [stepList, hab_len]
      · intro k hk
        by_cases hlt : k < a.length
        · have hlt' : k < b.length := by omega
          simp only [stepList, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt] at hk
          simp only [stepList, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt']
          exact hab k (by simpa [List.getD_eq_getElem?_getD] using hk)
        · by_cases heq : k = a.length
          · subst heq
            simp only [stepList, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
              Nat.sub_self, List.getElem?_cons_zero, Option.getD_some] at hk
            simp only [stepList, List.getD_eq_getElem?_getD, hab_len,
              List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero,
              Option.getD_some]
            apply gateOp_eval_mono g.op (hgs g List.mem_cons_self)
              (g.inputs.map fun i => a.getD i false) (g.inputs.map fun i => b.getD i false) (by simp)
            · intro idx hidx hget
              simp only [List.length_map] at hidx
              simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
                List.getElem?_eq_getElem hidx, Option.map_some, Option.getD_some] at hget ⊢
              exact hab g.inputs[idx] (by simpa [List.getD_eq_getElem?_getD] using hget)
            · simpa [List.getD_eq_getElem?_getD] using hk
          · have hge : (stepList a g).length ≤ k := by simp [stepList]; omega
            simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge] at hk
      · exact hw
  apply hstep C.gates (fun g hg => (hmono g hg).1) xs ys hlen
  intro w hw
  by_cases hlt : w < xs.length
  · exact hle w hlt hw
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hlt)] at hw

theorem wireVal_allFalse (C : Circuit) (N : ℕ) (hmono : Monotone2 C)
    (hwf : ∀ j < C.gates.length, (gateAt C j).inputs.length = 2 ∧
      (gateAt C j).inputs.Nodup ∧ ∀ i ∈ (gateAt C j).inputs, i < N + j)
    (xs : List Bool) (hlen : xs.length = N) (hzero : ∀ i < N, xs.getD i false = false) :
    ∀ w, wireVal C xs w = false := by
  have hstep : ∀ (k : ℕ) (hk : k ≤ C.gates.length),
      ∀ w, ((C.gates.take k).foldl stepList xs).getD w false = false := by
    intro k
    induction k with
    | zero =>
      intro _ w
      simp only [List.take_zero, List.foldl_nil]
      by_cases hlt : w < N
      · exact hzero w hlt
      · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : xs.length ≤ w)]
    | succ k ih =>
      intro hk w
      have hk_lt : k < C.gates.length := by omega
      have htake : C.gates.take (k + 1) = C.gates.take k ++ [C.gates[k]] := List.take_succ_eq_append_getElem hk_lt
      rw [htake, List.foldl_append, List.foldl_cons, List.foldl_nil]
      set pre := (C.gates.take k).foldl stepList xs
      have hpre : ∀ u, pre.getD u false = false := ih (by omega)
      by_cases hlt : w < pre.length
      · rw [stepList, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
        simpa [List.getD_eq_getElem?_getD] using hpre w
      · by_cases heq : w = pre.length
        · subst heq
          rw [stepList, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self]
          simp only [List.getElem?_cons_zero, Option.getD_some]
          have hg_mem : C.gates[k] ∈ C.gates := List.getElem_mem hk_lt
          have hg_at : gateAt C k = C.gates[k] := by simp [gateAt, List.getD_eq_getElem?_getD, hk_lt]
          have hlen2 : C.gates[k].inputs.length = 2 := by rw [← hg_at]; exact (hwf k hk_lt).1
          obtain ⟨a, b, hab⟩ : ∃ a b, C.gates[k].inputs = [a, b] := by
            rcases h : C.gates[k].inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;> simp [h] at hlen2
            exact ⟨a, b, rfl⟩
          have hop := (hmono C.gates[k] hg_mem).1
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
          rcases hop with hop | hop <;> simp [hop, hab, GateOp.eval, ← List.getD_eq_getElem?_getD, hpre]
        · have hge : (stepList pre C.gates[k]).length ≤ w := by simp [stepList]; omega
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]; rfl
  intro w
  change (C.gates.foldl stepList xs).getD w false = false
  have h := hstep C.gates.length (le_refl _) w
  simpa [List.take_length] using h

theorem cones_length (N : ℕ) (gs : List Gate) (acc : List (List ℕ)) :
    (gs.foldl (coneStep N) acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, coneStep, List.length_append, List.length_cons, List.length_nil]
    omega

theorem getD_foldl_coneStep_lt (N : ℕ) (gs : List Gate) (acc : List (List ℕ)) (j : ℕ) (hj : j < acc.length) :
    (gs.foldl (coneStep N) acc).getD j [] = acc.getD j [] := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : j < (coneStep N acc g).length := by
      simp only [coneStep, List.length_append, List.length_cons, List.length_nil]; omega
    rw [ih (coneStep N acc g) hlt]
    simp only [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

theorem cones_getD_eq (N : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    (cones N C).getD j [] =
      ((gateAt C j).inputs.filter (fun w => decide (N ≤ w ∧ w < N + j))).flatMap
        (fun w => (w - N) :: (cones N C).getD (w - N) []) := by
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
    have h1 := List.take_append_drop j C.gates
    have h2 : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [← h2, h1]
  have hgate : gateAt C j = C.gates[j] := by simp [gateAt, List.getD_eq_getElem?_getD, hj]
  rw [hgate]
  let pre := (C.gates.take j).foldl (coneStep N) []
  have hpre_len : pre.length = j := by
    simp [pre, cones_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have hc : cones N C = (C.gates.drop (j + 1)).foldl (coneStep N) (coneStep N pre C.gates[j]) := by
    unfold cones
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  have hlt_step : j < (coneStep N pre C.gates[j]).length := by
    simp only [coneStep, List.length_append, List.length_cons, List.length_nil, hpre_len]; omega
  rw [hc, getD_foldl_coneStep_lt _ _ _ _ hlt_step]
  simp only [coneStep, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by omega), hpre_len, Nat.sub_self]
  simp only [List.getElem?_cons_zero, Option.getD_some]
  apply List.flatMap_congr
  intro w hw
  simp only [List.mem_filter, decide_eq_true_eq] at hw
  have hsub : w - N < pre.length := by rw [hpre_len]; omega
  have hsub_s : w - N < (coneStep N pre C.gates[j]).length := by
    simp only [coneStep, List.length_append, List.length_cons, List.length_nil]; omega
  congr 1
  have h1 := getD_foldl_coneStep_lt N (C.gates.drop (j + 1)) (coneStep N pre C.gates[j]) (w - N) hsub_s
  simp only [coneStep, hpre_len, List.getD_eq_getElem?_getD] at h1
  rw [h1, List.getElem?_append_left hsub]

theorem inCone_iff (N : ℕ) (C : Circuit) (i j : ℕ) (hj : j < C.gates.length) :
    InCone N C i j ↔
      ∃ w ∈ (gateAt C j).inputs, N ≤ w ∧ w < N + j ∧ (i = w - N ∨ InCone N C i (w - N)) := by
  unfold InCone
  rw [cones_getD_eq N C j hj]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hw1, hw2, hw3⟩, h4⟩
    exact ⟨w, hw1, hw2, hw3, h4⟩
  · rintro ⟨w, hw1, hw2, hw3, h4⟩
    exact ⟨w, ⟨hw1, hw2, hw3⟩, h4⟩

theorem inCone_lt (N : ℕ) (C : Circuit) : ∀ j < C.gates.length, ∀ i, InCone N C i j → i < j := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj i hij
    rw [inCone_iff N C i j hj] at hij
    obtain ⟨w, _, hw1, hw2, h4 | h4⟩ := hij
    · omega
    · have hlt : w - N < j := by omega
      have hsub := ih (w - N) hlt (by omega) i h4
      omega

theorem inCone_trans (N : ℕ) (C : Circuit) :
    ∀ k < C.gates.length, ∀ i j, InCone N C i j → InCone N C j k → InCone N C i k := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hk i j hij hjk
    rw [inCone_iff N C j k hk] at hjk
    obtain ⟨w, hwin, hw1, hw2, rfl | hrec⟩ := hjk
    · rw [inCone_iff N C i k hk]
      exact ⟨w, hwin, hw1, hw2, Or.inr hij⟩
    · have hsub := ih (w - N) (by omega) (by omega) i j hij hrec
      rw [inCone_iff N C i k hk]
      exact ⟨w, hwin, hw1, hw2, Or.inr hsub⟩

def inSub (N : ℕ) (C : Circuit) (root : ℕ) (w : ℕ) : Prop :=
  w ∈ (gateAt C root).inputs ∨ ∃ i, InCone N C i root ∧ w ∈ (gateAt C i).inputs

theorem inSub_of_inCone (N : ℕ) (C : Circuit) (i root w : ℕ) (hroot : root < C.gates.length)
    (hi : InCone N C i root) (hw : inSub N C i w) : inSub N C root w := by
  rcases hw with hw | ⟨k, hki, hwk⟩
  · exact Or.inr ⟨i, hi, hw⟩
  · exact Or.inr ⟨k, inCone_trans N C root hroot k i hki hi, hwk⟩

theorem inSub_of_inCone_wire (N : ℕ) (C : Circuit) :
    ∀ r < C.gates.length, ∀ k, InCone N C k r → inSub N C r (N + k) := by
  intro r
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    intro hr k hkr
    rw [inCone_iff N C k r hr] at hkr
    obtain ⟨w, hwin, hw1, hw2, h4 | h4⟩ := hkr
    · left
      have : w = N + k := by omega
      rwa [← this]
    · have hsub := ih (w - N) (by omega) (by omega) k h4
      have hcw : InCone N C (w - N) r := (inCone_iff N C (w - N) r hr).mpr ⟨w, hwin, hw1, hw2, Or.inl rfl⟩
      exact inSub_of_inCone N C (w - N) r (N + k) hr hcw hsub

theorem inSub_unique_reader (N : ℕ) (C : Circuit) (g : ℕ)
    (hro : ∀ w, inSub N C g w → ((Finset.range C.gates.length).filter fun k => w ∈ (gateAt C k).inputs).card = 1)
    (w k1 k2 : ℕ) (hw : inSub N C g w)
    (hk1 : k1 < C.gates.length) (h1 : w ∈ (gateAt C k1).inputs)
    (hk2 : k2 < C.gates.length) (h2 : w ∈ (gateAt C k2).inputs) : k1 = k2 := by
  have hcard := hro w hw
  have hm1 : k1 ∈ (Finset.range C.gates.length).filter (fun k => w ∈ (gateAt C k).inputs) := by
    simp [hk1, h1]
  have hm2 : k2 ∈ (Finset.range C.gates.length).filter (fun k => w ∈ (gateAt C k).inputs) := by
    simp [hk2, h2]
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcard
  rw [hx, Finset.mem_singleton] at hm1 hm2
  omega

def wireIn (N : ℕ) (C : Circuit) (u w : ℕ) : Prop :=
  w = u ∨ (N ≤ u ∧ inSub N C (u - N) w)

theorem wireIn_disjoint (N : ℕ) (C : Circuit) (g : ℕ) (hg : g < C.gates.length)
    (hwf : ∀ j < C.gates.length, (gateAt C j).inputs.length = 2 ∧
      (gateAt C j).inputs.Nodup ∧ ∀ i ∈ (gateAt C j).inputs, i < N + j)
    (hro : ∀ w, inSub N C g w → ((Finset.range C.gates.length).filter fun k => w ∈ (gateAt C k).inputs).card = 1)
    (j : ℕ) (hjg : j = g ∨ InCone N C j g) (a b : ℕ)
    (ha : a ∈ (gateAt C j).inputs) (hb : b ∈ (gateAt C j).inputs) (hab : a ≠ b) :
    ∀ w, wireIn N C a w → wireIn N C b w → False := by
  have hj : j < C.gates.length := by
    rcases hjg with rfl | h
    · exact hg
    · exact Nat.lt_trans (inCone_lt N C g hg j h) hg
  have ha_lt : a < N + j := (hwf j hj).2.2 a ha
  have hb_lt : b < N + j := (hwf j hj).2.2 b hb
  have inSub_of_j : ∀ w, inSub N C j w → inSub N C g w := by
    intro w hw
    rcases hjg with rfl | h
    · exact hw
    · exact inSub_of_inCone N C j g w hg h hw
  have inSub_a_of_in : ∀ w, N ≤ a → inSub N C (a - N) w → inSub N C g w := by
    intro w haN hwa
    have hca : InCone N C (a - N) j := (inCone_iff N C (a - N) j hj).mpr ⟨a, ha, haN, ha_lt, Or.inl rfl⟩
    exact inSub_of_j w (inSub_of_inCone N C (a - N) j w hj hca hwa)
  have hmain : ∀ d w, d = N + j - w → wireIn N C a w → wireIn N C b w → False := by
    intro d
    induction d using Nat.strong_induction_on with
    | ind d ih =>
      intro w hd hwa hwb
      rcases hwa with hwa_eq | ⟨haN, hsa⟩
      · subst hwa_eq
        rcases hwb with hEq | ⟨hbN, hsb⟩
        · exact hab hEq
        · have hw_in : inSub N C g w := inSub_of_j w (Or.inl ha)
          rcases hsb with hsb | ⟨k, hkb, hwk⟩
          · have hk_lt : b - N < C.gates.length := by omega
            have heq := inSub_unique_reader N C g hro w j (b - N) hw_in hj ha hk_lt hsb
            omega
          · have hk_lt : k < b - N := inCone_lt N C (b - N) (by omega) k hkb
            have heq := inSub_unique_reader N C g hro w j k hw_in hj ha (by omega) hwk
            omega
      · rcases hwb with hwb_eq | ⟨hbN, hsb⟩
        · subst hwb_eq
          have hw_in : inSub N C g w := inSub_of_j w (Or.inl hb)
          rcases hsa with hsa | ⟨k, hka, hwk⟩
          · have hk_lt : a - N < C.gates.length := by omega
            have heq := inSub_unique_reader N C g hro w j (a - N) hw_in hj hb hk_lt hsa
            omega
          · have hk_lt : k < a - N := inCone_lt N C (a - N) (by omega) k hka
            have heq := inSub_unique_reader N C g hro w j k hw_in hj hb (by omega) hwk
            omega
        · have hw_in : inSub N C g w := inSub_a_of_in w haN hsa
          have get_reader : ∀ (u : ℕ), u < N + j → N ≤ u → inSub N C (u - N) w →
              ∃ k, (k = u - N ∨ InCone N C k (u - N)) ∧ k < C.gates.length ∧ w ∈ (gateAt C k).inputs ∧ w < N + k := by
            intro u hu huN hsu
            rcases hsu with hsu | ⟨k, hku, hwk⟩
            · refine ⟨u - N, Or.inl rfl, by omega, hsu, ?_⟩
              have := (hwf (u - N) (by omega)).2.2 w hsu
              omega
            · have hk_lt := inCone_lt N C (u - N) (by omega) k hku
              exact ⟨k, Or.inr hku, by omega, hwk, (hwf k (by omega)).2.2 w hwk⟩
          obtain ⟨k1, hk1_pos, hk1_lt, hk1_in, hw_lt1⟩ := get_reader a ha_lt haN hsa
          obtain ⟨k2, hk2_pos, hk2_lt, hk2_in, _⟩ := get_reader b hb_lt hbN hsb
          have hk_eq := inSub_unique_reader N C g hro w k1 k2 hw_in hk1_lt hk1_in hk2_lt hk2_in
          subst hk_eq
          have hk1_lt_j : k1 < j := by
            rcases hk1_pos with rfl | hc
            · omega
            · exact Nat.lt_trans (inCone_lt N C (a - N) (by omega) k1 hc) (by omega)
          have hwa' : wireIn N C a (N + k1) := by
            rcases hk1_pos with h1 | h1
            · left; omega
            · right; exact ⟨haN, inSub_of_inCone_wire N C (a - N) (by omega) k1 h1⟩
          have hwb' : wireIn N C b (N + k1) := by
            rcases hk2_pos with h2 | h2
            · left; omega
            · right; exact ⟨hbN, inSub_of_inCone_wire N C (b - N) (by omega) k1 h2⟩
          exact ih (N + j - (N + k1)) (by omega) (N + k1) rfl hwa' hwb'
  intro w hwa hwb
  exact hmain (N + j - w) w rfl hwa hwb

theorem wireVal_eq_of_wireIn (N : ℕ) (C : Circuit)
    (hwf : ∀ j < C.gates.length, (gateAt C j).inputs.length = 2 ∧
      (gateAt C j).inputs.Nodup ∧ ∀ i ∈ (gateAt C j).inputs, i < N + j)
    (xs ys : List Bool) (hx : xs.length = N) (hy : ys.length = N) :
    ∀ u, u < N + C.gates.length →
    (∀ w < N, wireIn N C u w → xs.getD w false = ys.getD w false) →
    wireVal C xs u = wireVal C ys u := by
  intro u
  induction u using Nat.strong_induction_on with
  | ind u ih =>
    intro hu hag
    by_cases hlt : u < N
    · rw [wireVal_lt C xs u (by omega), wireVal_lt C ys u (by omega)]
      exact hag u hlt (Or.inl rfl)
    · have hj : u - N < C.gates.length := by omega
      have hu_eq : u = N + (u - N) := by omega
      have hx_eq : u = xs.length + (u - N) := by omega
      have hy_eq : u = ys.length + (u - N) := by omega
      have hback := (hwf (u - N) hj).2.2
      conv_lhs => rw [hx_eq]
      conv_rhs => rw [hy_eq]
      rw [wireVal_gate_eq C xs (u - N) hj (by simpa [hx] using hback)]
      rw [wireVal_gate_eq C ys (u - N) hj (by simpa [hy] using hback)]
      congr 1
      apply List.map_congr_left
      intro v hv
      have hv_lt : v < N + (u - N) := hback v hv
      apply ih v (by omega) (by omega)
      intro w hw hvw
      apply hag w hw
      right
      refine ⟨by omega, ?_⟩
      rcases hvw with rfl | ⟨hvN, hsv⟩
      · exact Or.inl hv
      · have hcv : InCone N C (v - N) (u - N) :=
          (inCone_iff N C (v - N) (u - N) hj).mpr ⟨v, hv, hvN, hv_lt, Or.inl rfl⟩
        exact inSub_of_inCone N C (v - N) (u - N) w hj hcv hsv

theorem wireVal_false_of_wireIn_false (N : ℕ) (C : Circuit) (hmono : Monotone2 C)
    (hwf : ∀ j < C.gates.length, (gateAt C j).inputs.length = 2 ∧
      (gateAt C j).inputs.Nodup ∧ ∀ i ∈ (gateAt C j).inputs, i < N + j)
    (xs : List Bool) (hx : xs.length = N) (u : ℕ) (hu : u < N + C.gates.length)
    (hzero : ∀ w < N, wireIn N C u w → xs.getD w false = false) :
    wireVal C xs u = false := by
  let zs := List.replicate N false
  have hz_len : zs.length = N := by simp [zs]
  have hz_all : ∀ w < N, zs.getD w false = false := by
    intro w hw; simp [zs, List.getD_eq_getElem?_getD, hw]
  have heq : wireVal C xs u = wireVal C zs u := by
    apply wireVal_eq_of_wireIn N C hwf xs zs hx hz_len u hu
    intro w hw huw
    rw [hzero w hw huw, hz_all w hw]
  rw [heq]
  exact wireVal_allFalse C N hmono hwf zs hz_len hz_all u

theorem eval_mono_outside_and_g (N : ℕ) (C : Circuit) (g : ℕ) (hg : g < C.gates.length)
    (hmono : Monotone2 C)
    (hwf : ∀ j < C.gates.length, (gateAt C j).inputs.length = 2 ∧
      (gateAt C j).inputs.Nodup ∧ ∀ i ∈ (gateAt C j).inputs, i < N + j)
    (hro : ∀ w, inSub N C g w → ((Finset.range C.gates.length).filter fun k => w ∈ (gateAt C k).inputs).card = 1)
    (xs ys : List Bool) (hx : xs.length = N) (hy : ys.length = N)
    (hout : ∀ w < N, ¬ inSub N C g w → xs.getD w false = true → ys.getD w false = true)
    (hg_le : wireVal C xs (N + g) = true → wireVal C ys (N + g) = true) :
    ∀ w, ¬ inSub N C g w → wireVal C xs w = true → wireVal C ys w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwnot hval
    by_cases hlt : w < N
    · rw [wireVal_lt C xs w (by omega)] at hval
      rw [wireVal_lt C ys w (by omega)]
      exact hout w hlt hwnot hval
    · by_cases hge : N + C.gates.length ≤ w
      · rw [wireVal_ge C xs w (by omega)] at hval
        simp at hval
      · have hj : w - N < C.gates.length := by omega
        by_cases heqg : w - N = g
        · have hw_eq : w = N + g := by omega
          rw [hw_eq] at hval ⊢
          exact hg_le hval
        · have hnotcone : ¬ InCone N C (w - N) g := by
            intro hc
            have := inSub_of_inCone_wire N C g hg (w - N) hc
            have hw_eq : w = N + (w - N) := by omega
            rw [← hw_eq] at this
            exact hwnot this
          have hback := (hwf (w - N) hj).2.2
          have hx_eq : w = xs.length + (w - N) := by omega
          have hy_eq : w = ys.length + (w - N) := by omega
          rw [hx_eq, wireVal_gate_eq C xs (w - N) hj (by simpa [hx] using hback)] at hval
          rw [hy_eq, wireVal_gate_eq C ys (w - N) hj (by simpa [hy] using hback)]
          have hg_mem : gateAt C (w - N) ∈ C.gates := by
            simp [gateAt, List.getD_eq_getElem?_getD, hj, List.getElem_mem]
          apply gateOp_eval_mono (gateAt C (w - N)).op (hmono _ hg_mem).1
            ((gateAt C (w - N)).inputs.map fun i => wireVal C xs i)
            ((gateAt C (w - N)).inputs.map fun i => wireVal C ys i) (by simp)
          · intro idx hidx hget
            simp only [List.length_map] at hidx
            simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
              List.getElem?_eq_getElem hidx, Option.map_some, Option.getD_some] at hget ⊢
            let v := (gateAt C (w - N)).inputs[idx]
            have hv_mem : v ∈ (gateAt C (w - N)).inputs := List.getElem_mem hidx
            have hv_lt : v < w := by have := hback v hv_mem; omega
            have hv_not : ¬ inSub N C g v := by
              intro hvin
              rcases hvin with hvg | ⟨i, hig, hvi⟩
              · have := inSub_unique_reader N C g hro v (w - N) g (Or.inl hvg) hj hv_mem hg hvg
                exact heqg this
              · have hi_lt := Nat.lt_trans (inCone_lt N C g hg i hig) hg
                have := inSub_unique_reader N C g hro v (w - N) i (Or.inr ⟨i, hig, hvi⟩) hj hv_mem hi_lt hvi
                subst this
                exact hnotcone hig
            exact ih v hv_lt hv_not hget
          · exact hval

theorem eval_eq_outside_and_g (N : ℕ) (C : Circuit) (g : ℕ) (hg : g < C.gates.length)
    (hmono : Monotone2 C)
    (hwf : ∀ j < C.gates.length, (gateAt C j).inputs.length = 2 ∧
      (gateAt C j).inputs.Nodup ∧ ∀ i ∈ (gateAt C j).inputs, i < N + j)
    (hro : ∀ w, inSub N C g w → ((Finset.range C.gates.length).filter fun k => w ∈ (gateAt C k).inputs).card = 1)
    (xs ys : List Bool) (hx : xs.length = N) (hy : ys.length = N)
    (hout : ∀ w < N, ¬ inSub N C g w → xs.getD w false = ys.getD w false)
    (hg_eq : wireVal C xs (N + g) = wireVal C ys (N + g))
    (w : ℕ) (hwnot : ¬ inSub N C g w) :
    wireVal C xs w = wireVal C ys w := by
  cases hx_v : wireVal C xs w
  · cases hy_v : wireVal C ys w
    · rfl
    · have := eval_mono_outside_and_g N C g hg hmono hwf hro ys xs hy hx
        (fun i hi hni h => by rw [hout i hi hni]; exact h)
        (fun h => by rw [hg_eq]; exact h) w hwnot hy_v
      rw [hx_v] at this; simp at this
  · exact (eval_mono_outside_and_g N C g hg hmono hwf hro xs ys hx hy
      (fun i hi hni h => by rw [← hout i hi hni]; exact h)
      (fun h => by rw [← hg_eq]; exact h) w hwnot hx_v).symm

def rowOnly (n m : ℕ) (u : Fin n) : List Bool :=
  List.ofFn (fun i : Fin n => decide (i = u)) ++ List.replicate m false

def colOnly (n m : ℕ) (v : Fin m) : List Bool :=
  List.replicate n false ++ List.ofFn (fun j : Fin m => decide (j = v))

theorem len_oneEach (n m : ℕ) (u : Fin n) (v : Fin m) : (oneEach u v).length = n + m := by
  simp [oneEach]

theorem len_rowOnly (n m : ℕ) (u : Fin n) : (rowOnly n m u).length = n + m := by
  simp [rowOnly]

theorem len_colOnly (n m : ℕ) (v : Fin m) : (colOnly n m v).length = n + m := by
  simp [colOnly]

theorem getD_oneEach (n m : ℕ) (u : Fin n) (v : Fin m) (w : ℕ) :
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

theorem getD_rowOnly (n m : ℕ) (u : Fin n) (w : ℕ) :
    (rowOnly n m u).getD w false = decide (w = u.val) := by
  simp only [rowOnly, List.getD_eq_getElem?_getD]
  by_cases h1 : w < n
  · rw [List.getElem?_append_left (by simp [h1]), List.getElem?_ofFn]
    simp [h1, Fin.ext_iff]
  · by_cases h2 : w < n + m
    · rw [List.getElem?_append_right (by simp; omega)]
      simp only [List.length_ofFn]
      have hsub : w - n < m := by omega
      rw [List.getElem?_replicate]
      have hne : w ≠ u.val := by omega
      simp [hsub, hne]
    · rw [List.getElem?_eq_none (by simp; omega)]
      have hne : w ≠ u.val := by omega
      simp [hne]

theorem getD_colOnly (n m : ℕ) (v : Fin m) (w : ℕ) :
    (colOnly n m v).getD w false = decide (w = n + v.val) := by
  simp only [colOnly, List.getD_eq_getElem?_getD]
  by_cases h1 : w < n
  · rw [List.getElem?_append_left (by simp [h1]), List.getElem?_replicate]
    have hne : w ≠ n + v.val := by omega
    simp [h1, hne]
  · by_cases h2 : w < n + m
    · rw [List.getElem?_append_right (by simp; omega)]
      simp only [List.length_replicate, List.getElem?_ofFn]
      have hsub : w - n < m := by omega
      have heq : (w - n = v.val) ↔ (w = n + v.val) := by omega
      simp [hsub, Fin.ext_iff, heq]
    · rw [List.getElem?_eq_none (by simp; omega)]
      have hne : w ≠ n + v.val := by omega
      simp [hne]

theorem ro_block_prop (n m : ℕ) (C : Circuit) (g : ℕ) (hg : g < C.gates.length)
    (hmono : Monotone2 C)
    (hwf : ∀ j < C.gates.length, (gateAt C j).inputs.length = 2 ∧
      (gateAt C j).inputs.Nodup ∧ ∀ i ∈ (gateAt C j).inputs, i < n + m + j)
    (hro : ∀ w, inSub (n + m) C g w → ((Finset.range C.gates.length).filter fun k => w ∈ (gateAt C k).inputs).card = 1) :
    ∀ u, u < n + m + C.gates.length →
    (u < n + m ∨ (u - (n + m) = g ∨ InCone (n + m) C (u - (n + m)) g)) →
    (∀ r : Fin n, wireVal C (rowOnly n m r) u = false) →
    (∀ c : Fin m, wireVal C (colOnly n m c) u = false) →
    (∀ (r : Fin n) (c : Fin m), wireVal C (oneEach r c) u = true →
      wireIn (n + m) C u r.val ∧ wireIn (n + m) C u (n + c.val)) ∧
    (∀ (r1 : Fin n) (c1 c2 : Fin m),
      wireVal C (oneEach r1 c1) u = true → wireVal C (oneEach r1 c2) u = true →
      ∀ r : Fin n, wireVal C (oneEach r c1) u = wireVal C (oneEach r c2) u) ∧
    (∀ (r1 r2 : Fin n) (c1 : Fin m),
      wireVal C (oneEach r1 c1) u = true → wireVal C (oneEach r2 c1) u = true →
      ∀ c : Fin m, wireVal C (oneEach r1 c) u = wireVal C (oneEach r2 c) u) := by
  intro u
  induction u using Nat.strong_induction_on with
  | ind u ih =>
    intro hu hpos hrow0 hcol0
    by_cases hlt : u < n + m
    · have hnever : ∀ (r : Fin n) (c : Fin m), wireVal C (oneEach r c) u = false := by
        intro r c
        rw [wireVal_lt C (oneEach r c) u (by rw [len_oneEach]; exact hlt), getD_oneEach]
        by_cases hr : u = r.val
        · have h := hrow0 r
          rw [wireVal_lt C (rowOnly n m r) u (by rw [len_rowOnly]; exact hlt), getD_rowOnly] at h
          simp [hr] at h
        · by_cases hc : u = n + c.val
          · have h := hcol0 c
            rw [wireVal_lt C (colOnly n m c) u (by rw [len_colOnly]; exact hlt), getD_colOnly] at h
            simp [hc] at h
          · simp [hr, hc]
      refine ⟨fun r c h => by simp [hnever] at h,
              fun r1 c1 c2 h => by simp [hnever] at h,
              fun r1 r2 c1 h => by simp [hnever] at h⟩
    · have hjg : u - (n + m) = g ∨ InCone (n + m) C (u - (n + m)) g := by
        rcases hpos with h | h
        · omega
        · exact h
      let j := u - (n + m)
      have hj : j < C.gates.length := by omega
      have hu_eq : u = n + m + j := by omega
      have hlen2 := (hwf j hj).1
      have hnodup := (hwf j hj).2.1
      have hback := (hwf j hj).2.2
      obtain ⟨a, b, hab_list⟩ : ∃ a b, (gateAt C j).inputs = [a, b] := by
        rcases h : (gateAt C j).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;> simp [h] at hlen2
        exact ⟨a, b, rfl⟩
      have hab_ne : a ≠ b := by rw [hab_list] at hnodup; simpa using hnodup
      have ha_mem : a ∈ (gateAt C j).inputs := by rw [hab_list]; simp
      have hb_mem : b ∈ (gateAt C j).inputs := by rw [hab_list]; simp
      have ha_lt : a < u := by have := hback a ha_mem; omega
      have hb_lt : b < u := by have := hback b hb_mem; omega
      have hdisj := wireIn_disjoint (n + m) C g hg hwf hro j hjg a b ha_mem hb_mem hab_ne
      have wireIn_up : ∀ v, v ∈ (gateAt C j).inputs → ∀ w, wireIn (n + m) C v w → wireIn (n + m) C u w := by
        intro v hv w hvw
        right
        refine ⟨by omega, ?_⟩
        rcases hvw with rfl | ⟨hvN, hsv⟩
        · exact Or.inl hv
        · have hv_lt : v < n + m + j := hback v hv
          have hcv : InCone (n + m) C (v - (n + m)) j :=
            (inCone_iff (n + m) C (v - (n + m)) j hj).mpr ⟨v, hv, hvN, hv_lt, Or.inl rfl⟩
          exact inSub_of_inCone (n + m) C (v - (n + m)) j w hj hcv hsv
      have hpos_child : ∀ v, v ∈ (gateAt C j).inputs →
          v < n + m ∨ (v - (n + m) = g ∨ InCone (n + m) C (v - (n + m)) g) := by
        intro v hv
        by_cases hvN : v < n + m
        · exact Or.inl hvN
        · right; right
          have hv_lt : v < n + m + j := hback v hv
          have hcv : InCone (n + m) C (v - (n + m)) j :=
            (inCone_iff (n + m) C (v - (n + m)) j hj).mpr ⟨v, hv, by omega, hv_lt, Or.inl rfl⟩
          rcases hjg with rfl | hcjg
          · exact hcv
          · exact inCone_trans (n + m) C g hg (v - (n + m)) j hcv hcjg
      have hgate_mem : gateAt C j ∈ C.gates := by
        simp [gateAt, List.getD_eq_getElem?_getD, hj, List.getElem_mem]
      have hop := (hmono _ hgate_mem).1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      have heval_gate : ∀ xs, xs.length = n + m →
          wireVal C xs u = ((gateAt C j).op.eval [wireVal C xs a, wireVal C xs b]) := by
        intro xs hxs
        have heq_len : u = xs.length + j := by omega
        conv_lhs => rw [heq_len]
        rw [wireVal_gate_eq C xs j hj (by simpa [hxs] using hback), hab_list]
        rfl
      rcases hop with hop_and | hop_or
      · have eval_and : ∀ xs, xs.length = n + m → wireVal C xs u = (wireVal C xs a && wireVal C xs b) := by
          intro xs hxs
          rw [heval_gate xs hxs, hop_and]
          simp [GateOp.eval]
        have not_both_same : ∀ (r : Fin n) (c : Fin m), wireVal C (oneEach r c) u = true →
            (wireIn (n + m) C a r.val ∧ wireIn (n + m) C b (n + c.val) ∧
             wireVal C (rowOnly n m r) a = true ∧ wireVal C (colOnly n m c) b = true) ∨
            (wireIn (n + m) C b r.val ∧ wireIn (n + m) C a (n + c.val) ∧
             wireVal C (rowOnly n m r) b = true ∧ wireVal C (colOnly n m c) a = true) := by
          intro r c hval
          rw [eval_and _ (len_oneEach n m r c), Bool.and_eq_true] at hval
          obtain ⟨ha1, hb1⟩ := hval
          have ha_non0 : wireIn (n + m) C a r.val ∨ wireIn (n + m) C a (n + c.val) := by
            by_contra hnone
            push Not at hnone
            have hz := wireVal_false_of_wireIn_false (n + m) C hmono hwf (oneEach r c)
              (len_oneEach n m r c) a (by omega) (fun w hw haw => by
                rw [getD_oneEach]
                have h1 : w ≠ r.val := fun heq => hnone.1 (heq ▸ haw)
                have h2 : w ≠ n + c.val := fun heq => hnone.2 (heq ▸ haw)
                simp [h1, h2])
            rw [hz] at ha1; simp at ha1
          have hb_non0 : wireIn (n + m) C b r.val ∨ wireIn (n + m) C b (n + c.val) := by
            by_contra hnone
            push Not at hnone
            have hz := wireVal_false_of_wireIn_false (n + m) C hmono hwf (oneEach r c)
              (len_oneEach n m r c) b (by omega) (fun w hw hbw => by
                rw [getD_oneEach]
                have h1 : w ≠ r.val := fun heq => hnone.1 (heq ▸ hbw)
                have h2 : w ≠ n + c.val := fun heq => hnone.2 (heq ▸ hbw)
                simp [h1, h2])
            rw [hz] at hb1; simp at hb1
          rcases ha_non0 with har | hac
          · have hbr_not : ¬ wireIn (n + m) C b r.val := fun hbr => hdisj r.val har hbr
            have hbc : wireIn (n + m) C b (n + c.val) := hb_non0.resolve_left hbr_not
            have hac_not : ¬ wireIn (n + m) C a (n + c.val) := fun hac => hdisj (n + c.val) hac hbc
            have har_eq : wireVal C (rowOnly n m r) a = wireVal C (oneEach r c) a := by
              apply wireVal_eq_of_wireIn (n + m) C hwf _ _ (len_rowOnly n m r) (len_oneEach n m r c) a (by omega)
              intro w _ haw
              rw [getD_rowOnly, getD_oneEach]
              have hne : w ≠ n + c.val := fun heq => hac_not (heq ▸ haw)
              simp [hne]
            have hbc_eq : wireVal C (colOnly n m c) b = wireVal C (oneEach r c) b := by
              apply wireVal_eq_of_wireIn (n + m) C hwf _ _ (len_colOnly n m c) (len_oneEach n m r c) b (by omega)
              intro w _ hbw
              rw [getD_colOnly, getD_oneEach]
              have hne : w ≠ r.val := fun heq => hbr_not (heq ▸ hbw)
              simp [hne]
            exact Or.inl ⟨har, hbc, by rw [har_eq, ha1], by rw [hbc_eq, hb1]⟩
          · have hbc_not : ¬ wireIn (n + m) C b (n + c.val) := fun hbc => hdisj (n + c.val) hac hbc
            have hbr : wireIn (n + m) C b r.val := hb_non0.resolve_right hbc_not
            have har_not : ¬ wireIn (n + m) C a r.val := fun har => hdisj r.val har hbr
            have hbr_eq : wireVal C (rowOnly n m r) b = wireVal C (oneEach r c) b := by
              apply wireVal_eq_of_wireIn (n + m) C hwf _ _ (len_rowOnly n m r) (len_oneEach n m r c) b (by omega)
              intro w _ hbw
              rw [getD_rowOnly, getD_oneEach]
              have hne : w ≠ n + c.val := fun heq => hbc_not (heq ▸ hbw)
              simp [hne]
            have hac_eq : wireVal C (colOnly n m c) a = wireVal C (oneEach r c) a := by
              apply wireVal_eq_of_wireIn (n + m) C hwf _ _ (len_colOnly n m c) (len_oneEach n m r c) a (by omega)
              intro w _ haw
              rw [getD_colOnly, getD_oneEach]
              have hne : w ≠ r.val := fun heq => har_not (heq ▸ haw)
              simp [hne]
            exact Or.inr ⟨hbr, hac, by rw [hbr_eq, hb1], by rw [hac_eq, ha1]⟩
        refine ⟨?_, ?_, ?_⟩
        · intro r c hval
          rcases not_both_same r c hval with ⟨har, hbc, _, _⟩ | ⟨hbr, hac, _, _⟩
          · exact ⟨wireIn_up a ha_mem r.val har, wireIn_up b hb_mem (n + c.val) hbc⟩
          · exact ⟨wireIn_up b hb_mem r.val hbr, wireIn_up a ha_mem (n + c.val) hac⟩
        · intro r1 c1 c2 h1 h2 r
          rcases not_both_same r1 c1 h1 with ⟨har1, hbc1, _, hcb1⟩ | ⟨hbr1, hac1, _, hca1⟩
          · rcases not_both_same r1 c2 h2 with ⟨_, hbc2, _, hcb2⟩ | ⟨hbr1', _, _, _⟩
            · have hac1_not : ¬ wireIn (n + m) C a (n + c1.val) := fun h => hdisj _ h hbc1
              have hac2_not : ¬ wireIn (n + m) C a (n + c2.val) := fun h => hdisj _ h hbc2
              by_cases hrb : wireIn (n + m) C b r.val
              · have hra_not : ¬ wireIn (n + m) C a r.val := fun h => hdisj _ h hrb
                have ha1 : wireVal C (oneEach r c1) a = false :=
                  wireVal_false_of_wireIn_false (n + m) C hmono hwf _ (len_oneEach n m r c1) a (by omega)
                    (fun w _ haw => by
                      rw [getD_oneEach]
                      have hne1 : w ≠ r.val := fun heq => hra_not (heq ▸ haw)
                      have hne2 : w ≠ n + c1.val := fun heq => hac1_not (heq ▸ haw)
                      simp [hne1, hne2])
                have ha2 : wireVal C (oneEach r c2) a = false :=
                  wireVal_false_of_wireIn_false (n + m) C hmono hwf _ (len_oneEach n m r c2) a (by omega)
                    (fun w _ haw => by
                      rw [getD_oneEach]
                      have hne1 : w ≠ r.val := fun heq => hra_not (heq ▸ haw)
                      have hne2 : w ≠ n + c2.val := fun heq => hac2_not (heq ▸ haw)
                      simp [hne1, hne2])
                rw [eval_and _ (len_oneEach n m r c1), eval_and _ (len_oneEach n m r c2), ha1, ha2]
                rfl
              · have hb1 : wireVal C (oneEach r c1) b = true := by
                  have := wireVal_eq_of_wireIn (n + m) C hwf (colOnly n m c1) (oneEach r c1)
                    (len_colOnly n m c1) (len_oneEach n m r c1) b (by omega) (fun w _ hbw => by
                      rw [getD_colOnly, getD_oneEach]
                      have hne : w ≠ r.val := fun heq => hrb (heq ▸ hbw)
                      simp [hne])
                  rw [← this, hcb1]
                have hb2 : wireVal C (oneEach r c2) b = true := by
                  have := wireVal_eq_of_wireIn (n + m) C hwf (colOnly n m c2) (oneEach r c2)
                    (len_colOnly n m c2) (len_oneEach n m r c2) b (by omega) (fun w _ hbw => by
                      rw [getD_colOnly, getD_oneEach]
                      have hne : w ≠ r.val := fun heq => hrb (heq ▸ hbw)
                      simp [hne])
                  rw [← this, hcb2]
                have ha_eq : wireVal C (oneEach r c1) a = wireVal C (oneEach r c2) a := by
                  apply wireVal_eq_of_wireIn (n + m) C hwf _ _ (len_oneEach n m r c1) (len_oneEach n m r c2) a (by omega)
                  intro w _ haw
                  rw [getD_oneEach, getD_oneEach]
                  have hne1 : w ≠ n + c1.val := fun heq => hac1_not (heq ▸ haw)
                  have hne2 : w ≠ n + c2.val := fun heq => hac2_not (heq ▸ haw)
                  simp [hne1, hne2]
                rw [eval_and _ (len_oneEach n m r c1), eval_and _ (len_oneEach n m r c2), hb1, hb2, ha_eq]
            · exact False.elim (hdisj r1.val har1 hbr1')
          · rcases not_both_same r1 c2 h2 with ⟨har1', _, _, _⟩ | ⟨_, hac2, _, hca2⟩
            · exact False.elim (hdisj r1.val har1' hbr1)
            · have hbc1_not : ¬ wireIn (n + m) C b (n + c1.val) := fun h => hdisj _ hac1 h
              have hbc2_not : ¬ wireIn (n + m) C b (n + c2.val) := fun h => hdisj _ hac2 h
              by_cases hra : wireIn (n + m) C a r.val
              · have hrb_not : ¬ wireIn (n + m) C b r.val := fun h => hdisj _ hra h
                have hb1 : wireVal C (oneEach r c1) b = false :=
                  wireVal_false_of_wireIn_false (n + m) C hmono hwf _ (len_oneEach n m r c1) b (by omega)
                    (fun w _ hbw => by
                      rw [getD_oneEach]
                      have hne1 : w ≠ r.val := fun heq => hrb_not (heq ▸ hbw)
                      have hne2 : w ≠ n + c1.val := fun heq => hbc1_not (heq ▸ hbw)
                      simp [hne1, hne2])
                have hb2 : wireVal C (oneEach r c2) b = false :=
                  wireVal_false_of_wireIn_false (n + m) C hmono hwf _ (len_oneEach n m r c2) b (by omega)
                    (fun w _ hbw => by
                      rw [getD_oneEach]
                      have hne1 : w ≠ r.val := fun heq => hrb_not (heq ▸ hbw)
                      have hne2 : w ≠ n + c2.val := fun heq => hbc2_not (heq ▸ hbw)
                      simp [hne1, hne2])
                rw [eval_and _ (len_oneEach n m r c1), eval_and _ (len_oneEach n m r c2), hb1, hb2]
                simp
              · have ha1 : wireVal C (oneEach r c1) a = true := by
                  have := wireVal_eq_of_wireIn (n + m) C hwf (colOnly n m c1) (oneEach r c1)
                    (len_colOnly n m c1) (len_oneEach n m r c1) a (by omega) (fun w _ haw => by
                      rw [getD_colOnly, getD_oneEach]
                      have hne : w ≠ r.val := fun heq => hra (heq ▸ haw)
                      simp [hne])
                  rw [← this, hca1]
                have ha2 : wireVal C (oneEach r c2) a = true := by
                  have := wireVal_eq_of_wireIn (n + m) C hwf (colOnly n m c2) (oneEach r c2)
                    (len_colOnly n m c2) (len_oneEach n m r c2) a (by omega) (fun w _ haw => by
                      rw [getD_colOnly, getD_oneEach]
                      have hne : w ≠ r.val := fun heq => hra (heq ▸ haw)
                      simp [hne])
                  rw [← this, hca2]
                have hb_eq : wireVal C (oneEach r c1) b = wireVal C (oneEach r c2) b := by
                  apply wireVal_eq_of_wireIn (n + m) C hwf _ _ (len_oneEach n m r c1) (len_oneEach n m r c2) b (by omega)
                  intro w _ hbw
                  rw [getD_oneEach, getD_oneEach]
                  have hne1 : w ≠ n + c1.val := fun heq => hbc1_not (heq ▸ hbw)
                  have hne2 : w ≠ n + c2.val := fun heq => hbc2_not (heq ▸ hbw)
                  simp [hne1, hne2]
                rw [eval_and _ (len_oneEach n m r c1), eval_and _ (len_oneEach n m r c2), ha1, ha2, hb_eq]
        · intro r1 r2 c1 h1 h2 c
          rcases not_both_same r1 c1 h1 with ⟨har1, hbc1, hra1, _⟩ | ⟨hbr1, hac1, hrb1, _⟩
          · rcases not_both_same r2 c1 h2 with ⟨har2, _, hra2, _⟩ | ⟨_, hac1', _, _⟩
            · have hbr1_not : ¬ wireIn (n + m) C b r1.val := fun h => hdisj _ har1 h
              have hbr2_not : ¬ wireIn (n + m) C b r2.val := fun h => hdisj _ har2 h
              by_cases hca : wireIn (n + m) C a (n + c.val)
              · have hcb_not : ¬ wireIn (n + m) C b (n + c.val) := fun h => hdisj _ hca h
                have hb1 : wireVal C (oneEach r1 c) b = false :=
                  wireVal_false_of_wireIn_false (n + m) C hmono hwf _ (len_oneEach n m r1 c) b (by omega)
                    (fun w _ hbw => by
                      rw [getD_oneEach]
                      have hne1 : w ≠ r1.val := fun heq => hbr1_not (heq ▸ hbw)
                      have hne2 : w ≠ n + c.val := fun heq => hcb_not (heq ▸ hbw)
                      simp [hne1, hne2])
                have hb2 : wireVal C (oneEach r2 c) b = false :=
                  wireVal_false_of_wireIn_false (n + m) C hmono hwf _ (len_oneEach n m r2 c) b (by omega)
                    (fun w _ hbw => by
                      rw [getD_oneEach]
                      have hne1 : w ≠ r2.val := fun heq => hbr2_not (heq ▸ hbw)
                      have hne2 : w ≠ n + c.val := fun heq => hcb_not (heq ▸ hbw)
                      simp [hne1, hne2])
                rw [eval_and _ (len_oneEach n m r1 c), eval_and _ (len_oneEach n m r2 c), hb1, hb2]
                simp
              · have ha1 : wireVal C (oneEach r1 c) a = true := by
                  have := wireVal_eq_of_wireIn (n + m) C hwf (rowOnly n m r1) (oneEach r1 c)
                    (len_rowOnly n m r1) (len_oneEach n m r1 c) a (by omega) (fun w _ haw => by
                      rw [getD_rowOnly, getD_oneEach]
                      have hne : w ≠ n + c.val := fun heq => hca (heq ▸ haw)
                      simp [hne])
                  rw [← this, hra1]
                have ha2 : wireVal C (oneEach r2 c) a = true := by
                  have := wireVal_eq_of_wireIn (n + m) C hwf (rowOnly n m r2) (oneEach r2 c)
                    (len_rowOnly n m r2) (len_oneEach n m r2 c) a (by omega) (fun w _ haw => by
                      rw [getD_rowOnly, getD_oneEach]
                      have hne : w ≠ n + c.val := fun heq => hca (heq ▸ haw)
                      simp [hne])
                  rw [← this, hra2]
                have hb_eq : wireVal C (oneEach r1 c) b = wireVal C (oneEach r2 c) b := by
                  apply wireVal_eq_of_wireIn (n + m) C hwf _ _ (len_oneEach n m r1 c) (len_oneEach n m r2 c) b (by omega)
                  intro w _ hbw
                  rw [getD_oneEach, getD_oneEach]
                  have hne1 : w ≠ r1.val := fun heq => hbr1_not (heq ▸ hbw)
                  have hne2 : w ≠ r2.val := fun heq => hbr2_not (heq ▸ hbw)
                  simp [hne1, hne2]
                rw [eval_and _ (len_oneEach n m r1 c), eval_and _ (len_oneEach n m r2 c), ha1, ha2, hb_eq]
            · exact False.elim (hdisj (n + c1.val) hac1' hbc1)
          · rcases not_both_same r2 c1 h2 with ⟨_, hbc1', _, _⟩ | ⟨hbr2, _, hrb2, _⟩
            · exact False.elim (hdisj (n + c1.val) hac1 hbc1')
            · have har1_not : ¬ wireIn (n + m) C a r1.val := fun h => hdisj _ h hbr1
              have har2_not : ¬ wireIn (n + m) C a r2.val := fun h => hdisj _ h hbr2
              by_cases hcb : wireIn (n + m) C b (n + c.val)
              · have hca_not : ¬ wireIn (n + m) C a (n + c.val) := fun h => hdisj _ h hcb
                have ha1 : wireVal C (oneEach r1 c) a = false :=
                  wireVal_false_of_wireIn_false (n + m) C hmono hwf _ (len_oneEach n m r1 c) a (by omega)
                    (fun w _ haw => by
                      rw [getD_oneEach]
                      have hne1 : w ≠ r1.val := fun heq => har1_not (heq ▸ haw)
                      have hne2 : w ≠ n + c.val := fun heq => hca_not (heq ▸ haw)
                      simp [hne1, hne2])
                have ha2 : wireVal C (oneEach r2 c) a = false :=
                  wireVal_false_of_wireIn_false (n + m) C hmono hwf _ (len_oneEach n m r2 c) a (by omega)
                    (fun w _ haw => by
                      rw [getD_oneEach]
                      have hne1 : w ≠ r2.val := fun heq => har2_not (heq ▸ haw)
                      have hne2 : w ≠ n + c.val := fun heq => hca_not (heq ▸ haw)
                      simp [hne1, hne2])
                rw [eval_and _ (len_oneEach n m r1 c), eval_and _ (len_oneEach n m r2 c), ha1, ha2]
                rfl
              · have hb1 : wireVal C (oneEach r1 c) b = true := by
                  have := wireVal_eq_of_wireIn (n + m) C hwf (rowOnly n m r1) (oneEach r1 c)
                    (len_rowOnly n m r1) (len_oneEach n m r1 c) b (by omega) (fun w _ hbw => by
                      rw [getD_rowOnly, getD_oneEach]
                      have hne : w ≠ n + c.val := fun heq => hcb (heq ▸ hbw)
                      simp [hne])
                  rw [← this, hrb1]
                have hb2 : wireVal C (oneEach r2 c) b = true := by
                  have := wireVal_eq_of_wireIn (n + m) C hwf (rowOnly n m r2) (oneEach r2 c)
                    (len_rowOnly n m r2) (len_oneEach n m r2 c) b (by omega) (fun w _ hbw => by
                      rw [getD_rowOnly, getD_oneEach]
                      have hne : w ≠ n + c.val := fun heq => hcb (heq ▸ hbw)
                      simp [hne])
                  rw [← this, hrb2]
                have ha_eq : wireVal C (oneEach r1 c) a = wireVal C (oneEach r2 c) a := by
                  apply wireVal_eq_of_wireIn (n + m) C hwf _ _ (len_oneEach n m r1 c) (len_oneEach n m r2 c) a (by omega)
                  intro w _ haw
                  rw [getD_oneEach, getD_oneEach]
                  have hne1 : w ≠ r1.val := fun heq => har1_not (heq ▸ haw)
                  have hne2 : w ≠ r2.val := fun heq => har2_not (heq ▸ haw)
                  simp [hne1, hne2]
                rw [eval_and _ (len_oneEach n m r1 c), eval_and _ (len_oneEach n m r2 c), hb1, hb2, ha_eq]
      · have eval_or : ∀ xs, xs.length = n + m → wireVal C xs u = (wireVal C xs a || wireVal C xs b) := by
          intro xs hxs
          rw [heval_gate xs hxs, hop_or]
          simp [GateOp.eval]
        have hrow_a : ∀ r : Fin n, wireVal C (rowOnly n m r) a = false := by
          intro r; have h := hrow0 r; rw [eval_or _ (len_rowOnly n m r)] at h
          cases hv : wireVal C (rowOnly n m r) a <;> simp [hv] at h ⊢
        have hrow_b : ∀ r : Fin n, wireVal C (rowOnly n m r) b = false := by
          intro r; have h := hrow0 r; rw [eval_or _ (len_rowOnly n m r)] at h
          cases hv : wireVal C (rowOnly n m r) b <;> simp [hv] at h ⊢
        have hcol_a : ∀ c : Fin m, wireVal C (colOnly n m c) a = false := by
          intro c; have h := hcol0 c; rw [eval_or _ (len_colOnly n m c)] at h
          cases hv : wireVal C (colOnly n m c) a <;> simp [hv] at h ⊢
        have hcol_b : ∀ c : Fin m, wireVal C (colOnly n m c) b = false := by
          intro c; have h := hcol0 c; rw [eval_or _ (len_colOnly n m c)] at h
          cases hv : wireVal C (colOnly n m c) b <;> simp [hv] at h ⊢
        obtain ⟨ha_in, ha_col, ha_row⟩ := ih a ha_lt (by omega) (hpos_child a ha_mem) hrow_a hcol_a
        obtain ⟨hb_in, hb_col, hb_row⟩ := ih b hb_lt (by omega) (hpos_child b hb_mem) hrow_b hcol_b
        refine ⟨?_, ?_, ?_⟩
        · intro r c hval
          rw [eval_or _ (len_oneEach n m r c), Bool.or_eq_true] at hval
          rcases hval with ha1 | hb1
          · obtain ⟨h1, h2⟩ := ha_in r c ha1
            exact ⟨wireIn_up a ha_mem _ h1, wireIn_up a ha_mem _ h2⟩
          · obtain ⟨h1, h2⟩ := hb_in r c hb1
            exact ⟨wireIn_up b hb_mem _ h1, wireIn_up b hb_mem _ h2⟩
        · intro r1 c1 c2 h1 h2 r
          rw [eval_or _ (len_oneEach n m r1 c1), Bool.or_eq_true] at h1
          rw [eval_or _ (len_oneEach n m r1 c2), Bool.or_eq_true] at h2
          rcases h1 with ha1 | hb1
          · rcases h2 with ha2 | hb2
            · have hc1_a := (ha_in r1 c1 ha1).2
              have hc2_a := (ha_in r1 c2 ha2).2
              have hb1_f : wireVal C (oneEach r c1) b = false := by
                cases h : wireVal C (oneEach r c1) b
                · rfl
                · exact False.elim (hdisj _ hc1_a (hb_in r c1 h).2)
              have hb2_f : wireVal C (oneEach r c2) b = false := by
                cases h : wireVal C (oneEach r c2) b
                · rfl
                · exact False.elim (hdisj _ hc2_a (hb_in r c2 h).2)
              rw [eval_or _ (len_oneEach n m r c1), eval_or _ (len_oneEach n m r c2), hb1_f, hb2_f,
                ha_col r1 c1 c2 ha1 ha2 r]
            · exact False.elim (hdisj _ (ha_in r1 c1 ha1).1 (hb_in r1 c2 hb2).1)
          · rcases h2 with ha2 | hb2
            · exact False.elim (hdisj _ (ha_in r1 c2 ha2).1 (hb_in r1 c1 hb1).1)
            · have hc1_b := (hb_in r1 c1 hb1).2
              have hc2_b := (hb_in r1 c2 hb2).2
              have ha1_f : wireVal C (oneEach r c1) a = false := by
                cases h : wireVal C (oneEach r c1) a
                · rfl
                · exact False.elim (hdisj _ (ha_in r c1 h).2 hc1_b)
              have ha2_f : wireVal C (oneEach r c2) a = false := by
                cases h : wireVal C (oneEach r c2) a
                · rfl
                · exact False.elim (hdisj _ (ha_in r c2 h).2 hc2_b)
              rw [eval_or _ (len_oneEach n m r c1), eval_or _ (len_oneEach n m r c2), ha1_f, ha2_f,
                hb_col r1 c1 c2 hb1 hb2 r]
        · intro r1 r2 c1 h1 h2 c
          rw [eval_or _ (len_oneEach n m r1 c1), Bool.or_eq_true] at h1
          rw [eval_or _ (len_oneEach n m r2 c1), Bool.or_eq_true] at h2
          rcases h1 with ha1 | hb1
          · rcases h2 with ha2 | hb2
            · have hr1_a := (ha_in r1 c1 ha1).1
              have hr2_a := (ha_in r2 c1 ha2).1
              have hb1_f : wireVal C (oneEach r1 c) b = false := by
                cases h : wireVal C (oneEach r1 c) b
                · rfl
                · exact False.elim (hdisj _ hr1_a (hb_in r1 c h).1)
              have hb2_f : wireVal C (oneEach r2 c) b = false := by
                cases h : wireVal C (oneEach r2 c) b
                · rfl
                · exact False.elim (hdisj _ hr2_a (hb_in r2 c h).1)
              rw [eval_or _ (len_oneEach n m r1 c), eval_or _ (len_oneEach n m r2 c), hb1_f, hb2_f,
                ha_row r1 r2 c1 ha1 ha2 c]
            · exact False.elim (hdisj _ (ha_in r1 c1 ha1).2 (hb_in r2 c1 hb2).2)
          · rcases h2 with ha2 | hb2
            · exact False.elim (hdisj _ (ha_in r2 c1 ha2).2 (hb_in r1 c1 hb1).2)
            · have hr1_b := (hb_in r1 c1 hb1).1
              have hr2_b := (hb_in r2 c1 hb2).1
              have ha1_f : wireVal C (oneEach r1 c) a = false := by
                cases h : wireVal C (oneEach r1 c) a
                · rfl
                · exact False.elim (hdisj _ (ha_in r1 c h).1 hr1_b)
              have ha2_f : wireVal C (oneEach r2 c) a = false := by
                cases h : wireVal C (oneEach r2 c) a
                · rfl
                · exact False.elim (hdisj _ (ha_in r2 c h).1 hr2_b)
              rw [eval_or _ (len_oneEach n m r1 c), eval_or _ (len_oneEach n m r2 c), ha1_f, ha2_f,
                hb_row r1 r2 c1 hb1 hb2 c]

theorem wireIn_has_input (N : ℕ) (C : Circuit)
    (hwf : ∀ j < C.gates.length, (gateAt C j).inputs.length = 2 ∧
      (gateAt C j).inputs.Nodup ∧ ∀ i ∈ (gateAt C j).inputs, i < N + j) :
    ∀ u < N + C.gates.length, ∃ w < N, wireIn N C u w := by
  intro u
  induction u using Nat.strong_induction_on with
  | ind u ih =>
    intro hu
    by_cases hlt : u < N
    · exact ⟨u, hlt, Or.inl rfl⟩
    · have hj : u - N < C.gates.length := by omega
      have hlen2 := (hwf (u - N) hj).1
      obtain ⟨a, b, hab⟩ : ∃ a b, (gateAt C (u - N)).inputs = [a, b] := by
        rcases h : (gateAt C (u - N)).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;> simp [h] at hlen2
        exact ⟨a, b, rfl⟩
      have ha_mem : a ∈ (gateAt C (u - N)).inputs := by rw [hab]; simp
      have ha_lt : a < N + (u - N) := (hwf (u - N) hj).2.2 a ha_mem
      obtain ⟨w, hwN, hwa⟩ := ih a (by omega) (by omega)
      refine ⟨w, hwN, Or.inr ⟨by omega, ?_⟩⟩
      rcases hwa with rfl | ⟨haN, hsa⟩
      · exact Or.inl ha_mem
      · have hca : InCone N C (a - N) (u - N) :=
          (inCone_iff N C (a - N) (u - N) hj).mpr ⟨a, ha_mem, haN, ha_lt, Or.inl rfl⟩
        exact inSub_of_inCone N C (a - N) (u - N) w hj hca hsa

theorem gate_has_two_inputs (N : ℕ) (C : Circuit) (g : ℕ) (hg : g < C.gates.length)
    (hwf : ∀ j < C.gates.length, (gateAt C j).inputs.length = 2 ∧
      (gateAt C j).inputs.Nodup ∧ ∀ i ∈ (gateAt C j).inputs, i < N + j)
    (hro : ∀ w, inSub N C g w → ((Finset.range C.gates.length).filter fun k => w ∈ (gateAt C k).inputs).card = 1)
    (j : ℕ) (hjg : j = g ∨ InCone N C j g) :
    ∃ w1 w2, w1 < N ∧ w2 < N ∧ w1 ≠ w2 ∧ inSub N C j w1 ∧ inSub N C j w2 := by
  have hj : j < C.gates.length := by
    rcases hjg with rfl | h
    · exact hg
    · exact Nat.lt_trans (inCone_lt N C g hg j h) hg
  have hlen2 := (hwf j hj).1
  have hnodup := (hwf j hj).2.1
  have hback := (hwf j hj).2.2
  obtain ⟨a, b, hab⟩ : ∃ a b, (gateAt C j).inputs = [a, b] := by
    rcases h : (gateAt C j).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;> simp [h] at hlen2
    exact ⟨a, b, rfl⟩
  have hab_ne : a ≠ b := by rw [hab] at hnodup; simpa using hnodup
  have ha_mem : a ∈ (gateAt C j).inputs := by rw [hab]; simp
  have hb_mem : b ∈ (gateAt C j).inputs := by rw [hab]; simp
  have ha_lt : a < N + j := hback a ha_mem
  have hb_lt : b < N + j := hback b hb_mem
  obtain ⟨w1, hw1N, hw1a⟩ := wireIn_has_input N C hwf a (by omega)
  obtain ⟨w2, hw2N, hw2b⟩ := wireIn_has_input N C hwf b (by omega)
  have hdisj := wireIn_disjoint N C g hg hwf hro j hjg a b ha_mem hb_mem hab_ne
  have hne : w1 ≠ w2 := fun heq => hdisj w1 hw1a (heq ▸ hw2b)
  have to_sub : ∀ v, v ∈ (gateAt C j).inputs → ∀ w, wireIn N C v w → inSub N C j w := by
    intro v hv w hvw
    rcases hvw with rfl | ⟨hvN, hsv⟩
    · exact Or.inl hv
    · have hv_lt : v < N + j := hback v hv
      have hcv : InCone N C (v - N) j := (inCone_iff N C (v - N) j hj).mpr ⟨v, hv, hvN, hv_lt, Or.inl rfl⟩
      exact inSub_of_inCone N C (v - N) j w hj hcv hsv
  exact ⟨w1, w2, hw1N, hw2N, hne, to_sub a ha_mem w1 hw1a, to_sub b hb_mem w2 hw2b⟩

end PEqualNP.Outside.L_meta_17164

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.Represents PEqualNP.Outside.L_meta_17164 in
theorem PEqualNP.Outside.L_meta_17164 : (∀ (n m : ℕ) (A : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit) (g : ℕ), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.Represents.Represents A C → (∀ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.length = 2 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.Nodup ∧ ∀ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs, i < n + m + j) → (∀ u u' : Fin n, u ≠ u' → ∃ v, A u v ≠ A u' v) → (∀ v v' : Fin m, v ≠ v' → ∃ u, A u v ≠ A u v') → (∀ u, (∃ v, A u v = true) ∧ ∃ v, A u v = false) → (∀ v, (∃ u, A u v = true) ∧ ∃ u, A u v = false) → (∀ u v, A u v = true → (∃ v', v' ≠ v ∧ A u v' = true) ∨ ∃ u', u' ≠ u ∧ A u' v = true) → g < C.gates.length → (∀ w, (w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs ∨ ∃ i, PEqualNP.EdgeOwnership.InCone (n + m) C i g ∧ w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs) → ((Finset.range C.gates.length).filter fun k => w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs).card = 1) → (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∃ a b, a < n ∧ n ≤ b ∧ b < n + m ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.toFinset = {a, b}) := by
  intro n m A C g hmono hrep hwf hdistR hdistC hR hC hnoiso hg hro
  have hro' : ∀ w, inSub (n + m) C g w →
      ((Finset.range C.gates.length).filter fun k => w ∈ (gateAt C k).inputs).card = 1 := hro
  have heval_row0 : ∀ u : Fin n, C.eval (rowOnly n m u) = false := by
    intro u
    obtain ⟨v, hv⟩ := (hR u).2
    cases h : C.eval (rowOnly n m u)
    · rfl
    · have hm : wireVal C (oneEach u v) C.output = true := by
        apply wireVal_mono C hmono (rowOnly n m u) (oneEach u v)
        · rw [len_rowOnly, len_oneEach]
        · intro i _ hi
          rw [getD_rowOnly] at hi
          rw [getD_oneEach, hi]
          rfl
        · exact h
      change C.eval (oneEach u v) = true at hm
      rw [hrep u v, hv] at hm
      simp at hm
  have heval_col0 : ∀ v : Fin m, C.eval (colOnly n m v) = false := by
    intro v
    obtain ⟨u, hu⟩ := (hC v).2
    cases h : C.eval (colOnly n m v)
    · rfl
    · have hm : wireVal C (oneEach u v) C.output = true := by
        apply wireVal_mono C hmono (colOnly n m v) (oneEach u v)
        · rw [len_colOnly, len_oneEach]
        · intro i _ hi
          rw [getD_colOnly] at hi
          rw [getD_oneEach, hi]
          simp
        · exact h
      change C.eval (oneEach u v) = true at hm
      rw [hrep u v, hu] at hm
      simp at hm
  have hnot_out_in : ¬ inSub (n + m) C g C.output := by
    intro hout_in
    by_cases hout_lt : C.output < n + m
    · by_cases hout_n : C.output < n
      · let u : Fin n := ⟨C.output, hout_n⟩
        obtain ⟨v, hv⟩ := (hR u).2
        have hev : C.eval (oneEach u v) = true := by
          change wireVal C (oneEach u v) C.output = true
          rw [wireVal_lt C _ _ (by rw [len_oneEach]; exact hout_lt), getD_oneEach]
          simp [u]
        rw [hrep u v, hv] at hev; simp at hev
      · let v : Fin m := ⟨C.output - n, by omega⟩
        obtain ⟨u, hu⟩ := (hC v).2
        have hev : C.eval (oneEach u v) = true := by
          change wireVal C (oneEach u v) C.output = true
          rw [wireVal_lt C _ _ (by rw [len_oneEach]; exact hout_lt), getD_oneEach]
          have : C.output = n + v.val := by simp [v]; omega
          simp [this]
        rw [hrep u v, hu] at hev; simp at hev
    · have hcone_out : InCone (n + m) C (C.output - (n + m)) g := by
        rcases hout_in with hmem | ⟨i, hig, hmem⟩
        · have hlt := (hwf g hg).2.2 C.output hmem
          exact (inCone_iff (n + m) C _ g hg).mpr ⟨C.output, hmem, by omega, hlt, Or.inl rfl⟩
        · have hi_lt := Nat.lt_trans (inCone_lt (n + m) C g hg i hig) hg
          have hlt := (hwf i hi_lt).2.2 C.output hmem
          have hci : InCone (n + m) C (C.output - (n + m)) i :=
            (inCone_iff (n + m) C _ i hi_lt).mpr ⟨C.output, hmem, by omega, hlt, Or.inl rfl⟩
          exact inCone_trans (n + m) C g hg _ i hci hig
      have hout_lt_len : C.output < n + m + C.gates.length := by
        have := inCone_lt (n + m) C g hg _ hcone_out; omega
      obtain ⟨_, hcol_eq, hrow_eq⟩ := ro_block_prop n m C g hg hmono hwf hro' C.output hout_lt_len
        (Or.inr (Or.inr hcone_out)) heval_row0 heval_col0
      obtain ⟨w1, _, hw1N, _, _, _, _⟩ := gate_has_two_inputs (n + m) C g hg hwf hro' g (Or.inl rfl)
      have hhas_edge : ∃ (u : Fin n) (v : Fin m), A u v = true := by
        by_cases hw1n : w1 < n
        · obtain ⟨v, hv⟩ := (hR ⟨w1, hw1n⟩).1
          exact ⟨⟨w1, hw1n⟩, v, hv⟩
        · obtain ⟨u, hu⟩ := (hC ⟨w1 - n, by omega⟩).1
          exact ⟨u, ⟨w1 - n, by omega⟩, hu⟩
      obtain ⟨u0, v0, huv0⟩ := hhas_edge
      rcases hnoiso u0 v0 huv0 with ⟨v1, hv1_ne, huv1⟩ | ⟨u1, hu1_ne, huv1⟩
      · have h1 : wireVal C (oneEach u0 v0) C.output = true := by
          change C.eval (oneEach u0 v0) = true; rw [hrep, huv0]
        have h2 : wireVal C (oneEach u0 v1) C.output = true := by
          change C.eval (oneEach u0 v1) = true; rw [hrep, huv1]
        obtain ⟨u, hu_ne⟩ := hdistC v0 v1 hv1_ne.symm
        have heq := hcol_eq u0 v0 v1 h1 h2 u
        change C.eval (oneEach u v0) = C.eval (oneEach u v1) at heq
        rw [hrep, hrep] at heq
        exact hu_ne heq
      · have h1 : wireVal C (oneEach u0 v0) C.output = true := by
          change C.eval (oneEach u0 v0) = true; rw [hrep, huv0]
        have h2 : wireVal C (oneEach u1 v0) C.output = true := by
          change C.eval (oneEach u1 v0) = true; rw [hrep, huv1]
        obtain ⟨v, hv_ne⟩ := hdistR u0 u1 hu1_ne.symm
        have heq := hrow_eq u0 u1 v0 h1 h2 v
        change C.eval (oneEach u0 v) = C.eval (oneEach u1 v) at heq
        rw [hrep, hrep] at heq
        exact hv_ne heq
  have hno_inner_edge : ∀ (u : Fin n) (v : Fin m), inSub (n + m) C g u.val → inSub (n + m) C g (n + v.val) → A u v = false := by
    intro u0 v0 hu0 hv0
    by_contra htrue
    have huv0 : A u0 v0 = true := by cases h : A u0 v0 <;> simp [h] at htrue ⊢
    have hval_out : wireVal C (oneEach u0 v0) C.output = true := by
      change C.eval (oneEach u0 v0) = true; rw [hrep, huv0]
    have hval_g : wireVal C (oneEach u0 v0) (n + m + g) = true := by
      cases h : wireVal C (oneEach u0 v0) (n + m + g)
      · let zs := List.replicate (n + m) false
        have hz_len : zs.length = n + m := by simp [zs]
        have hz_all : ∀ i < n + m, zs.getD i false = false := by
          intro i hi; simp [zs, List.getD_eq_getElem?_getD, hi]
        have hg_z : wireVal C zs (n + m + g) = false := wireVal_allFalse C (n + m) hmono hwf zs hz_len hz_all _
        have hout_eq := eval_eq_outside_and_g (n + m) C g hg hmono hwf hro' (oneEach u0 v0) zs
          (len_oneEach n m u0 v0) hz_len (fun w hw hnot => by
            rw [getD_oneEach, hz_all w hw]
            have h1 : w ≠ u0.val := fun heq => hnot (heq ▸ hu0)
            have h2 : w ≠ n + v0.val := fun heq => hnot (heq ▸ hv0)
            simp [h1, h2]) (by rw [h, hg_z]) C.output hnot_out_in
        rw [wireVal_allFalse C (n + m) hmono hwf zs hz_len hz_all C.output] at hout_eq
        rw [hout_eq] at hval_out; simp at hval_out
      · rfl
    have hg_implies_out : ∀ xs, xs.length = n + m → wireVal C xs (n + m + g) = true → C.eval xs = true := by
      intro xs hxs hgx
      exact eval_mono_outside_and_g (n + m) C g hg hmono hwf hro' (oneEach u0 v0) xs
        (len_oneEach n m u0 v0) hxs (fun w _ hnot hw1 => by
          rw [getD_oneEach] at hw1
          simp only [Bool.or_eq_true, decide_eq_true_eq] at hw1
          rcases hw1 with rfl | rfl
          · exact False.elim (hnot hu0)
          · exact False.elim (hnot hv0))
        (fun _ => hgx) C.output hnot_out_in hval_out
    have hg_row0 : ∀ r : Fin n, wireVal C (rowOnly n m r) (n + m + g) = false := by
      intro r
      cases h : wireVal C (rowOnly n m r) (n + m + g)
      · rfl
      · have := hg_implies_out (rowOnly n m r) (len_rowOnly n m r) h
        rw [heval_row0 r] at this; simp at this
    have hg_col0 : ∀ c : Fin m, wireVal C (colOnly n m c) (n + m + g) = false := by
      intro c
      cases h : wireVal C (colOnly n m c) (n + m + g)
      · rfl
      · have := hg_implies_out (colOnly n m c) (len_colOnly n m c) h
        rw [heval_col0 c] at this; simp at this
    obtain ⟨hg_in, hg_col, hg_row⟩ := ro_block_prop n m C g hg hmono hwf hro' (n + m + g) (by omega)
      (Or.inr (Or.inl (by omega))) hg_row0 hg_col0
    have hA_eq_g : ∀ (r : Fin n) (c : Fin m), (inSub (n + m) C g r.val ∨ inSub (n + m) C g (n + c.val)) →
        A r c = wireVal C (oneEach r c) (n + m + g) := by
      intro r c hrc
      cases h : wireVal C (oneEach r c) (n + m + g)
      · rcases hrc with hr | hc
        · have heq := eval_eq_outside_and_g (n + m) C g hg hmono hwf hro' (oneEach r c) (colOnly n m c)
            (len_oneEach n m r c) (len_colOnly n m c) (fun w _ hnot => by
              rw [getD_oneEach, getD_colOnly]
              have hne : w ≠ r.val := fun heq => hnot (heq ▸ hr)
              simp [hne]) (by rw [h, hg_col0 c]) C.output hnot_out_in
          change C.eval (oneEach r c) = C.eval (colOnly n m c) at heq
          rw [hrep, heval_col0] at heq; exact heq
        · have heq := eval_eq_outside_and_g (n + m) C g hg hmono hwf hro' (oneEach r c) (rowOnly n m r)
            (len_oneEach n m r c) (len_rowOnly n m r) (fun w _ hnot => by
              rw [getD_oneEach, getD_rowOnly]
              have hne : w ≠ n + c.val := fun heq => hnot (heq ▸ hc)
              simp [hne]) (by rw [h, hg_row0 r]) C.output hnot_out_in
          change C.eval (oneEach r c) = C.eval (rowOnly n m r) at heq
          rw [hrep, heval_row0] at heq; exact heq
      · have := hg_implies_out (oneEach r c) (len_oneEach n m r c) h
        rw [hrep] at this; exact this
    rcases hnoiso u0 v0 huv0 with ⟨v1, hv1_ne, huv1⟩ | ⟨u1, hu1_ne, huv1⟩
    · have hgv1 : wireVal C (oneEach u0 v1) (n + m + g) = true := by
        rw [← hA_eq_g u0 v1 (Or.inl hu0), huv1]
      have hv1_in : inSub (n + m) C g (n + v1.val) := by
        have := (hg_in u0 v1 hgv1).2
        rcases this with heq | ⟨_, hs⟩
        · omega
        · simpa using hs
      obtain ⟨u, hu_ne⟩ := hdistC v0 v1 hv1_ne.symm
      have heq := hg_col u0 v0 v1 hval_g hgv1 u
      rw [← hA_eq_g u v0 (Or.inr hv0), ← hA_eq_g u v1 (Or.inr hv1_in)] at heq
      exact hu_ne heq
    · have hgu1 : wireVal C (oneEach u1 v0) (n + m + g) = true := by
        rw [← hA_eq_g u1 v0 (Or.inr hv0), huv1]
      have hu1_in : inSub (n + m) C g u1.val := by
        have := (hg_in u1 v0 hgu1).1
        rcases this with heq | ⟨_, hs⟩
        · omega
        · simpa using hs
      obtain ⟨v, hv_ne⟩ := hdistR u0 u1 hu1_ne.symm
      have heq := hg_row u0 u1 v0 hval_g hgu1 v
      rw [← hA_eq_g u0 v (Or.inl hu0), ← hA_eq_g u1 v (Or.inl hu1_in)] at heq
      exact hv_ne heq
  have hrow_true : ∀ u : Fin n, inSub (n + m) C g u.val → wireVal C (rowOnly n m u) (n + m + g) = true := by
    intro u hu
    obtain ⟨v, hv⟩ := (hR u).1
    have hv_not : ¬ inSub (n + m) C g (n + v.val) := by
      intro hvin
      have hf := hno_inner_edge u v hu hvin
      rw [hv] at hf; simp at hf
    cases h : wireVal C (rowOnly n m u) (n + m + g)
    · have hgv : wireVal C (oneEach u v) (n + m + g) = false := by
        have heq := wireVal_eq_of_wireIn (n + m) C hwf (oneEach u v) (rowOnly n m u)
          (len_oneEach n m u v) (len_rowOnly n m u) (n + m + g) (by omega) (fun w hw hwg => by
            rw [getD_oneEach, getD_rowOnly]
            have hne : w ≠ n + v.val := by
              intro heq; subst heq
              rcases hwg with h0 | ⟨_, hs⟩
              · omega
              · simp at hs; exact hv_not hs
            simp [hne])
        rw [heq, h]
      have hg_col : wireVal C (colOnly n m v) (n + m + g) = false :=
        wireVal_false_of_wireIn_false (n + m) C hmono hwf (colOnly n m v) (len_colOnly n m v) (n + m + g)
          (by omega) (fun w hw hwg => by
            rw [getD_colOnly]
            have hne : w ≠ n + v.val := by
              intro heq; subst heq
              rcases hwg with h0 | ⟨_, hs⟩
              · omega
              · simp at hs; exact hv_not hs
            simp [hne])
      have hout_eq := eval_eq_outside_and_g (n + m) C g hg hmono hwf hro' (oneEach u v) (colOnly n m v)
        (len_oneEach n m u v) (len_colOnly n m v) (fun w _ hnot => by
          rw [getD_oneEach, getD_colOnly]
          have hne : w ≠ u.val := fun heq => hnot (heq ▸ hu)
          simp [hne]) (by rw [hgv, hg_col]) C.output hnot_out_in
      change C.eval (oneEach u v) = C.eval (colOnly n m v) at hout_eq
      rw [hrep, hv, heval_col0] at hout_eq
      simp at hout_eq
    · rfl
  have hcol_true : ∀ v : Fin m, inSub (n + m) C g (n + v.val) → wireVal C (colOnly n m v) (n + m + g) = true := by
    intro v hv
    obtain ⟨u, hu⟩ := (hC v).1
    have hu_not : ¬ inSub (n + m) C g u.val := by
      intro huin
      have hf := hno_inner_edge u v huin hv
      rw [hu] at hf; simp at hf
    cases h : wireVal C (colOnly n m v) (n + m + g)
    · have hgu : wireVal C (oneEach u v) (n + m + g) = false := by
        have heq := wireVal_eq_of_wireIn (n + m) C hwf (oneEach u v) (colOnly n m v)
          (len_oneEach n m u v) (len_colOnly n m v) (n + m + g) (by omega) (fun w hw hwg => by
            rw [getD_oneEach, getD_colOnly]
            have hne : w ≠ u.val := by
              intro heq; subst heq
              rcases hwg with h0 | ⟨_, hs⟩
              · omega
              · simp at hs; exact hu_not hs
            simp [hne])
        rw [heq, h]
      have hg_row : wireVal C (rowOnly n m u) (n + m + g) = false :=
        wireVal_false_of_wireIn_false (n + m) C hmono hwf (rowOnly n m u) (len_rowOnly n m u) (n + m + g)
          (by omega) (fun w hw hwg => by
            rw [getD_rowOnly]
            have hne : w ≠ u.val := by
              intro heq; subst heq
              rcases hwg with h0 | ⟨_, hs⟩
              · omega
              · simp at hs; exact hu_not hs
            simp [hne])
      have hout_eq := eval_eq_outside_and_g (n + m) C g hg hmono hwf hro' (oneEach u v) (rowOnly n m u)
        (len_oneEach n m u v) (len_rowOnly n m u) (fun w _ hnot => by
          rw [getD_oneEach, getD_rowOnly]
          have hne : w ≠ n + v.val := fun heq => hnot (heq ▸ hv)
          simp [hne]) (by rw [hgu, hg_row]) C.output hnot_out_in
      change C.eval (oneEach u v) = C.eval (rowOnly n m u) at hout_eq
      rw [hrep, hu, heval_row0] at hout_eq
      simp at hout_eq
    · rfl
  have huniq_row : ∀ u1 u2 : Fin n, inSub (n + m) C g u1.val → inSub (n + m) C g u2.val → u1 = u2 := by
    intro u1 u2 hu1 hu2
    by_contra hne
    obtain ⟨v, hv⟩ := hdistR u1 u2 hne
    have hg1 : wireVal C (oneEach u1 v) (n + m + g) = true :=
      wireVal_mono C hmono (rowOnly n m u1) (oneEach u1 v) (by rw [len_rowOnly, len_oneEach])
        (fun i _ hi => by rw [getD_rowOnly] at hi; rw [getD_oneEach, hi]; rfl) _ (hrow_true u1 hu1)
    have hg2 : wireVal C (oneEach u2 v) (n + m + g) = true :=
      wireVal_mono C hmono (rowOnly n m u2) (oneEach u2 v) (by rw [len_rowOnly, len_oneEach])
        (fun i _ hi => by rw [getD_rowOnly] at hi; rw [getD_oneEach, hi]; rfl) _ (hrow_true u2 hu2)
    have hout_eq := eval_eq_outside_and_g (n + m) C g hg hmono hwf hro' (oneEach u1 v) (oneEach u2 v)
      (len_oneEach n m u1 v) (len_oneEach n m u2 v) (fun w _ hnot => by
        rw [getD_oneEach, getD_oneEach]
        have h1 : w ≠ u1.val := fun heq => hnot (heq ▸ hu1)
        have h2 : w ≠ u2.val := fun heq => hnot (heq ▸ hu2)
        simp [h1, h2]) (by rw [hg1, hg2]) C.output hnot_out_in
    change C.eval (oneEach u1 v) = C.eval (oneEach u2 v) at hout_eq
    rw [hrep, hrep] at hout_eq
    exact hv hout_eq
  have huniq_col : ∀ v1 v2 : Fin m, inSub (n + m) C g (n + v1.val) → inSub (n + m) C g (n + v2.val) → v1 = v2 := by
    intro v1 v2 hv1 hv2
    by_contra hne
    obtain ⟨u, hu⟩ := hdistC v1 v2 hne
    have hg1 : wireVal C (oneEach u v1) (n + m + g) = true :=
      wireVal_mono C hmono (colOnly n m v1) (oneEach u v1) (by rw [len_colOnly, len_oneEach])
        (fun i _ hi => by rw [getD_colOnly] at hi; rw [getD_oneEach, hi]; simp) _ (hcol_true v1 hv1)
    have hg2 : wireVal C (oneEach u v2) (n + m + g) = true :=
      wireVal_mono C hmono (colOnly n m v2) (oneEach u v2) (by rw [len_colOnly, len_oneEach])
        (fun i _ hi => by rw [getD_colOnly] at hi; rw [getD_oneEach, hi]; simp) _ (hcol_true v2 hv2)
    have hout_eq := eval_eq_outside_and_g (n + m) C g hg hmono hwf hro' (oneEach u v1) (oneEach u v2)
      (len_oneEach n m u v1) (len_oneEach n m u v2) (fun w _ hnot => by
        rw [getD_oneEach, getD_oneEach]
        have h1 : w ≠ n + v1.val := fun heq => hnot (heq ▸ hv1)
        have h2 : w ≠ n + v2.val := fun heq => hnot (heq ▸ hv2)
        simp [h1, h2]) (by rw [hg1, hg2]) C.output hnot_out_in
    change C.eval (oneEach u v1) = C.eval (oneEach u v2) at hout_eq
    rw [hrep, hrep] at hout_eq
    exact hu hout_eq
  have hlen2 := (hwf g hg).1
  have hnodup := (hwf g hg).2.1
  have hback := (hwf g hg).2.2
  obtain ⟨p, q, hpq_list⟩ : ∃ p q, (gateAt C g).inputs = [p, q] := by
    rcases h : (gateAt C g).inputs with _ | ⟨p, _ | ⟨q, _ | ⟨c, t⟩⟩⟩ <;> simp [h] at hlen2
    exact ⟨p, q, rfl⟩
  have hpq_ne : p ≠ q := by rw [hpq_list] at hnodup; simpa using hnodup
  have hp_mem : p ∈ (gateAt C g).inputs := by rw [hpq_list]; simp
  have hq_mem : q ∈ (gateAt C g).inputs := by rw [hpq_list]; simp
  have hp_lt : p < n + m + g := hback p hp_mem
  have hq_lt : q < n + m + g := hback q hq_mem
  have hdisj := wireIn_disjoint (n + m) C g hg hwf hro' g (Or.inl rfl) p q hp_mem hq_mem hpq_ne
  have no_three : ∀ w1 w2 w3, w1 < n + m → w2 < n + m → w3 < n + m →
      w1 ≠ w2 → w1 ≠ w3 → w2 ≠ w3 →
      inSub (n + m) C g w1 → inSub (n + m) C g w2 → inSub (n + m) C g w3 → False := by
    intro w1 w2 w3 h1 h2 h3 h12 h13 h23 s1 s2 s3
    by_cases a1 : w1 < n <;> by_cases a2 : w2 < n <;> by_cases a3 : w3 < n
    · have := huniq_row ⟨w1, a1⟩ ⟨w2, a2⟩ s1 s2; simp [Fin.ext_iff] at this; exact h12 this
    · have := huniq_row ⟨w1, a1⟩ ⟨w2, a2⟩ s1 s2; simp [Fin.ext_iff] at this; exact h12 this
    · have := huniq_row ⟨w1, a1⟩ ⟨w3, a3⟩ s1 s3; simp [Fin.ext_iff] at this; exact h13 this
    · have := huniq_col ⟨w2 - n, by omega⟩ ⟨w3 - n, by omega⟩ (by simpa [Nat.add_sub_cancel' (Nat.le_of_not_lt a2)] using s2)
        (by simpa [Nat.add_sub_cancel' (Nat.le_of_not_lt a3)] using s3)
      simp [Fin.ext_iff] at this; omega
    · have := huniq_row ⟨w2, a2⟩ ⟨w3, a3⟩ s2 s3; simp [Fin.ext_iff] at this; exact h23 this
    · have := huniq_col ⟨w1 - n, by omega⟩ ⟨w3 - n, by omega⟩ (by simpa [Nat.add_sub_cancel' (Nat.le_of_not_lt a1)] using s1)
        (by simpa [Nat.add_sub_cancel' (Nat.le_of_not_lt a3)] using s3)
      simp [Fin.ext_iff] at this; omega
    · have := huniq_col ⟨w1 - n, by omega⟩ ⟨w2 - n, by omega⟩ (by simpa [Nat.add_sub_cancel' (Nat.le_of_not_lt a1)] using s1)
        (by simpa [Nat.add_sub_cancel' (Nat.le_of_not_lt a2)] using s2)
      simp [Fin.ext_iff] at this; omega
    · have := huniq_col ⟨w1 - n, by omega⟩ ⟨w2 - n, by omega⟩ (by simpa [Nat.add_sub_cancel' (Nat.le_of_not_lt a1)] using s1)
        (by simpa [Nat.add_sub_cancel' (Nat.le_of_not_lt a2)] using s2)
      simp [Fin.ext_iff] at this; omega
  have hp_inp : p < n + m := by
    by_contra hpN
    have hcp : InCone (n + m) C (p - (n + m)) g :=
      (inCone_iff (n + m) C _ g hg).mpr ⟨p, hp_mem, by omega, hp_lt, Or.inl rfl⟩
    obtain ⟨w1, w2, hw1, hw2, h12, s1, s2⟩ := gate_has_two_inputs (n + m) C g hg hwf hro' (p - (n + m)) (Or.inr hcp)
    obtain ⟨w3, hw3, hw3q⟩ := wireIn_has_input (n + m) C hwf q (by omega)
    have h13 : w1 ≠ w3 := fun heq => hdisj w1 (Or.inr ⟨by omega, s1⟩) (heq ▸ hw3q)
    have h23 : w2 ≠ w3 := fun heq => hdisj w2 (Or.inr ⟨by omega, s2⟩) (heq ▸ hw3q)
    have s3 : inSub (n + m) C g w3 := by
      rcases hw3q with rfl | ⟨hqN, hsq⟩
      · exact Or.inl hq_mem
      · have hcq : InCone (n + m) C (q - (n + m)) g :=
          (inCone_iff (n + m) C _ g hg).mpr ⟨q, hq_mem, hqN, hq_lt, Or.inl rfl⟩
        exact inSub_of_inCone (n + m) C (q - (n + m)) g w3 hg hcq hsq
    exact no_three w1 w2 w3 hw1 hw2 hw3 h12 h13 h23
      (inSub_of_inCone (n + m) C _ g w1 hg hcp s1) (inSub_of_inCone (n + m) C _ g w2 hg hcp s2) s3
  have hq_inp : q < n + m := by
    by_contra hqN
    have hcq : InCone (n + m) C (q - (n + m)) g :=
      (inCone_iff (n + m) C _ g hg).mpr ⟨q, hq_mem, by omega, hq_lt, Or.inl rfl⟩
    obtain ⟨w1, w2, hw1, hw2, h12, s1, s2⟩ := gate_has_two_inputs (n + m) C g hg hwf hro' (q - (n + m)) (Or.inr hcq)
    have h1p : w1 ≠ p := fun heq => hdisj p (Or.inl rfl) (Or.inr ⟨by omega, heq ▸ s1⟩)
    have h2p : w2 ≠ p := fun heq => hdisj p (Or.inl rfl) (Or.inr ⟨by omega, heq ▸ s2⟩)
    exact no_three w1 w2 p hw1 hw2 hp_inp h12 h1p h2p
      (inSub_of_inCone (n + m) C _ g w1 hg hcq s1) (inSub_of_inCone (n + m) C _ g w2 hg hcq s2) (Or.inl hp_mem)
  have hsplit_pq : (p < n ∧ n ≤ q) ∨ (q < n ∧ n ≤ p) := by
    by_cases hpn : p < n <;> by_cases hqn : q < n
    · have := huniq_row ⟨p, hpn⟩ ⟨q, hqn⟩ (Or.inl hp_mem) (Or.inl hq_mem)
      simp [Fin.ext_iff] at this; exact False.elim (hpq_ne this)
    · exact Or.inl ⟨hpn, by omega⟩
    · exact Or.inr ⟨hqn, by omega⟩
    · have hp_sub : inSub (n + m) C g (n + (p - n)) := by
        rw [Nat.add_sub_cancel' (Nat.le_of_not_lt hpn)]; exact Or.inl hp_mem
      have hq_sub : inSub (n + m) C g (n + (q - n)) := by
        rw [Nat.add_sub_cancel' (Nat.le_of_not_lt hqn)]; exact Or.inl hq_mem
      have := huniq_col ⟨p - n, by omega⟩ ⟨q - n, by omega⟩ hp_sub hq_sub
      simp [Fin.ext_iff] at this; omega
  have hgate_mem : gateAt C g ∈ C.gates := by
    simp [gateAt, List.getD_eq_getElem?_getD, hg, List.getElem_mem]
  have hop_or : (gateAt C g).op = GateOp.or := by
    have hop := (hmono _ hgate_mem).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with hop_and | hop_or
    · rcases hsplit_pq with ⟨hpn, hqn⟩ | ⟨hqn, hpn⟩
      · have ht := hrow_true ⟨p, hpn⟩ (Or.inl hp_mem)
        have heq_len : n + m + g = (rowOnly n m ⟨p, hpn⟩).length + g := by rw [len_rowOnly]
        rw [heq_len, wireVal_gate_eq C _ g hg (by simpa [len_rowOnly] using hback), hop_and, hpq_list] at ht
        have hqf : wireVal C (rowOnly n m ⟨p, hpn⟩) q = false := by
          rw [wireVal_lt C _ q (by rw [len_rowOnly]; exact hq_inp), getD_rowOnly]
          simp [show q ≠ p by omega]
        simp [GateOp.eval, hqf] at ht
      · have ht := hrow_true ⟨q, hqn⟩ (Or.inl hq_mem)
        have heq_len : n + m + g = (rowOnly n m ⟨q, hqn⟩).length + g := by rw [len_rowOnly]
        rw [heq_len, wireVal_gate_eq C _ g hg (by simpa [len_rowOnly] using hback), hop_and, hpq_list] at ht
        have hpf : wireVal C (rowOnly n m ⟨q, hqn⟩) p = false := by
          rw [wireVal_lt C _ p (by rw [len_rowOnly]; exact hp_inp), getD_rowOnly]
          simp [show p ≠ q by omega]
        simp [GateOp.eval, hpf] at ht
    · exact hop_or
  refine ⟨hop_or, ?_⟩
  rcases hsplit_pq with ⟨hpn, hqn⟩ | ⟨hqn, hpn⟩
  · exact ⟨p, q, hpn, hqn, hq_inp, by rw [hpq_list]; simp⟩
  · refine ⟨q, p, hqn, hpn, hp_inp, ?_⟩
    rw [hpq_list]
    ext x
    simp [or_comm]
