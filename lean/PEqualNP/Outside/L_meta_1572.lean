import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1572

open PEqualNP.CircuitLowerBounds

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_nil (x : List Bool) : run [] x = x := rfl

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) := rfl

lemma run_append (gs1 gs2 : List Gate) (x : List Bool) :
    run (gs1 ++ gs2) x = run gs2 (run gs1 x) := by
  induction gs1 generalizing x with
  | nil => rfl
  | cons g gs1 ih => exact ih _

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih =>
    rw [run_cons, ih]
    simp
    omega

lemma getD_append_left (xs ys : List Bool) (w : ℕ) (hw : w < xs.length) :
    (xs ++ ys).getD w false = xs.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hw]

lemma getD_append_singleton_eq (xs : List Bool) (b : Bool) :
    (xs ++ [b]).getD xs.length false = b := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_ge_length (xs : List Bool) (w : ℕ) (hw : xs.length ≤ w) :
    xs.getD w false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hw]

lemma run_getD_lt (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih]
    · exact getD_append_left x _ w hw
    · simp; omega

lemma run_getD_ge (gs : List Gate) (x : List Bool) (w : ℕ) (hw : x.length + gs.length ≤ w) :
    (run gs x).getD w false = false := by
  apply getD_ge_length
  rw [run_length]
  exact hw

lemma run_getD_gate (gs : List Gate) (x : List Bool) (i : Fin gs.length)
    (ha : ∀ a ∈ (gs.get i).inputs, a < x.length + (i : ℕ)) :
    (run gs x).getD (x.length + (i : ℕ)) false =
      (gs.get i).op.eval ((gs.get i).inputs.map fun a => (run gs x).getD a false) := by
  have hsplit : gs = gs.take i.val ++ [gs.get i] ++ gs.drop (i.val + 1) := by
    have hi : i.val < gs.length := i.isLt
    have h1 : gs.get i = gs[i.val] := rfl
    rw [h1]
    simp [List.take_append_getElem]
  have hlen_take : (gs.take i.val).length = i.val := by
    simp [List.length_take, Nat.le_of_lt i.isLt]
  have hlen_pre : (run (gs.take i.val) x).length = x.length + i.val := by
    rw [run_length, hlen_take]
  have hpre_eq : ∀ a < x.length + i.val,
      (run gs x).getD a false = (run (gs.take i.val) x).getD a false := by
    intro a hlt
    have hrun1 : run gs x = run (gs.take i.val ++ ([gs.get i] ++ gs.drop (i.val + 1))) x := by
      have h1 : gs = gs.take i.val ++ ([gs.get i] ++ gs.drop (i.val + 1)) := by
        rw [← List.append_assoc]
        exact hsplit
      exact congrArg (fun l => run l x) h1
    rw [hrun1, run_append]
    exact run_getD_lt _ _ a (by rw [hlen_pre]; exact hlt)
  have hmap : ((gs.get i).inputs.map fun a => (run gs x).getD a false) =
      ((gs.get i).inputs.map fun a => (run (gs.take i.val) x).getD a false) := by
    apply List.map_congr_left
    intro a hmem
    exact hpre_eq a (ha a hmem)
  rw [hmap]
  have hrun2 : run gs x = run (gs.take i.val ++ [gs.get i] ++ gs.drop (i.val + 1)) x :=
    congrArg (fun l => run l x) hsplit
  rw [hrun2, run_append, run_append, run_cons, run_nil]
  rw [run_getD_lt]
  · rw [← hlen_pre]
    exact getD_append_singleton_eq _ _
  · simp [hlen_pre]

lemma run_mono (gs : List Gate)
    (hbasis : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : List Bool) (hlen : x.length = y.length)
    (hxy : ∀ k, x.getD k false = true → y.getD k false = true) :
    ∀ k, (run gs x).getD k false = true → (run gs y).getD k false = true := by
  induction gs generalizing x y with
  | nil => exact hxy
  | cons g gs ih =>
    have hg : g.op = GateOp.and ∨ g.op = GateOp.or := hbasis g (by simp)
    have hgs : ∀ g' ∈ gs, g'.op = GateOp.and ∨ g'.op = GateOp.or :=
      fun g' hmem => hbasis g' (by simp [hmem])
    have hstep :
        g.op.eval (g.inputs.map fun i => x.getD i false) = true →
        g.op.eval (g.inputs.map fun i => y.getD i false) = true := by
      rcases hg with hand | hor
      · rw [hand]
        simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq, forall_exists_index,
          and_imp, forall_apply_eq_imp_iff₂]
        intro hall a ha
        exact hxy a (hall a ha)
      · rw [hor]
        simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
        rintro ⟨_, ⟨a, ha, rfl⟩, hxa⟩
        exact ⟨y.getD a false, ⟨a, ha, rfl⟩, hxy a hxa⟩
    rw [run_cons, run_cons]
    apply ih hgs
    · simp [hlen]
    · intro k hk
      by_cases hlt : k < x.length
      · rw [getD_append_left y _ k (by omega)]
        rw [getD_append_left x _ k hlt] at hk
        exact hxy k hk
      · by_cases heq : k = x.length
        · subst heq
          rw [hlen]
          rw [getD_append_singleton_eq] at hk ⊢
          exact hstep hk
        · have hge : (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]).length ≤ k := by
            simp; omega
          rw [getD_ge_length _ k hge] at hk
          exact Bool.noConfusion hk

def InOrCone (gates : List Gate) (g Y : ℕ) : Prop :=
  ∀ S : Set ℕ, g ∈ S →
    (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S →
      (gates.get i).op = GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → Y ∈ S

lemma inOrCone_self (gates : List Gate) (g : ℕ) : InOrCone gates g g :=
  fun _ hg _ => hg

lemma inOrCone_step (gates : List Gate) (g : ℕ) (i : Fin gates.length) (a : ℕ)
    (hcone : InOrCone gates g (13 + (i : ℕ)))
    (hor : (gates.get i).op = GateOp.or)
    (ha : a ∈ (gates.get i).inputs) :
    InOrCone gates g a :=
  fun S hg hcl => hcl i (hcone S hg hcl) hor a ha

lemma eval_eq_run (gates : List Gate) (w : ℕ) (x : List Bool) :
    Circuit.eval ⟨gates, w⟩ x = (run gates x).getD w false := rfl

lemma inOrCone_eval_false (gates : List Gate) (g Y : ℕ) (x : Fin 13 → Bool)
    (hno_const : ∀ i : Fin gates.length,
      1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ))
    (hcone : InOrCone gates g Y)
    (hg : Circuit.eval ⟨gates, g⟩ (List.ofFn x) = false) :
    Circuit.eval ⟨gates, Y⟩ (List.ofFn x) = false := by
  let S : Set ℕ := {w | Circuit.eval ⟨gates, w⟩ (List.ofFn x) = false}
  have hcl : ∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S →
      (gates.get i).op = GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S := by
    intro i hi hor a ha
    change (run gates (List.ofFn x)).getD a false = false
    have hgate : (run gates (List.ofFn x)).getD (13 + (i : ℕ)) false =
        (gates.get i).op.eval ((gates.get i).inputs.map fun b =>
          (run gates (List.ofFn x)).getD b false) := by
      have hlen : (List.ofFn x).length = 13 := by simp
      simpa [hlen] using run_getD_gate gates (List.ofFn x) i (by simpa [hlen] using (hno_const i).2)
    have hi' : (run gates (List.ofFn x)).getD (13 + (i : ℕ)) false = false := hi
    rw [hgate, hor] at hi'
    simp only [GateOp.eval, List.any_eq_false, List.mem_map, id_eq, forall_exists_index,
      and_imp, forall_apply_eq_imp_iff₂] at hi'
    exact Bool.eq_false_iff.mpr (hi' a ha)
  exact hcone S hg hcl

lemma find_and_atom (gates : List Gate) (g : ℕ) (x : Fin 13 → Bool)
    (hbasis : ∀ gt ∈ gates,
      (gt.op = GateOp.and ∨ gt.op = GateOp.or) ∧ gt.inputs.length ≤ 2)
    (hno_const : ∀ i : Fin gates.length,
      1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ))
    (hno_inp : ∀ v : Fin 13, x v = true → ¬ InOrCone gates g v.val) :
    ∀ w : ℕ, InOrCone gates g w →
      Circuit.eval ⟨gates, w⟩ (List.ofFn x) = true →
      ∃ Y : ℕ, InOrCone gates g Y ∧
        (∃ i : Fin gates.length, Y = 13 + (i : ℕ) ∧ (gates.get i).op = GateOp.and) ∧
        Circuit.eval ⟨gates, Y⟩ (List.ofFn x) = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw_cone hw_true
    by_cases hw13 : w < 13
    · let v : Fin 13 := ⟨w, hw13⟩
      have hv : Circuit.eval ⟨gates, w⟩ (List.ofFn x) = x v := by
        rw [eval_eq_run, run_getD_lt]
        · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw13, ↓reduceDIte,
            Option.getD_some, v]
        · simp [hw13]
      rw [hv] at hw_true
      exact False.elim (hno_inp v hw_true hw_cone)
    · by_cases hwge : 13 + gates.length ≤ w
      · have hf : Circuit.eval ⟨gates, w⟩ (List.ofFn x) = false := by
          rw [eval_eq_run]
          apply run_getD_ge
          simp; omega
        rw [hf] at hw_true
        exact Bool.noConfusion hw_true
      · let i : Fin gates.length := ⟨w - 13, by omega⟩
        have hwi : w = 13 + (i : ℕ) := by simp [i]; omega
        have hop : (gates.get i).op = GateOp.and ∨ (gates.get i).op = GateOp.or :=
          (hbasis (gates.get i) (List.get_mem gates i)).1
        rcases hop with hand | hor
        · exact ⟨w, hw_cone, ⟨i, hwi, hand⟩, hw_true⟩
        · have hgate : (run gates (List.ofFn x)).getD (13 + (i : ℕ)) false =
              (gates.get i).op.eval ((gates.get i).inputs.map fun b =>
                (run gates (List.ofFn x)).getD b false) := by
            have hlen : (List.ofFn x).length = 13 := by simp
            simpa [hlen] using run_getD_gate gates (List.ofFn x) i
              (by simpa [hlen] using (hno_const i).2)
          have ht : (run gates (List.ofFn x)).getD (13 + (i : ℕ)) false = true := by
            simpa [eval_eq_run, hwi] using hw_true
          rw [hgate, hor] at ht
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at ht
          rcases ht with ⟨_, ⟨a, ha, rfl⟩, ha_true⟩
          have halt : a < w := by
            have := (hno_const i).2 a ha
            omega
          have ha_cone : InOrCone gates g a :=
            inOrCone_step gates g i a (by simpa [hwi] using hw_cone) hor ha
          exact ih a halt ha_cone ha_true

lemma one_side (gates : List Gate) (g : ℕ)
    (La Lb : Finset (Fin 13)) (u0 u1 c : Fin 13)
    (hbasis : ∀ gt ∈ gates,
      (gt.op = GateOp.and ∨ gt.op = GateOp.or) ∧ gt.inputs.length ≤ 2)
    (hno_const : ∀ i : Fin gates.length,
      1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ))
    (hu0 : u0 ∉ Lb) (hu1 : u1 ∉ La) (hinter : La ∩ Lb = {c})
    (hfalse_a : Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ La))) = false)
    (hfalse_b : Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ Lb))) = false)
    (hcard : 2 ≤ (La.filter (fun p => Circuit.eval ⟨gates, g⟩
      (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ u0 ∧ v = u1)))) = true)).card) :
    ∃ Y : ℕ, InOrCone gates g Y ∧
      (∃ i : Fin gates.length, Y = 13 + (i : ℕ) ∧ (gates.get i).op = GateOp.and) ∧
      ∃ p ∈ La, p ≠ u0 ∧ p ≠ c ∧ Circuit.eval ⟨gates, Y⟩
        (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ u0 ∧ v = u1)))) = true := by
  let test : Fin 13 → Fin 13 → Bool := fun p v => decide (v = p ∨ (p ≠ u0 ∧ v = u1))
  let F : Finset (Fin 13) := La.filter (fun p => Circuit.eval ⟨gates, g⟩ (List.ofFn (test p)) = true)
  have hu0_not_mem : u0 ∉ F := by
    intro hmem
    have ht : Circuit.eval ⟨gates, g⟩ (List.ofFn (test u0)) = true := (Finset.mem_filter.mp hmem).2
    have hmon := run_mono gates (fun gt hgt => (hbasis gt hgt).1)
      (List.ofFn (test u0)) (List.ofFn (fun v : Fin 13 => decide (v ∉ Lb))) (by simp)
      (by
        intro k hk
        by_cases hk13 : k < 13
        · simp only [test, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hk13, ↓reduceDIte,
            Option.getD_some, decide_eq_true_eq] at hk ⊢
          rcases hk with hvu | ⟨hne, _⟩
          · intro hmem_b
            have : (⟨k, hk13⟩ : Fin 13) = u0 := hvu
            rw [this] at hmem_b
            exact hu0 hmem_b
          · exact False.elim (hne rfl)
        · have hge : (List.ofFn (test u0)).length ≤ k := by simp; omega
          rw [getD_ge_length _ k hge] at hk
          exact Bool.noConfusion hk)
      g ht
    rw [eval_eq_run] at hfalse_b
    rw [hfalse_b] at hmon
    exact Bool.noConfusion hmon
  have hex_p : ∃ p ∈ F, p ≠ c := by
    by_contra hnone
    push Not at hnone
    have hsub : F ⊆ {c} := fun p hp => Finset.mem_singleton.mpr (hnone p hp)
    have hle : F.card ≤ ({c} : Finset (Fin 13)).card := Finset.card_le_card hsub
    simp at hle
    have hcard' : 2 ≤ F.card := hcard
    omega
  rcases hex_p with ⟨p, hpF, hpc⟩
  have hpLa : p ∈ La := (Finset.mem_filter.mp hpF).1
  have hpg : Circuit.eval ⟨gates, g⟩ (List.ofFn (test p)) = true := (Finset.mem_filter.mp hpF).2
  have hpu0 : p ≠ u0 := fun heq => hu0_not_mem (heq ▸ hpF)
  have hpLb : p ∉ Lb := by
    intro hpLb
    have hmem_inter : p ∈ La ∩ Lb := Finset.mem_inter.mpr ⟨hpLa, hpLb⟩
    rw [hinter, Finset.mem_singleton] at hmem_inter
    exact hpc hmem_inter
  have hno_inp : ∀ v : Fin 13, test p v = true → ¬ InOrCone gates g v.val := by
    intro v hv hcone
    have hv' : v = p ∨ (p ≠ u0 ∧ v = u1) := by
      simpa [test] using hv
    rcases hv' with rfl | ⟨_, rfl⟩
    · have hvf := inOrCone_eval_false gates g v.val (fun w : Fin 13 => decide (w ∉ Lb))
        hno_const hcone hfalse_b
      rw [eval_eq_run, run_getD_lt] at hvf
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, v.isLt, ↓reduceDIte,
          Option.getD_some, decide_eq_false_iff_not, not_not] at hvf
        exact hpLb hvf
      · simp
    · have hvf := inOrCone_eval_false gates g v.val (fun w : Fin 13 => decide (w ∉ La))
        hno_const hcone hfalse_a
      rw [eval_eq_run, run_getD_lt] at hvf
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, v.isLt, ↓reduceDIte,
          Option.getD_some, decide_eq_false_iff_not, not_not] at hvf
        exact hu1 hvf
      · simp
  rcases find_and_atom gates g (test p) hbasis hno_const hno_inp g (inOrCone_self gates g) hpg with
    ⟨Y, hYcone, hYand, hYtrue⟩
  exact ⟨Y, hYcone, hYand, p, hpLa, hpu0, hpc, hYtrue⟩

lemma plane_nonmem_aux :
    (∀ l ∈ ({4, 10, 12} : Finset (Fin 13)),
      (1 : Fin 13) ∉ ({l, l + 1, l + 3, l + 9} : Finset (Fin 13))) ∧
    (∀ m ∈ ({1, 5, 11} : Finset (Fin 13)),
      (0 : Fin 13) ∉ ({m, m + 1, m + 3, m + 9} : Finset (Fin 13))) := by
  decide

end PEqualNP.Outside.L_meta_1572

theorem PEqualNP.Outside.L_meta_1572 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (g : ℕ) (l m c : Fin 13),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ)) → l ∈ ({4, 10, 12} : Finset (Fin 13)) → m ∈ ({1, 5, 11} : Finset (Fin 13)) → L l ∩ L m = {c} →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false →
    (2 ≤ ((L l).filter (fun p => PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 0 ∧ v = 1)))) = true)).card →
      ∃ Y : ℕ, (∀ S : Set ℕ, g ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → Y ∈ S) ∧ (∃ i : Fin gates.length, Y = 13 + (i : ℕ) ∧ (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ ∃ p ∈ L l, p ≠ 0 ∧ p ≠ c ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 0 ∧ v = 1)))) = true) ∧
    (2 ≤ ((L m).filter (fun p => PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 1 ∧ v = 0)))) = true)).card →
      ∃ Y : ℕ, (∀ S : Set ℕ, g ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → Y ∈ S) ∧ (∃ i : Fin gates.length, Y = 13 + (i : ℕ) ∧ (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ ∃ p ∈ L m, p ≠ 1 ∧ p ≠ c ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 1 ∧ v = 0)))) = true) := by
  intro L hL gates g l m c hbasis hno_const hl hm hinter hfalse_l hfalse_m
  have h1l : (1 : Fin 13) ∉ L l := by
    rw [hL l]
    exact PEqualNP.Outside.L_meta_1572.plane_nonmem_aux.1 l hl
  have h0m : (0 : Fin 13) ∉ L m := by
    rw [hL m]
    exact PEqualNP.Outside.L_meta_1572.plane_nonmem_aux.2 m hm
  refine ⟨?_, ?_⟩
  · intro hcard
    exact PEqualNP.Outside.L_meta_1572.one_side gates g (L l) (L m) 0 1 c
      hbasis hno_const h0m h1l hinter hfalse_l hfalse_m hcard
  · intro hcard
    exact PEqualNP.Outside.L_meta_1572.one_side gates g (L m) (L l) 1 0 c
      hbasis hno_const h1l h0m (by rw [Finset.inter_comm]; exact hinter) hfalse_m hfalse_l hcard
