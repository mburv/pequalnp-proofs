import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Lmeta612

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem foldl_step_length (G : List Gate) (w : List Bool) :
    (G.foldl step w).length = w.length + G.length := by
  induction G generalizing w with
  | nil => simp
  | cons g G ih => rw [List.foldl_cons, ih]; simp [step]; omega

theorem getD_append_lt (l l' : List Bool) (i : ℕ) (hi : i < l.length) :
    (l ++ l').getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_of_length_le (l : List Bool) (i : ℕ) (hi : l.length ≤ i) :
    l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

theorem foldl_step_getD (G : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (G.foldl step w).getD i false = w.getD i false := by
  induction G generalizing w with
  | nil => rfl
  | cons g G ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    exact getD_append_lt _ _ _ hi

theorem foldl_step_getD_gate (G : List Gate) (w : List Bool) (t : ℕ) (ht : t < G.length) :
    (G.foldl step w).getD (w.length + t) false =
      (G[t]).op.eval ((G[t]).inputs.map fun i => ((G.take t).foldl step w).getD i false) := by
  have hsplit : G = G.take t ++ G[t] :: G.drop (t + 1) := by
    simp [List.take_append_drop]
  conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
  rw [foldl_step_getD _ _ _ (by simp only [step, List.length_append, List.length_singleton, foldl_step_length, List.length_take, Nat.min_eq_left ht.le]; omega)]
  simp only [step]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp only [foldl_step_length, List.length_take, Nat.min_eq_left ht.le]; omega)]
  simp [foldl_step_length, Nat.min_eq_left ht.le]

theorem foldl_take_getD (G : List Gate) (w : List Bool) (t i : ℕ)
    (hi : i < ((G.take t).foldl step w).length) :
    (G.foldl step w).getD i false = ((G.take t).foldl step w).getD i false := by
  conv_lhs => rw [← List.take_append_drop t G, List.foldl_append]
  exact foldl_step_getD _ _ _ hi

theorem gate_value (G : List Gate) (w : List Bool) (t : ℕ) (ht : t < G.length) :
    (G.foldl step w).getD (w.length + t) false =
      (G[t]).op.eval ((G[t]).inputs.map fun i =>
        if i < w.length + t then (G.foldl step w).getD i false else false) := by
  rw [foldl_step_getD_gate G w t ht]
  congr 1
  apply List.map_congr_left
  intro i _
  have hlen : ((G.take t).foldl step w).length = w.length + t := by
    rw [foldl_step_length, List.length_take, Nat.min_eq_left ht.le]
  split_ifs with h
  · exact (foldl_take_getD G w t i (by rw [hlen]; exact h)).symm
  · exact getD_of_length_le _ _ (by rw [hlen]; omega)

def val (C : Circuit) (n : ℕ) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

theorem val_input (C : Circuit) (n : ℕ) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val C n x w = x ⟨w, hw⟩ := by
  unfold val
  rw [wires_eq, foldl_step_getD _ _ _ (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

theorem val_none (C : Circuit) (n : ℕ) (x : Fin n → Bool) (j : ℕ)
    (hg : C.gates[j]? = none) : val C n x (n + j) = false := by
  unfold val
  apply getD_of_length_le
  rw [wires_eq, foldl_step_length]
  have := List.getElem?_eq_none_iff.mp hg
  simp only [List.length_ofFn]
  omega

theorem val_gate (C : Circuit) (n : ℕ) (x : Fin n → Bool) (j : ℕ) (h : Gate)
    (hg : C.gates[j]? = some h) :
    val C n x (n + j) =
      h.op.eval (h.inputs.map fun i => if i < n + j then val C n x i else false) := by
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp hg
  have := gate_value C.gates (List.ofFn x) j hj
  simp only [List.length_ofFn] at this
  exact this

theorem val_or (C : Circuit) (n : ℕ) (x : Fin n → Bool) (j : ℕ) (h : Gate)
    (hg : C.gates[j]? = some h) (hop : h.op = GateOp.or) :
    val C n x (n + j) = true ↔ ∃ w ∈ h.inputs, w < n + j ∧ val C n x w = true := by
  rw [val_gate C n x j h hg, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
  constructor
  · rintro ⟨w, hw, hv⟩
    by_cases hlt : w < n + j
    · exact ⟨w, hw, hlt, by simpa [hlt] using hv⟩
    · simp [hlt] at hv
  · rintro ⟨w, hw, hlt, hv⟩
    exact ⟨w, hw, by simpa [hlt] using hv⟩

theorem val_and (C : Circuit) (n : ℕ) (x : Fin n → Bool) (j : ℕ) (h : Gate)
    (hg : C.gates[j]? = some h) (hop : h.op = GateOp.and) :
    val C n x (n + j) = true ↔ ∀ w ∈ h.inputs, w < n + j ∧ val C n x w = true := by
  rw [val_gate C n x j h hg, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id]
  constructor
  · intro hall w hw
    have hv := hall w hw
    by_cases hlt : w < n + j
    · exact ⟨hlt, by simpa [hlt] using hv⟩
    · simp [hlt] at hv
  · intro hall w hw
    obtain ⟨hlt, hv⟩ := hall w hw
    simpa [hlt] using hv


def e0 {n : ℕ} : Fin n → Bool := fun _ => false

def e1 {n : ℕ} (t : Fin n) : Fin n → Bool := fun i => decide (i = t)

def e2 {n : ℕ} (c t : Fin n) : Fin n → Bool := fun i => decide (i = c ∨ i = t)

variable {n : ℕ} {C : Circuit}

theorem gate_kind (hC : Monotone2 C) {j : ℕ} {g : Gate} (hg : C.gates[j]? = some g) :
    g.op = GateOp.and ∨ g.op = GateOp.or := by
  have h := (hC g (List.mem_of_getElem? hg)).1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  exact h

theorem fanin_le (hC : Monotone2 C) {j : ℕ} {g : Gate} (hg : C.gates[j]? = some g) :
    g.inputs.length ≤ 2 :=
  (hC g (List.mem_of_getElem? hg)).2

noncomputable def support (C : Circuit) (n : ℕ) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => val C n (e1 i) w = true)

theorem mem_support (C : Circuit) (n : ℕ) (w : ℕ) (i : Fin n) :
    i ∈ support C n w ↔ val C n (e1 i) w = true := by
  simp [support]

theorem support_input (C : Circuit) (n : ℕ) (w : ℕ) (hw : w < n) :
    support C n w = {⟨w, hw⟩} := by
  ext i
  rw [mem_support]
  rw [val_input C n (e1 i) w hw]
  simp [e1, Fin.ext_iff, eq_comm]

variable {n : ℕ} {C : Circuit}

def touches (C : Circuit) (n t : ℕ) (i j : Fin n) : Prop :=
  ∃ g : Gate, C.gates[t]? = some g ∧ g.op = GateOp.or ∧
    val C n e0 (n + t) = false ∧
    i ∈ support C n (n + t) ∧ j ∈ support C n (n + t)

def linked (C : Circuit) (n k : ℕ) (i j : Fin n) : Prop :=
  Relation.ReflTransGen (fun a b => ∃ t < k, touches C n t a b) i j

theorem linked_refl (C : Circuit) (n k : ℕ) (i : Fin n) : linked C n k i i :=
  Relation.ReflTransGen.refl

theorem touches_comm (C : Circuit) (n t : ℕ) (i j : Fin n) :
    touches C n t i j → touches C n t j i := by
  rintro ⟨g, hg, hop, hem, hi, hj⟩
  exact ⟨g, hg, hop, hem, hj, hi⟩

theorem linked_symm (C : Circuit) (n k : ℕ) {i j : Fin n} (h : linked C n k i j) :
    linked C n k j i := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
    obtain ⟨t, ht, hto⟩ := hstep
    exact Relation.ReflTransGen.trans
      (Relation.ReflTransGen.single ⟨t, ht, touches_comm C n t _ _ hto⟩) ih

theorem linked_trans (C : Circuit) (n k : ℕ) {i j m : Fin n}
    (hij : linked C n k i j) (hjm : linked C n k j m) : linked C n k i m :=
  Relation.ReflTransGen.trans hij hjm

open Classical in
noncomputable def classRep (C : Circuit) (n k : ℕ) (N : Finset (Fin n)) : Finset (Fin n) :=
  N.filter fun i => ∀ j ∈ N, linked C n k j i → i ≤ j

theorem classRep_zero (C : Circuit) (n : ℕ) (N : Finset (Fin n)) :
    classRep C n 0 N = N := by
  classical
  ext i
  simp only [classRep, Finset.mem_filter]
  constructor
  · intro h
    exact h.1
  · intro hi
    refine ⟨hi, ?_⟩
    intro j hj hlin
    cases hlin with
    | refl => exact le_rfl
    | tail _ hst =>
      obtain ⟨t, ht, _⟩ := hst
      omega

theorem classRep_card_zero (C : Circuit) (n : ℕ) (N : Finset (Fin n)) :
    (classRep C n 0 N).card = N.card := by
  rw [classRep_zero]

theorem mem_support_or (hC : Monotone2 C) {j : ℕ} {g : Gate}
    (hg : C.gates[j]? = some g) (hop : g.op = GateOp.or) (i : Fin n) :
    i ∈ support C n (n + j) ↔ ∃ a ∈ g.inputs, a < n + j ∧ i ∈ support C n a := by
  rw [mem_support, val_or C n (e1 i) j g hg hop]
  constructor
  · rintro ⟨a, ha, hlt, hv⟩
    exact ⟨a, ha, hlt, (mem_support C n a i).2 hv⟩
  · rintro ⟨a, ha, hlt, hi⟩
    exact ⟨a, ha, hlt, (mem_support C n a i).1 hi⟩

theorem support_and_subset (hC : Monotone2 C) {j : ℕ} {g : Gate}
    (hg : C.gates[j]? = some g) (hop : g.op = GateOp.and)
    {a : ℕ} (ha : a ∈ g.inputs) (hlt : a < n + j) :
    support C n (n + j) ⊆ support C n a := by
  intro i hi
  rw [mem_support] at hi ⊢
  exact ((val_and C n (e1 i) j g hg hop).1 hi a ha).2

theorem support_linked (hC : Monotone2 C) (k w : ℕ)
    (hw : w < n ∨ (n ≤ w ∧ w - n < k ∧ w - n < C.gates.length))
    (hempty : val C n e0 w = false) :
    ∀ i j : Fin n, i ∈ support C n w → j ∈ support C n w → linked C n k i j := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro i j hi hj
    rcases hw with hlt | ⟨hn, hk, hlen⟩
    · have hsi := (mem_support C n w i).1 hi
      have hsj := (mem_support C n w j).1 hj
      rw [val_input C n _ w hlt] at hsi hsj
      have hi' : i = ⟨w, hlt⟩ := by simpa [e1, Fin.ext_iff, eq_comm] using hsi
      have hj' : j = ⟨w, hlt⟩ := by simpa [e1, Fin.ext_iff, eq_comm] using hsj
      subst hi'
      subst hj'
      exact linked_refl C n k _
    · have hjg : (w - n) < C.gates.length := hlen
      have hg : C.gates[w - n]? = some (C.gates[w - n]'hjg) := List.getElem?_eq_getElem hjg
      set g := C.gates[w - n]'hjg
      have hwj : w = n + (w - n) := by omega
      rcases gate_kind hC hg with hop | hop
      · have hiw : i ∈ support C n (n + (w - n)) := by rw [← hwj]; exact hi
        have hjw : j ∈ support C n (n + (w - n)) := by rw [← hwj]; exact hj
        have hempty_w : val C n e0 (n + (w - n)) = false := by rw [← hwj]; exact hempty
        by_cases hem : g.inputs = []
        · have htrue : val C n e0 (n + (w - n)) = true := by
            rw [val_and C n e0 (w - n) g hg hop]
            intro a ha
            simp [hem] at ha
          exact absurd htrue (by simpa using hempty_w)
        · have hex : ∃ a ∈ g.inputs, a < n + (w - n) ∧ val C n e0 a = false := by
            by_contra hno
            by_cases hdead : ∃ a ∈ g.inputs, n + (w - n) ≤ a
            · obtain ⟨a, ha, _⟩ := hdead
              have hnot : ¬ i ∈ support C n (n + (w - n)) := by
                intro hmem
                have hall := (val_and C n (e1 i) (w - n) g hg hop).1
                  ((mem_support C n _ i).1 hmem) a ha
                omega
              exact hnot hiw
            · have hlive : ∀ a, a ∈ g.inputs → a < n + (w - n) := by
                intro a ha
                by_contra hge
                exact hdead ⟨a, ha, by omega⟩
              have hpos : ∀ a, a ∈ g.inputs → val C n e0 a = true := by
                intro a ha
                cases hv : val C n e0 a with
                | true => rfl
                | false => exact (hno ⟨a, ha, hlive a ha, hv⟩).elim
              have htrue : val C n e0 (n + (w - n)) = true := by
                rw [val_and C n e0 (w - n) g hg hop]
                intro a ha
                exact ⟨hlive a ha, hpos a ha⟩
              exact absurd htrue (by simpa using hempty_w)
          obtain ⟨a, ha, hlt_an, ha_empty⟩ := hex
          have hall_i := (val_and C n (e1 i) (w - n) g hg hop).1
            ((mem_support C n _ i).1 hiw) a ha
          have hall_j := (val_and C n (e1 j) (w - n) g hg hop).1
            ((mem_support C n _ j).1 hjw) a ha
          have hlt_a : a < w := by omega
          have hi_a : i ∈ support C n a := by rw [mem_support]; exact hall_i.2
          have hj_a : j ∈ support C n a := by rw [mem_support]; exact hall_j.2
          have hcond : a < n ∨ (n ≤ a ∧ a - n < k ∧ a - n < C.gates.length) := by
            by_cases han : a < n
            · exact Or.inl han
            · refine Or.inr ⟨by omega, ?_, ?_⟩
              · have : a - n < w - n := by omega
                exact this.trans hk
              · have : a - n < w - n := by omega
                exact this.trans hlen
          exact ih a hlt_a hcond ha_empty i j hi_a hj_a
      · rw [hwj] at hi hj
        obtain ⟨ai, hai, hlti, hii⟩ := (mem_support_or hC hg hop i).1 hi
        obtain ⟨aj, haj, hltj, hij⟩ := (mem_support_or hC hg hop j).1 hj
        by_cases hsame : ai = aj
        · subst hsame
          have hcond : ai < n ∨ (n ≤ ai ∧ ai - n < k ∧ ai - n < C.gates.length) := by
            by_cases han : ai < n
            · exact Or.inl han
            · refine Or.inr ⟨by omega, ?_, ?_⟩
              · have : ai - n < w - n := by omega
                exact this.trans hk
              · have : ai - n < w - n := by omega
                exact this.trans hlen
          have hai_empty : val C n e0 ai = false := by
            cases hv : val C n e0 ai with
            | false => rfl
            | true =>
              have htor : val C n e0 (n + (w - n)) = true :=
                (val_or C n e0 (w - n) g hg hop).2 ⟨ai, hai, hlti, hv⟩
              rw [← hwj] at htor
              exact absurd htor (by simpa using hempty)
          exact ih ai (by omega) hcond hai_empty i j hii hij
        · -- different inputs: the OR gate itself links them, and its index is < k
          have hstep : ∃ t < k, touches C n t i j := by
            refine ⟨w - n, hk, ?_⟩
            refine ⟨g, hg, hop, ?_, hi, hj⟩
            rw [← hwj]
            exact hempty
          exact Relation.ReflTransGen.single hstep

def orAt (C : Circuit) (n t : ℕ) : Prop :=
  ∃ g : Gate, C.gates[t]? = some g ∧ g.op = GateOp.or ∧ val C n e0 (n + t) = false

theorem touches_orAt (C : Circuit) (n t : ℕ) (i j : Fin n) :
    touches C n t i j → orAt C n t := by
  rintro ⟨g, hg, hop, hem, _, _⟩
  exact ⟨g, hg, hop, hem⟩

theorem linked_succ_same (C : Circuit) (n k : ℕ) (h : ¬ orAt C n k) (i j : Fin n) :
    linked C n (k + 1) i j ↔ linked C n k i j := by
  constructor
  · intro hlin
    induction hlin with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hstep ih =>
      obtain ⟨t, ht, hto⟩ := hstep
      have htk : t < k := by
        have hne : t ≠ k := by
          intro heq
          exact h (heq ▸ touches_orAt C n t _ _ hto)
        omega
      exact Relation.ReflTransGen.tail ih ⟨t, htk, hto⟩
  · intro hlin
    induction hlin with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hstep ih =>
      obtain ⟨t, ht, hto⟩ := hstep
      exact Relation.ReflTransGen.tail ih ⟨t, by omega, hto⟩

open Classical in
noncomputable def orBefore (C : Circuit) (n k : ℕ) : Finset ℕ :=
  (Finset.range k).filter fun t => orAt C n t

theorem orBefore_zero (C : Circuit) (n : ℕ) : orBefore C n 0 = ∅ := by
  simp [orBefore]

theorem orBefore_succ_not (C : Circuit) (n k : ℕ) (h : ¬ orAt C n k) :
    orBefore C n (k + 1) = orBefore C n k := by
  classical
  ext t
  simp only [orBefore, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨ht, hor⟩
    have htk : t < k := by
      have hne : t ≠ k := fun heq => h (heq ▸ hor)
      omega
    exact ⟨htk, hor⟩
  · rintro ⟨ht, hor⟩
    exact ⟨by omega, hor⟩

theorem orBefore_succ_yes (C : Circuit) (n k : ℕ) (h : orAt C n k) :
    orBefore C n (k + 1) = insert k (orBefore C n k) := by
  classical
  ext t
  simp only [orBefore, Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
  constructor
  · rintro ⟨ht, hor⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp ht with hlt | heq
    · exact Or.inr ⟨hlt, hor⟩
    · exact Or.inl heq
  · rintro (rfl | ⟨ht, hor⟩)
    · exact ⟨by omega, h⟩
    · exact ⟨by omega, hor⟩

theorem classRep_same (C : Circuit) (n k : ℕ) (h : ¬ orAt C n k) (N : Finset (Fin n)) :
    classRep C n (k + 1) N = classRep C n k N := by
  classical
  ext i
  simp only [classRep, Finset.mem_filter]
  constructor
  · rintro ⟨hi, hmin⟩
    refine ⟨hi, ?_⟩
    intro j hj hlin
    exact hmin j hj ((linked_succ_same C n k h j i).mpr hlin)
  · rintro ⟨hi, hmin⟩
    refine ⟨hi, ?_⟩
    intro j hj hlin
    exact hmin j hj ((linked_succ_same C n k h j i).mp hlin)

theorem support_two_classes (hC : Monotone2 C) {k : ℕ} {g : Gate}
    (hg : C.gates[k]? = some g) (hop : g.op = GateOp.or)
    (hem : val C n e0 (n + k) = false) :
    ∃ L : Finset (Fin n), L.card ≤ 2 ∧ ∀ i ∈ support C n (n + k), ∃ r ∈ L, linked C n k i r := by
  classical
  -- each live input lies in one class; pick its minimum element as a representative
  have hfan := fanin_le hC hg
  let reps : List (Fin n) := g.inputs.filterMap fun a =>
    if hlt : a < n + k then
      if hempty : val C n e0 a = false then
        if hne : (support C n a).Nonempty then some ((support C n a).min' hne) else none
      else none
    else none
  have hlen : reps.length ≤ g.inputs.length := by
    simpa [reps] using List.length_filterMap_le (fun a =>
      if hlt : a < n + k then
        if hempty : val C n e0 a = false then
          if hne : (support C n a).Nonempty then some ((support C n a).min' hne) else none
        else none
      else none) g.inputs
  refine ⟨reps.toFinset, (List.toFinset_card_le _).trans (hlen.trans hfan), ?_⟩
  · intro i hi
    obtain ⟨a, ha, hlt, hia⟩ := (mem_support_or hC hg hop i).1 hi
    have ha_empty : val C n e0 a = false := by
      cases hv : val C n e0 a with
      | false => rfl
      | true =>
        have htor : val C n e0 (n + k) = true :=
          (val_or C n e0 k g hg hop).2 ⟨a, ha, hlt, hv⟩
        exact absurd htor (by simpa using hem)
    have hne : (support C n a).Nonempty := ⟨i, hia⟩
    have hmem : (support C n a).min' hne ∈ reps.toFinset := by
      rw [List.mem_toFinset]
      simp only [reps, List.mem_filterMap]
      refine ⟨a, ha, ?_⟩
      simp [hlt, ha_empty, hne]
    refine ⟨(support C n a).min' hne, hmem, ?_⟩
    have hcond : a < n ∨ (n ≤ a ∧ a - n < k ∧ a - n < C.gates.length) := by
      by_cases han : a < n
      · exact Or.inl han
      · refine Or.inr ⟨by omega, ?_, ?_⟩
        · omega
        · have hklen : k < C.gates.length := (List.getElem?_eq_some_iff.mp hg).1
          omega
    have hall := support_linked hC k a hcond ha_empty
    exact hall i ((support C n a).min' hne) hia (Finset.min'_mem _ _)

theorem card_image_merge {α : Type} [DecidableEq α]
    (D : Finset α) (color : α → ℕ) (c1 c2 : ℕ) :
    (D.image color).card ≤
      (D.image (fun x => if color x = c2 then c1 else color x)).card + 1 := by
  classical
  let color' := fun x => if color x = c2 then c1 else color x
  have hsub : D.image color ⊆ insert c2 (D.image color') := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    by_cases h : color x = c2
    · rw [h]
      exact Finset.mem_insert_self c2 _
    · apply Finset.mem_insert_of_mem
      exact Finset.mem_image.mpr ⟨x, hx, by simp [color', h]⟩
  calc
    (D.image color).card ≤ (insert c2 (D.image color')).card := Finset.card_le_card hsub
    _ ≤ (D.image color').card + 1 := Finset.card_insert_le _ _

theorem linked_succ_expand (C : Circuit) (n k : ℕ) (i j : Fin n)
    (h : orAt C n k) (hlin : linked C n (k + 1) i j) :
    linked C n k i j ∨
      ((∃ s ∈ support C n (n + k), linked C n k i s) ∧
        (∃ s ∈ support C n (n + k), linked C n k j s)) := by
  induction hlin with
  | refl => exact Or.inl Relation.ReflTransGen.refl
  | tail hprev hstep ih =>
    rename_i mid last
    obtain ⟨t, ht, hto⟩ := hstep
    rcases Nat.lt_succ_iff_lt_or_eq.mp ht with hlt | heq
    · rcases ih with hold | ⟨hstart, hmid⟩
      · exact Or.inl (Relation.ReflTransGen.tail hold ⟨t, hlt, hto⟩)
      · refine Or.inr ⟨hstart, ?_⟩
        obtain ⟨s, hs, hm⟩ := hmid
        have hback : linked C n k last mid :=
          Relation.ReflTransGen.single ⟨t, hlt, touches_comm C n t mid last hto⟩
        exact ⟨s, hs, linked_trans C n k hback hm⟩
    · subst heq
      obtain ⟨g, hg, hop, _, hmid, hlast⟩ := hto
      refine Or.inr ⟨?_, ⟨last, hlast, Relation.ReflTransGen.refl⟩⟩
      rcases ih with hold | ⟨hstart, _⟩
      · exact ⟨mid, hmid, hold⟩
      · exact hstart

theorem color_bound (hC : Monotone2 C) (k : ℕ) (D : Finset (Fin n)) :
    ∃ color : Fin n → ℕ,
      D.card ≤ (D.image color).card + (orBefore C n k).card ∧
      ∀ i j : Fin n, linked C n k i j → color i = color j := by
  classical
  induction k with
  | zero =>
    refine ⟨fun i => i.val, ?_, ?_⟩
    · have hinj : Function.Injective (fun i : Fin n => i.val) := Fin.val_injective
      rw [Finset.card_image_of_injective D hinj]
      simp [orBefore_zero]
    · intro i j hlin
      cases hlin with
      | refl => rfl
      | tail _ hst =>
        obtain ⟨t, ht, _⟩ := hst
        omega
  | succ k ih =>
    obtain ⟨color, hcard, hinv⟩ := ih
    by_cases hOr : orAt C n k
    · obtain ⟨g, hg, hop, hem⟩ := hOr
      obtain ⟨L, hL, hcover⟩ := support_two_classes hC hg hop hem
      have hsame : ∀ i j, linked C n k i j → color i = color j := hinv
      let cols : Finset ℕ := L.image color
      have hcols : cols.card ≤ 2 := (Finset.card_image_le (s := L) (f := color)).trans hL
      obtain ⟨c1, c2, hcol⟩ : ∃ c1 c2 : ℕ, ∀ r ∈ L, color r = c1 ∨ color r = c2 := by
        by_cases hzero : cols.card = 0
        · have hemL : L = ∅ := by
            by_contra hne
            obtain ⟨r, hr⟩ := Finset.nonempty_iff_ne_empty.mpr hne
            have : 0 < cols.card :=
              Finset.card_pos.mpr ⟨color r, Finset.mem_image.mpr ⟨r, hr, rfl⟩⟩
            omega
          exact ⟨0, 0, fun r hr => by simp [hemL] at hr⟩
        · by_cases hone : cols.card = 1
          · obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hone
            exact ⟨c, c, fun r hr => by
              have hmem : color r ∈ cols := Finset.mem_image.mpr ⟨r, hr, rfl⟩
              simpa [hc] using hmem⟩
          · have htwo : cols.card = 2 := by omega
            obtain ⟨a, b, _, hc⟩ := Finset.card_eq_two.mp htwo
            exact ⟨a, b, fun r hr => by
              have hmem : color r ∈ cols := Finset.mem_image.mpr ⟨r, hr, rfl⟩
              simpa [hc] using hmem⟩
      let color' : Fin n → ℕ := fun x => if color x = c2 then c1 else color x
      refine ⟨color', ?_, ?_⟩
      · have hm := card_image_merge D color c1 c2
        have hm' : (D.image color).card ≤ (D.image color').card + 1 := by
          simpa [color'] using hm
        rw [orBefore_succ_yes C n k ⟨g, hg, hop, hem⟩]
        have hnot : k ∉ orBefore C n k := by
          simp [orBefore, Finset.mem_filter, Finset.mem_range]
        rw [Finset.card_insert_of_notMem hnot]
        omega
      · intro i j hlin
        rcases linked_succ_expand C n k i j ⟨g, hg, hop, hem⟩ hlin with hold | ⟨hiS, hjS⟩
        · have heq := hsame i j hold
          simp [color', heq]
        · have hcolS (x : Fin n)
              (hx : ∃ s ∈ support C n (n + k), linked C n k x s) :
              color x = c1 ∨ color x = c2 := by
            obtain ⟨s, hs, hxs⟩ := hx
            obtain ⟨r, hr, hsr⟩ := hcover s hs
            have hx_r := hsame x r (linked_trans C n k hxs hsr)
            simpa [hx_r] using hcol r hr
          have hi' : color' i = c1 := by
            rcases hcolS i hiS with h | h
            · simp [color', h]
            · simp [color', h]
          have hj' : color' j = c1 := by
            rcases hcolS j hjS with h | h
            · simp [color', h]
            · simp [color', h]
          exact hi'.trans hj'.symm
    · refine ⟨color, ?_, ?_⟩
      · rw [orBefore_succ_not C n k ‹¬ orAt C n k›]
        exact hcard
      · intro i j hlin
        exact hinv i j ((linked_succ_same C n k ‹¬ orAt C n k› i j).mp hlin)

theorem support_card_le (hC : Monotone2 C) (k w : ℕ)
    (hw : w < n ∨ (n ≤ w ∧ w - n < k ∧ w - n < C.gates.length))
    (hempty : val C n e0 w = false) :
    (support C n w).card ≤ (orBefore C n k).card + 1 := by
  classical
  obtain ⟨color, hcard, hinv⟩ := color_bound hC k (support C n w)
  by_cases hne : (support C n w).Nonempty
  · obtain ⟨i0, hi0⟩ := hne
    have hsub : (support C n w).image color ⊆ {color i0} := by
      intro c hc
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hc
      have hcolor := hinv i i0 (support_linked hC k w hw hempty i i0 hi hi0)
      simp [hcolor]
    have hcard1 : ((support C n w).image color).card ≤ 1 := by
      have hle := Finset.card_le_card hsub
      simpa using hle
    omega
  · have hemptyS : support C n w = ∅ := by
      simpa [Finset.not_nonempty_iff_eq_empty] using hne
    simp [hemptyS]

theorem no_singleton {G : SimpleGraph (Fin n)}
    (hE : ∀ x : Fin n → Bool,
      val C n x C.output = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
    (i : Fin n) : val C n (e1 i) C.output = false := by
  cases hv : val C n (e1 i) C.output with
  | false => rfl
  | true =>
    obtain ⟨u, v, huv, hu, hv2⟩ := (hE (e1 i)).1 hv
    have hu' : u = i := by simpa [e1] using hu
    have hv' : v = i := by simpa [e1] using hv2
    subst hu'
    subst hv'
    exact (G.irrefl huv).elim

theorem no_empty {G : SimpleGraph (Fin n)}
    (hE : ∀ x : Fin n → Bool,
      val C n x C.output = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) :
    val C n e0 C.output = false := by
  cases hv : val C n e0 C.output with
  | false => rfl
  | true =>
    obtain ⟨u, v, _, hu, _⟩ := (hE e0).1 hv
    simp [e0] at hu

theorem yes_edge {G : SimpleGraph (Fin n)}
    (hE : ∀ x : Fin n → Bool,
      val C n x C.output = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
    {u v : Fin n} (huv : G.Adj u v) :
    val C n (e2 u v) C.output = true :=
  (hE (e2 u v)).2 ⟨u, v, huv, by simp [e2], by simp [e2]⟩

theorem val_mono (hC : Monotone2 C) {x y : Fin n → Bool}
    (hxy : ∀ i, x i = true → y i = true) :
    ∀ w, val C n x w = true → val C n y w = true := by
  intro w hw
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    rcases Nat.lt_or_ge w n with hlt | hge
    · rw [val_input C n x w hlt] at hw
      rw [val_input C n y w hlt]
      exact hxy ⟨w, hlt⟩ hw
    · by_cases hlen : w - n < C.gates.length
      · have hg : C.gates[w - n]? = some (C.gates[w - n]'(by omega)) :=
          List.getElem?_eq_getElem (by omega)
        set g := C.gates[w - n]'(by omega)
        have hwj : w = n + (w - n) := by omega
        rcases gate_kind hC hg with hop | hop
        · rw [hwj] at hw ⊢
          rw [val_and C n x (w - n) g hg hop] at hw
          rw [val_and C n y (w - n) g hg hop]
          intro a ha
          have hax := hw a ha
          exact ⟨hax.1, ih a (by omega) hax.2⟩
        · rw [hwj] at hw ⊢
          rw [val_or C n x (w - n) g hg hop] at hw
          obtain ⟨a, ha, hlt_a, hv⟩ := hw
          exact (val_or C n y (w - n) g hg hop).2 ⟨a, ha, hlt_a, ih a (by omega) hv⟩
      · have hwj : w = n + (w - n) := by omega
        rw [hwj] at hw
        rw [val_none C n x (w - n) (by
          rw [List.getElem?_eq_none]
          omega)] at hw
        simp at hw

theorem cross_edge {G : SimpleGraph (Fin n)}
    (hC : Monotone2 C)
    (hE : ∀ x : Fin n → Bool,
      val C n x C.output = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
    {j : ℕ} {g : Gate} (hg : C.gates[j]? = some g) (hop : g.op = GateOp.and)
    (hout : C.output = n + j)
    {a b : ℕ} (ha : a ∈ g.inputs) (hb : b ∈ g.inputs)
    (hlt_a : a < n + j) (hlt_b : b < n + j)
    (hab : a ≠ b)
    {p q : Fin n} (hp : p ∈ support C n a) (hq : q ∈ support C n b) (hpq : p ≠ q) :
    G.Adj p q := by
  have hmono_a : val C n (e2 p q) a = true :=
    val_mono hC (fun i hi => by
      have hi' : i = p := by simpa [e1, decide_eq_true_eq] using hi
      subst hi'
      simp [e2]) a ((mem_support C n a p).1 hp)
  have hmono_b : val C n (e2 p q) b = true :=
    val_mono hC (fun i hi => by
      have hi' : i = q := by simpa [e1, decide_eq_true_eq] using hi
      subst hi'
      simp [e2]) b ((mem_support C n b q).1 hq)
  have honly : ∀ w ∈ g.inputs, w = a ∨ w = b := by
    intro w hw
    by_contra hne
    push Not at hne
    classical
    have hcard : ({a, b, w} : Finset ℕ).card ≤ g.inputs.length := by
      calc
        ({a, b, w} : Finset ℕ).card ≤ g.inputs.toFinset.card := by
          apply Finset.card_le_card
          intro y hy
          simp only [Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with rfl | rfl | rfl
          · exact List.mem_toFinset.mpr ha
          · exact List.mem_toFinset.mpr hb
          · exact List.mem_toFinset.mpr hw
        _ ≤ g.inputs.length := List.toFinset_card_le _
    have h3 : ({a, b, w} : Finset ℕ).card = 3 := by
      refine (Finset.card_eq_three).2 ⟨a, b, w, hab, hne.1.symm, hne.2.symm, rfl⟩
    have hfan := fanin_le hC hg
    omega
  have hAnd : val C n (e2 p q) (n + j) = true := by
    rw [val_and C n (e2 p q) j g hg hop]
    intro w hw
    rcases honly w hw with rfl | rfl
    · exact ⟨hlt_a, hmono_a⟩
    · exact ⟨hlt_b, hmono_b⟩
  rw [← hout] at hAnd
  obtain ⟨u, v, huv, hu, hv⟩ := (hE (e2 p q)).1 hAnd
  have hu' : u = p ∨ u = q := by simpa [e2] using hu
  have hv' : v = p ∨ v = q := by simpa [e2] using hv
  rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl
  · exact (G.irrefl huv).elim
  · exact huv
  · exact huv.symm
  · exact (G.irrefl huv).elim

theorem support_disjoint_of_and {G : SimpleGraph (Fin n)}
    (hC : Monotone2 C)
    (hE : ∀ x : Fin n → Bool,
      val C n x C.output = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
    {j : ℕ} {g : Gate} (hg : C.gates[j]? = some g) (hop : g.op = GateOp.and)
    (hout : C.output = n + j)
    {a b : ℕ} (ha : a ∈ g.inputs) (hb : b ∈ g.inputs)
    (hlt_a : a < n + j) (hlt_b : b < n + j) (hab : a ≠ b) :
    Disjoint (support C n a) (support C n b) := by
  classical
  rw [Finset.disjoint_left]
  intro i hiA hiB
  have honly : ∀ w ∈ g.inputs, w = a ∨ w = b := by
    intro w hw
    by_contra hne
    push Not at hne
    have hcard : ({a, b, w} : Finset ℕ).card ≤ g.inputs.length := by
      calc
        ({a, b, w} : Finset ℕ).card ≤ g.inputs.toFinset.card := by
          apply Finset.card_le_card
          intro y hy
          simp only [Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with rfl | rfl | rfl
          · exact List.mem_toFinset.mpr ha
          · exact List.mem_toFinset.mpr hb
          · exact List.mem_toFinset.mpr hw
        _ ≤ g.inputs.length := List.toFinset_card_le _
    have h3 : ({a, b, w} : Finset ℕ).card = 3 :=
      (Finset.card_eq_three).2 ⟨a, b, w, hab, hne.1.symm, hne.2.symm, rfl⟩
    have hfan := fanin_le hC hg
    omega
  have hAnd : val C n (e1 i) (n + j) = true := by
    rw [val_and C n (e1 i) j g hg hop]
    intro w hw
    rcases honly w hw with hwa | hwb
    · rw [hwa]
      exact ⟨hlt_a, (mem_support C n a i).1 hiA⟩
    · rw [hwb]
      exact ⟨hlt_b, (mem_support C n b i).1 hiB⟩
  rw [← hout] at hAnd
  exact Bool.eq_false_iff.mp (no_singleton hE i) hAnd

theorem two_members {α : Type} [DecidableEq α] (s : Finset α) (hs : 2 ≤ s.card) :
    ∃ i j, i ∈ s ∧ j ∈ s ∧ i ≠ j := by
  classical
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (by omega : 0 < s.card)
  have hpos : 0 < (s.erase i).card := by
    rw [Finset.card_erase_of_mem hi]
    omega
  obtain ⟨j, hj⟩ := Finset.card_pos.mp hpos
  exact ⟨i, j, hi, Finset.mem_of_mem_erase hj, (Finset.ne_of_mem_erase hj).symm⟩

theorem exists_small_side {G : SimpleGraph (Fin n)}
    (hC : Monotone2 C)
    (hC4 : ∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a)
    (hE : ∀ x : Fin n → Bool,
      val C n x C.output = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
    (hedge : ∃ u v, G.Adj u v)
    {j : ℕ} {g : Gate} (hg : C.gates[j]? = some g) (hop : g.op = GateOp.and)
    (hout : C.output = n + j) :
    ∃ w ∈ g.inputs, w < n + j ∧ (support C n w).card ≤ 1 := by
  classical
  by_contra hno
  push Not at hno
  obtain ⟨u0, v0, huv0⟩ := hedge
  have htrue := yes_edge hE huv0
  rw [hout] at htrue
  have hlive : ∀ w ∈ g.inputs, w < n + j := by
    intro w hw
    by_contra hge
    rw [val_and C n (e2 u0 v0) j g hg hop] at htrue
    exact hge (htrue w hw).1
  have hbig : ∀ w ∈ g.inputs, 2 ≤ (support C n w).card := by
    intro w hw
    have hgt : 1 < (support C n w).card := hno w hw (hlive w hw)
    omega
  let S : Finset ℕ := g.inputs.toFinset
  have hSne : S.Nonempty := by
    have hne : g.inputs ≠ [] := by
      intro hem
      have ht : val C n e0 (n + j) = true := by
        rw [val_and C n e0 j g hg hop]
        intro w hw
        simp [hem] at hw
      rw [← hout] at ht
      exact Bool.eq_false_iff.mp (no_empty hE) ht
    obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil _ hne
    exact ⟨w, List.mem_toFinset.mpr hw⟩
  have hScard : S.card ≤ 2 := (List.toFinset_card_le _).trans (fanin_le hC hg)
  have hSpos : 0 < S.card := Finset.card_pos.mpr hSne
  have hSge : S.card = 1 ∨ S.card = 2 := by omega
  rcases hSge with h1 | h2
  · obtain ⟨w, hwS⟩ := Finset.card_eq_one.mp h1
    have hw : w ∈ g.inputs := by
      have : w ∈ S := by simp [hwS]
      exact List.mem_toFinset.mp this
    have hlt := hlive w hw
    obtain ⟨i, hi⟩ := Finset.card_pos.mp (lt_of_lt_of_le (by omega : 0 < 2) (hbig w hw))
    have hAnd : val C n (e1 i) (n + j) = true := by
      rw [val_and C n (e1 i) j g hg hop]
      intro a ha
      have haS : a ∈ S := List.mem_toFinset.mpr ha
      have haw : a = w := by simpa [hwS] using haS
      rw [haw]
      exact ⟨hlt, (mem_support C n w i).1 hi⟩
    rw [← hout] at hAnd
    exact Bool.eq_false_iff.mp (no_singleton hE i) hAnd
  · obtain ⟨a, b, haS, hbS, hab⟩ := two_members S (by omega)
    have ha : a ∈ g.inputs := List.mem_toFinset.mp haS
    have hb : b ∈ g.inputs := List.mem_toFinset.mp hbS
    have hlta := hlive a ha
    have hltb := hlive b hb
    have hdis := support_disjoint_of_and hC hE hg hop hout ha hb hlta hltb hab
    obtain ⟨a1, a2, ha1, ha2, ha12⟩ := two_members (support C n a) (hbig a ha)
    obtain ⟨b1, b2, hb1, hb2, hb12⟩ := two_members (support C n b) (hbig b hb)
    have hab1 : a1 ≠ b1 := by
      intro h
      exact Finset.disjoint_left.mp hdis ha1 (h ▸ hb1)
    have hab2 : a1 ≠ b2 := by
      intro h
      exact Finset.disjoint_left.mp hdis ha1 (h ▸ hb2)
    have ha2b1 : a2 ≠ b1 := by
      intro h
      exact Finset.disjoint_left.mp hdis ha2 (h ▸ hb1)
    have ha2b2 : a2 ≠ b2 := by
      intro h
      exact Finset.disjoint_left.mp hdis ha2 (h ▸ hb2)
    have e11 := cross_edge hC hE hg hop hout ha hb hlta hltb hab ha1 hb1 hab1
    have e21 := cross_edge hC hE hg hop hout ha hb hlta hltb hab ha2 hb1 ha2b1
    have e22 := cross_edge hC hE hg hop hout ha hb hlta hltb hab ha2 hb2 ha2b2
    have e12 := cross_edge hC hE hg hop hout ha hb hlta hltb hab ha1 hb2 hab2
    exact (hC4 a1 b1 a2 b2 hab1 ha12 hab2 ha2b1.symm hb12 ha2b2 e11 e21.symm e22)
      e12.symm

def readsWire (C : Circuit) (n u v : ℕ) : Prop :=
  n ≤ u ∧ u - n < C.gates.length ∧ ∃ g : Gate, C.gates[u - n]? = some g ∧ v ∈ g.inputs ∧ v < u

def inCone (C : Circuit) (n root gate : ℕ) : Prop :=
  root = n + gate ∨ Relation.ReflTransGen (readsWire C n) root (n + gate)

open Classical in
noncomputable def cone (C : Circuit) (n root : ℕ) : Finset ℕ :=
  (Finset.range C.size).filter fun j => inCone C n root j

theorem cone_card_le_size (C : Circuit) (n root : ℕ) : (cone C n root).card ≤ C.size := by
  classical
  have hsub : cone C n root ⊆ Finset.range C.size := fun j hj => (Finset.mem_filter.mp hj).1
  simpa using Finset.card_le_card hsub

theorem val_eval (x : Fin n → Bool) :
    val C n x C.output = C.eval (List.ofFn x) := by
  simp [val, Circuit.eval, wires_eq]

noncomputable def coneW (C : Circuit) (n w : ℕ) : Finset ℕ :=
  if h : n ≤ w ∧ w - n < C.gates.length then
    let g := C.gates[w - n]'h.2
    insert (w - n) (g.inputs.foldl (fun s a => if a < w then s ∪ coneW C n a else s) (∅ : Finset ℕ))
  else
    ∅
termination_by w
decreasing_by
  omega

theorem coneW_input {w : ℕ} (hw : w < n) : coneW C n w = ∅ := by
  unfold coneW
  have hnot : ¬ (n ≤ w ∧ w - n < C.gates.length) := by
    intro h
    omega
  simp [hnot]

theorem fold_cone_subset {w : ℕ} (inputs : List ℕ) (s : Finset ℕ)
    (hs : s ⊆ Finset.range C.size)
    (ih : ∀ a, a < w → coneW C n a ⊆ Finset.range C.size) :
    inputs.foldl (fun s a => if a < w then s ∪ coneW C n a else s) s ⊆ Finset.range C.size := by
  induction inputs generalizing s with
  | nil => simpa
  | cons a as ihf =>
    by_cases ha : a < w
    · have hnext : s ∪ coneW C n a ⊆ Finset.range C.size := by
        intro x hx
        rcases Finset.mem_union.mp hx with hx | hx
        · exact hs hx
        · exact (ih a ha) hx
      simpa [ha] using ihf (s ∪ coneW C n a) hnext
    · simpa [ha] using ihf s hs

theorem coneW_subset (w : ℕ) : coneW C n w ⊆ Finset.range C.size := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    rw [coneW]
    by_cases h : n ≤ w ∧ w - n < C.gates.length
    · simp only [h, ↓reduceDIte]
      intro j hj
      have hlt : w - n < C.gates.length := h.2
      rcases Finset.mem_insert.mp hj with rfl | hfold
      · exact Finset.mem_range.mpr hlt
      · exact fold_cone_subset (C.gates[w - n]'hlt).inputs ∅ (by simp) ih hfold
    · simp [h]

theorem coneW_card_le (w : ℕ) : (coneW C n w).card ≤ C.size := by
  simpa using Finset.card_le_card (coneW_subset (C := C) (n := n) w)

open Classical in
noncomputable def neighbors (G : SimpleGraph (Fin n)) (v : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun u => G.Adj v u)

theorem one_gate {G : SimpleGraph (Fin n)}
    (hE : ∀ x : Fin n → Bool,
      val C n x C.output = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
    (u v : Fin n) (huv : G.Adj u v) : 1 ≤ C.size := by
  have ht := yes_edge hE huv
  by_contra h0
  have hsize : C.gates.length = 0 := by
    simp only [Circuit.size] at h0
    omega
  have hout : C.output < n ∨ n ≤ C.output := lt_or_ge C.output n
  rcases hout with hlt | hge
  · have hsing : val C n (e1 ⟨C.output, hlt⟩) C.output = true := by
      rw [val_input C n _ _ hlt]
      simp [e1]
    exact Bool.eq_false_iff.mp (no_singleton hE _) hsing
  · have hfalse : val C n (e2 u v) C.output = false := by
      rw [val, wires_eq]
      apply getD_of_length_le
      rw [foldl_step_length, List.length_ofFn, hsize]
      exact hge
    exact Bool.eq_false_iff.mp hfalse ht

theorem coneW_eq {w : ℕ} :
    coneW C n w =
      if h : n ≤ w ∧ w - n < C.gates.length then
        insert (w - n)
          ((C.gates[w - n]'h.2).inputs.foldl (fun s a => if a < w then s ∪ coneW C n a else s) ∅)
      else
        ∅ := by
  rw [coneW.eq_def]

end PEqualNP.Outside.Lmeta612
