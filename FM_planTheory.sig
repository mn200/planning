signature FM_planTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val exec_plan_primitive_def : thm
    val plan_def : thm
    val planning_problem_def : thm
    val problem_A : thm
    val problem_A_fupd : thm
    val problem_G : thm
    val problem_G_fupd : thm
    val problem_I : thm
    val problem_I_fupd : thm
    val problem_TY_DEF : thm
    val problem_case_def : thm
    val problem_size_def : thm
    val state_list_primitive_def : thm
    val state_set_def : thm
    val state_succ_def : thm

  (*  Theorems  *)
    val CARD_INJ_IMAGE_2 : thm
    val EXISTS_problem : thm
    val FDOM_state_succ : thm
    val FINITE_states : thm
    val FORALL_problem : thm
    val IS_PREFIX_MEM : thm
    val IS_SUFFIX_MEM : thm
    val LENGTH_INJ_PREFIXES : thm
    val LENGTH_state_set : thm
    val MEM_LAST' : thm
    val MEM_statelist_FDOM : thm
    val NIL_NOTIN_stateset : thm
    val card_of_set_of_all_possible_states : thm
    val card_union' : thm
    val construction_of_all_possible_states_lemma : thm
    val cycle_removal_lemma : thm
    val datatype_problem : thm
    val empty_state_list_lemma : thm
    val exec_plan_Append : thm
    val exec_plan_def : thm
    val exec_plan_ind : thm
    val general_theorem : thm
    val general_theorem' : thm
    val lemma_1 : thm
    val lemma_1_1 : thm
    val lemma_1_1_1 : thm
    val lemma_2 : thm
    val lemma_2_1 : thm
    val lemma_2_1_1 : thm
    val lemma_2_1_1_1 : thm
    val lemma_2_1_1_2 : thm
    val lemma_2_2 : thm
    val lemma_2_2_1 : thm
    val lemma_2_3_1_1 : thm
    val lemma_2_3_1_2 : thm
    val lemma_2_3_1_2_1 : thm
    val lemma_2_3_1_3_1 : thm
    val lemma_2_3_1_4 : thm
    val lemma_2_3_1_thm : thm
    val lemma_2_3_2 : thm
    val lemma_2_3_2_1 : thm
    val lemma_3 : thm
    val lemma_3_1 : thm
    val lemma_temp : thm
    val main_lemma : thm
    val plan_CONS : thm
    val problem_11 : thm
    val problem_Axiom : thm
    val problem_accessors : thm
    val problem_accfupds : thm
    val problem_case_cong : thm
    val problem_component_equality : thm
    val problem_fn_updates : thm
    val problem_fupdcanon : thm
    val problem_fupdcanon_comp : thm
    val problem_fupdfupds : thm
    val problem_fupdfupds_comp : thm
    val problem_induction : thm
    val problem_literal_11 : thm
    val problem_literal_nchotomy : thm
    val problem_nchotomy : thm
    val problem_updates_eq_literal : thm
    val state_list_def : thm
    val state_list_ind : thm
    val state_list_length_lemma : thm
    val state_set_card : thm
    val state_set_finite : thm
    val state_set_thm : thm

  val FM_plan_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [finite_map] Parent theory of "FM_plan"

   [sublist] Parent theory of "FM_plan"

   [exec_plan_primitive_def]  Definition

      |- exec_plan =
         WFREC (@R. WF R ∧ ∀as a s. R (state_succ s a,as) (s,a::as))
           (λexec_plan a'.
              case a' of
                (s,[]) => I s
              | (s,a::as) => I (exec_plan (state_succ s a,as)))

   [plan_def]  Definition

      |- ∀PROB as.
           plan (PROB,as) ⇔
           (planning_problem PROB ∧ (exec_plan (PROB.I,as) = PROB.G)) ∧
           set as ⊆ PROB.A

   [planning_problem_def]  Definition

      |- ∀PROB.
           planning_problem PROB ⇔
           (∀a.
              a ∈ PROB.A ⇒
              FDOM (SND a) ⊆ FDOM PROB.I ∧ FDOM (FST a) ⊆ FDOM PROB.I) ∧
           (FDOM PROB.G = FDOM PROB.I)

   [problem_A]  Definition

      |- ∀f f0 f1. (problem f f0 f1).A = f0

   [problem_A_fupd]  Definition

      |- ∀f2 f f0 f1.
           problem f f0 f1 with A updated_by f2 = problem f (f2 f0) f1

   [problem_G]  Definition

      |- ∀f f0 f1. (problem f f0 f1).G = f1

   [problem_G_fupd]  Definition

      |- ∀f2 f f0 f1.
           problem f f0 f1 with G updated_by f2 = problem f f0 (f2 f1)

   [problem_I]  Definition

      |- ∀f f0 f1. (problem f f0 f1).I = f

   [problem_I_fupd]  Definition

      |- ∀f2 f f0 f1.
           problem f f0 f1 with I updated_by f2 = problem (f2 f) f0 f1

   [problem_TY_DEF]  Definition

      |- ∃rep.
           TYPE_DEFINITION
             (λa0'.
                ∀'problem' .
                  (∀a0'.
                     (∃a0 a1 a2.
                        a0' =
                        (λa0 a1 a2.
                           ind_type$CONSTR 0 (a0,a1,a2)
                             (λn. ind_type$BOTTOM)) a0 a1 a2) ⇒
                     'problem' a0') ⇒
                  'problem' a0') rep

   [problem_case_def]  Definition

      |- ∀a0 a1 a2 f. problem_CASE (problem a0 a1 a2) f = f a0 a1 a2

   [problem_size_def]  Definition

      |- ∀f a0 a1 a2.
           problem_size f (problem a0 a1 a2) =
           1 +
           (fmap_size (λk. 0) (λv. 1 + bool_size v) a0 +
            fmap_size (λk. 0) (λv. 1 + bool_size v) a2)

   [state_list_primitive_def]  Definition

      |- state_list =
         WFREC (@R. WF R ∧ ∀as a s. R (state_succ s a,as) (s,a::as))
           (λstate_list a'.
              case a' of
                (s,[]) => I []
              | (s,a::as) => I (s::state_list (state_succ s a,as)))

   [state_set_def]  Definition

      |- (∀s ss.
            state_set (s::ss) = [s] INSERT IMAGE (CONS s) (state_set ss)) ∧
         (state_set [] = ∅)

   [state_succ_def]  Definition

      |- ∀s a. state_succ s a = if FST a ⊑ s then SND a ⊌ s else s

   [CARD_INJ_IMAGE_2]  Theorem

      |- ∀f s.
           FINITE s ⇒
           (∀x y. x ∈ s ∧ y ∈ s ⇒ ((f x = f y) ⇔ (x = y))) ⇒
           (CARD (IMAGE f s) = CARD s)

   [EXISTS_problem]  Theorem

      |- ∀P. (∃p. P p) ⇔ ∃f1 f0 f. P <|I := f1; A := f0; G := f|>

   [FDOM_state_succ]  Theorem

      |- FDOM (SND a) ⊆ FDOM s ⇒ (FDOM (state_succ s a) = FDOM s)

   [FINITE_states]  Theorem

      |- ∀X. FINITE X ⇒ FINITE {s | FDOM s = X}

   [FORALL_problem]  Theorem

      |- ∀P. (∀p. P p) ⇔ ∀f1 f0 f. P <|I := f1; A := f0; G := f|>

   [IS_PREFIX_MEM]  Theorem

      |- ∀y. x ≼ y ⇒ ∀e. MEM e x ⇒ MEM e y

   [IS_SUFFIX_MEM]  Theorem

      |- IS_SUFFIX s (h::t) ⇒ MEM h s

   [LENGTH_INJ_PREFIXES]  Theorem

      |- ∀x1 x2. x1 ≼ y ∧ x2 ≼ y ⇒ ((LENGTH x1 = LENGTH x2) ⇔ (x1 = x2))

   [LENGTH_state_set]  Theorem

      |- ∀X e. e ∈ state_set X ⇒ LENGTH e ≤ LENGTH X

   [MEM_LAST']  Theorem

      |- seq ≠ [] ⇒ MEM (LAST seq) seq

   [MEM_statelist_FDOM]  Theorem

      |- ∀PROB h as s0.
           plan (PROB,as) ∧ (FDOM s0 = FDOM PROB.I) ∧
           MEM h (state_list (s0,as)) ⇒
           (FDOM h = FDOM PROB.I)

   [NIL_NOTIN_stateset]  Theorem

      |- ∀X. [] ∉ state_set X

   [card_of_set_of_all_possible_states]  Theorem

      |- ∀X. FINITE X ⇒ (CARD {s | FDOM s = X} = 2 ** CARD X)

   [card_union']  Theorem

      |- FINITE s ∧ FINITE t ∧ DISJOINT s t ⇒
         (CARD (s ∪ t) = CARD s + CARD t)

   [construction_of_all_possible_states_lemma]  Theorem

      |- ∀e X.
           e ∉ X ⇒
           ({s | FDOM s = e INSERT X} =
            IMAGE (λs. s |+ (e,T)) {s | FDOM s = X} ∪
            IMAGE (λs. s |+ (e,F)) {s | FDOM s = X})

   [cycle_removal_lemma]  Theorem

      |- ∀PROB as1 as2 as3.
           plan (PROB,as1 ++ as2 ++ as3) ∧
           (exec_plan (PROB.I,as1 ++ as2) = exec_plan (PROB.I,as1)) ∧
           as2 ≠ [] ⇒
           plan (PROB,as1 ++ as3)

   [datatype_problem]  Theorem

      |- DATATYPE (record problem I A G)

   [empty_state_list_lemma]  Theorem

      |- ∀as s. ([] = state_list (s,as)) ⇔ (as = [])

   [exec_plan_Append]  Theorem

      |- ∀as_a as_b s.
           exec_plan (s,as_a ++ as_b) = exec_plan (exec_plan (s,as_a),as_b)

   [exec_plan_def]  Theorem

      |- (∀s as a. exec_plan (s,a::as) = exec_plan (state_succ s a,as)) ∧
         ∀s. exec_plan (s,[]) = s

   [exec_plan_ind]  Theorem

      |- ∀P.
           (∀s a as. P (state_succ s a,as) ⇒ P (s,a::as)) ∧
           (∀s. P (s,[])) ⇒
           ∀v v1. P (v,v1)

   [general_theorem]  Theorem

      |- ∀P f l.
           (∀p. P p ∧ f p > l ⇒ ∃p'. P p' ∧ f p' < f p) ⇒
           ∀p. P p ⇒ ∃p'. P p' ∧ f p' ≤ l

   [general_theorem']  Theorem

      |- ∀P f l prob.
           (∀p. P (prob,p) ∧ f p > l ⇒ ∃p'. P (prob,p') ∧ f p' < f p) ⇒
           ∀p. P (prob,p) ⇒ ∃p'. P (prob,p') ∧ f p' ≤ l

   [lemma_1]  Theorem

      |- ∀as PROB.
           plan (PROB,as) ⇒
           IMAGE LAST (state_set (state_list (PROB.I,as))) ⊆
           {s | FDOM s = FDOM PROB.I}

   [lemma_1_1]  Theorem

      |- ∀PROB as h.
           plan (PROB,h::as) ⇒ plan (PROB with I := state_succ PROB.I h,as)

   [lemma_1_1_1]  Theorem

      |- ∀PROB.
           planning_problem PROB ∧ (FDOM I' = FDOM PROB.I) ⇒
           planning_problem (PROB with I := I')

   [lemma_2]  Theorem

      |- ∀PROB as.
           plan (PROB,as) ⇒
           LENGTH as > 2 ** CARD (FDOM PROB.I) ⇒
           ∃as1 as2 as3.
             (as1 ++ as2 ++ as3 = as) ∧
             (exec_plan (PROB.I,as1 ++ as2) = exec_plan (PROB.I,as1)) ∧
             as2 ≠ []

   [lemma_2_1]  Theorem

      |- ∀as PROB.
           plan (PROB,as) ⇒
           (LENGTH as = CARD (state_set (state_list (PROB.I,as))))

   [lemma_2_1_1]  Theorem

      |- ∀as PROB h.
           plan (PROB,h::as) ⇒
           (CARD (state_set (state_list (PROB.I,h::as))) =
            SUC
              (CARD
                 (state_set
                    (state_list
                       ((PROB with I := state_succ PROB.I h).I,as)))))

   [lemma_2_1_1_1]  Theorem

      |- ∀as x PROB.
           as ≠ [] ∧ plan (PROB,as) ⇒
           x ∈ state_set (state_list (PROB.I,as)) ⇒
           LENGTH x ≤ LENGTH as

   [lemma_2_1_1_2]  Theorem

      |- ∀l1 l2. LENGTH l1 > LENGTH l2 ⇒ l1 ≠ l2

   [lemma_2_2]  Theorem

      |- ∀as PROB.
           plan (PROB,as) ⇒
           ¬INJ LAST (state_set (state_list (PROB.I,as)))
              {s | FDOM s = FDOM PROB.I} ⇒
           ∃slist_1 slist_2.
             slist_1 ∈ state_set (state_list (PROB.I,as)) ∧
             slist_2 ∈ state_set (state_list (PROB.I,as)) ∧
             (LAST slist_1 = LAST slist_2) ∧
             LENGTH slist_1 ≠ LENGTH slist_2

   [lemma_2_2_1]  Theorem

      |- ∀as x y PROB.
           plan (PROB,as) ∧ x ∈ state_set (state_list (PROB.I,as)) ∧
           y ∈ state_set (state_list (PROB.I,as)) ∧ x ≠ y ⇒
           LENGTH x ≠ LENGTH y

   [lemma_2_3_1_1]  Theorem

      |- ∀sl. [] ∉ state_set sl

   [lemma_2_3_1_2]  Theorem

      |- ∀s slist h t.
           slist ≠ [] ∧ s::slist ∈ state_set (state_list (s,h::t)) ⇒
           slist ∈ state_set (state_list (state_succ s h,t))

   [lemma_2_3_1_2_1]  Theorem

      |- ∀sl. sl ≠ [] ⇒ sl ∈ state_set sl

   [lemma_2_3_1_3_1]  Theorem

      |- ∀PROB h as.
           plan (PROB,h::as) ⇒
           (PROB.G = (PROB with I := state_succ PROB.I h).G)

   [lemma_2_3_1_4]  Theorem

      |- ∀l. l ≠ [] ⇒ FRONT l ≼ l

   [lemma_2_3_1_thm]  Theorem

      |- ∀slist as PROB.
           as ≠ [] ∧ slist ≠ [] ∧ plan (PROB,as) ⇒
           slist ∈ state_set (state_list (PROB.I,as)) ⇒
           ∃as'.
             as' ≼ as ∧ (exec_plan (PROB.I,as') = LAST slist) ∧
             (LENGTH slist = SUC (LENGTH as'))

   [lemma_2_3_2]  Theorem

      |- ∀l l1 l2. LENGTH l2 > LENGTH l1 ∧ l1 ≼ l ∧ l2 ≼ l ⇒ l1 ≼ l2

   [lemma_2_3_2_1]  Theorem

      |- ∀l. LENGTH l ≥ 0

   [lemma_3]  Theorem

      |- ∀as PROB.
           plan (PROB,as) ∧ LENGTH as > 2 ** CARD (FDOM PROB.I) ⇒
           ∃as'. plan (PROB,as') ∧ LENGTH as' < LENGTH as ∧ sublist as' as

   [lemma_3_1]  Theorem

      |- ∀l1 l2 l3. l2 ≠ [] ⇒ LENGTH (l1 ++ l3) < LENGTH (l1 ++ l2 ++ l3)

   [lemma_temp]  Theorem

      |- ∀x PROB as h.
           plan (PROB,as) ⇒
           x ∈ state_set (state_list (PROB.I,as)) ⇒
           LENGTH (h::state_list (PROB.I,as)) > LENGTH x

   [main_lemma]  Theorem

      |- ∀PROB as.
           plan (PROB,as) ⇒
           ∃as'.
             plan (PROB,as') ∧ sublist as' as ∧
             LENGTH as' ≤ 2 ** CARD (FDOM PROB.I)

   [plan_CONS]  Theorem

      |- plan (PROB,h::as) ⇔
         plan (PROB with I := state_succ PROB.I h,as) ∧ h ∈ PROB.A ∧
         planning_problem PROB

   [problem_11]  Theorem

      |- ∀a0 a1 a2 a0' a1' a2'.
           (problem a0 a1 a2 = problem a0' a1' a2') ⇔
           (a0 = a0') ∧ (a1 = a1') ∧ (a2 = a2')

   [problem_Axiom]  Theorem

      |- ∀f. ∃fn. ∀a0 a1 a2. fn (problem a0 a1 a2) = f a0 a1 a2

   [problem_accessors]  Theorem

      |- (∀f f0 f1. (problem f f0 f1).I = f) ∧
         (∀f f0 f1. (problem f f0 f1).A = f0) ∧
         ∀f f0 f1. (problem f f0 f1).G = f1

   [problem_accfupds]  Theorem

      |- (∀p f. (p with A updated_by f).I = p.I) ∧
         (∀p f. (p with G updated_by f).I = p.I) ∧
         (∀p f. (p with I updated_by f).A = p.A) ∧
         (∀p f. (p with G updated_by f).A = p.A) ∧
         (∀p f. (p with I updated_by f).G = p.G) ∧
         (∀p f. (p with A updated_by f).G = p.G) ∧
         (∀p f. (p with I updated_by f).I = f p.I) ∧
         (∀p f. (p with A updated_by f).A = f p.A) ∧
         ∀p f. (p with G updated_by f).G = f p.G

   [problem_case_cong]  Theorem

      |- ∀M M' f.
           (M = M') ∧
           (∀a0 a1 a2.
              (M' = problem a0 a1 a2) ⇒ (f a0 a1 a2 = f' a0 a1 a2)) ⇒
           (problem_CASE M f = problem_CASE M' f')

   [problem_component_equality]  Theorem

      |- ∀p1 p2. (p1 = p2) ⇔ (p1.I = p2.I) ∧ (p1.A = p2.A) ∧ (p1.G = p2.G)

   [problem_fn_updates]  Theorem

      |- (∀f2 f f0 f1.
            problem f f0 f1 with I updated_by f2 = problem (f2 f) f0 f1) ∧
         (∀f2 f f0 f1.
            problem f f0 f1 with A updated_by f2 = problem f (f2 f0) f1) ∧
         ∀f2 f f0 f1.
           problem f f0 f1 with G updated_by f2 = problem f f0 (f2 f1)

   [problem_fupdcanon]  Theorem

      |- (∀p g f.
            p with <|A updated_by f; I updated_by g|> =
            p with <|I updated_by g; A updated_by f|>) ∧
         (∀p g f.
            p with <|G updated_by f; I updated_by g|> =
            p with <|I updated_by g; G updated_by f|>) ∧
         ∀p g f.
           p with <|G updated_by f; A updated_by g|> =
           p with <|A updated_by g; G updated_by f|>

   [problem_fupdcanon_comp]  Theorem

      |- ((∀g f.
              _ record fupdateA f o  _ record fupdateI g =
              _ record fupdateI g o  _ record fupdateA f) ∧
          ∀h g f.
             _ record fupdateA f o  _ record fupdateI g o h =
             _ record fupdateI g o  _ record fupdateA f o h) ∧
         ((∀g f.
              _ record fupdateG f o  _ record fupdateI g =
              _ record fupdateI g o  _ record fupdateG f) ∧
          ∀h g f.
             _ record fupdateG f o  _ record fupdateI g o h =
             _ record fupdateI g o  _ record fupdateG f o h) ∧
         (∀g f.
             _ record fupdateG f o  _ record fupdateA g =
             _ record fupdateA g o  _ record fupdateG f) ∧
         ∀h g f.
            _ record fupdateG f o  _ record fupdateA g o h =
            _ record fupdateA g o  _ record fupdateG f o h

   [problem_fupdfupds]  Theorem

      |- (∀p g f.
            p with <|I updated_by f; I updated_by g|> =
            p with I updated_by f o g) ∧
         (∀p g f.
            p with <|A updated_by f; A updated_by g|> =
            p with A updated_by f o g) ∧
         ∀p g f.
           p with <|G updated_by f; G updated_by g|> =
           p with G updated_by f o g

   [problem_fupdfupds_comp]  Theorem

      |- ((∀g f.
              _ record fupdateI f o  _ record fupdateI g =
              _ record fupdateI (f o g)) ∧
          ∀h g f.
             _ record fupdateI f o  _ record fupdateI g o h =
             _ record fupdateI (f o g) o h) ∧
         ((∀g f.
              _ record fupdateA f o  _ record fupdateA g =
              _ record fupdateA (f o g)) ∧
          ∀h g f.
             _ record fupdateA f o  _ record fupdateA g o h =
             _ record fupdateA (f o g) o h) ∧
         (∀g f.
             _ record fupdateG f o  _ record fupdateG g =
             _ record fupdateG (f o g)) ∧
         ∀h g f.
            _ record fupdateG f o  _ record fupdateG g o h =
            _ record fupdateG (f o g) o h

   [problem_induction]  Theorem

      |- ∀P. (∀f f0 f1. P (problem f f0 f1)) ⇒ ∀p. P p

   [problem_literal_11]  Theorem

      |- ∀f11 f01 f1 f12 f02 f2.
           (<|I := f11; A := f01; G := f1|> =
            <|I := f12; A := f02; G := f2|>) ⇔
           (f11 = f12) ∧ (f01 = f02) ∧ (f1 = f2)

   [problem_literal_nchotomy]  Theorem

      |- ∀p. ∃f1 f0 f. p = <|I := f1; A := f0; G := f|>

   [problem_nchotomy]  Theorem

      |- ∀pp. ∃f f0 f1. pp = problem f f0 f1

   [problem_updates_eq_literal]  Theorem

      |- ∀p f1 f0 f.
           p with <|I := f1; A := f0; G := f|> =
           <|I := f1; A := f0; G := f|>

   [state_list_def]  Theorem

      |- (∀s as a.
            state_list (s,a::as) = s::state_list (state_succ s a,as)) ∧
         ∀s. state_list (s,[]) = []

   [state_list_ind]  Theorem

      |- ∀P.
           (∀s a as. P (state_succ s a,as) ⇒ P (s,a::as)) ∧
           (∀s. P (s,[])) ⇒
           ∀v v1. P (v,v1)

   [state_list_length_lemma]  Theorem

      |- ∀as s. LENGTH as = LENGTH (state_list (s,as))

   [state_set_card]  Theorem

      |- ∀X. CARD (state_set X) = LENGTH X

   [state_set_finite]  Theorem

      |- ∀X. FINITE (state_set X)

   [state_set_thm]  Theorem

      |- ∀s1. s1 ∈ state_set s2 ⇔ s1 ≼ s2 ∧ s1 ≠ []


*)
end
