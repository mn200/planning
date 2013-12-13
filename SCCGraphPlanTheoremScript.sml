
open HolKernel Parse boolLib bossLib;
open finite_mapTheory
open arithmeticTheory
open pred_setTheory
open rich_listTheory
open listTheory;							 
open utilsTheory;
open FM_planTheory 
open sublistTheory;
open GraphPlanTheoremTheory;
open relationTheory;
val _ = new_theory "SCCGraphPlanTheorem";


val dep_tc_def = Define `dep_tc (PROB)   =  TC (\v1' v2'. dep(PROB, v1', v2'))`;



val ancestors_def = Define
 `ancestors(PROB: 'a problem, vs: ('a -> bool)) = 
    {v: 'a | (?v': 'a. v' IN vs /\ ((dep_tc(PROB)) v v') ) /\ (!v': 'a. v' IN vs ==> ~((dep_tc(PROB)) v' v))}`;


val scc_def = Define 
`scc(PROB, vs) 
    = (!v1 v2. v1 IN vs /\ v2 IN vs ==> ((dep_tc(PROB)) v1 v2) /\ ((dep_tc(PROB)) v2 v1))
          /\ (!vs'. DISJOINT vs' vs ==> ~(dep_var_set(PROB, vs, vs')) \/ ~(dep_var_set(PROB, vs', vs)))`;

val scc_set_def = Define
`scc_set(PROB, S) = !vs. vs IN S /\ vs SUBSET FDOM(PROB.I) ==> scc(PROB, vs)`;


val sum_scc_parents_def 
  = Define` sum_scc_parents(PROB, S) 
     = SIGMA (\vs. problem_plan_bound((prob_proj(PROB, vs UNION (ancestors(PROB, vs)))))) S`;

val childless_vs_def = Define`
      childless_vs(PROB, vs) = !vs'. DISJOINT vs vs' ==> ~(dep_var_set(PROB, vs, vs'))`


val childless_svs_def = Define`
      childless_svs(PROB, S) = !vs. vs IN S ==> (childless_vs(PROB, vs))`;


val childless_problem_scc_set_def = Define`
      childless_problem_scc_set(PROB) = {vs | (scc(PROB, vs)) /\ (childless_vs(PROB, vs))}`;


val member_leaves_def = Define
     `member_leaves(PROB, S) 
           = set (FILTER (\vs. (scc(PROB, vs) /\ childless_vs(PROB, vs))) (SET_TO_LIST S))`;

val scc_lemma_1 = store_thm("scc_lemma_1",
``!PROB S. FINITE(S) ==> FINITE((member_leaves(PROB, S)))``,
cheat)

val single_child_parents_def = Define
`single_child_parents(PROB, vs) 
           = {vs' | vs' SUBSET (ancestors(PROB, vs)) 
                       /\ childless_vs(prob_proj(PROB, (FDOM PROB.I) DIFF vs), vs') 
                            /\scc(PROB, vs')}`;

val single_child_ancestors_def_1 = store_thm("single_child_ancestors_def_1",
``WF (\x y. CARD (FDOM (FST(x)).I ) < CARD(FDOM ((FST(y)).I)))``,
cheat(*SRW_TAC[][WF_DEF]
THEN Q.EXISTS_TAC `(prob_proj((FST w), EMPTY) , SND w)`
SRW_TAC[][]
THEN SRW_TAC[][prob_proj_def]
THENL
[
   METIS_TAC[]
   ,
   FULL_SIMP_TAC(srw_ss())[FDOM_DRESTRICT]
]*));

val single_child_ancestors_def_2_1 = store_thm("single_child_ancestors_def_2_1",
``!s t.FINITE s /\ FINITE t /\ s SUBSET t ==> (t INTER (t DIFF s) = t DIFF s)``, 
SRW_TAC[][SUBSET_DEF, INTER_DEF, DIFF_DEF, EXTENSION]
THEN METIS_TAC[]
)


val single_child_ancestors_def_2 = store_thm("single_child_ancestors_def_2",
``!PROB vs vs'. vs SUBSET FDOM(PROB.I) /\ ~(vs = EMPTY) 
                ==> CARD(FDOM((prob_proj(PROB, (FDOM(PROB.I)) DIFF vs)).I)) < CARD(FDOM(PROB.I))``,
SRW_TAC[][prob_proj_def, FDOM_DRESTRICT]
THEN `FINITE (FDOM(PROB.I))` by SRW_TAC[][]
THEN `FINITE vs` by METIS_TAC[SUBSET_FINITE]
THEN MP_TAC(single_child_ancestors_def_2_1 |> Q.SPECL[`vs`,`(FDOM PROB.I)`])
THEN SRW_TAC[][]
THEN MP_TAC(REWRITE_RULE [Once INTER_COMM] (bound_child_parent_lemma_1_1_1_3_1_3 |> Q.SPECL[`vs`, `FDOM PROB.I`]))
THEN SRW_TAC[][]
THEN `~(CARD vs = 0)` by METIS_TAC[(GSYM CARD_EQ_0 |> Q.SPEC `vs`)] 
THEN1 DECIDE_TAC
THEN MP_TAC(CARD_SUBSET |>  Q.SPEC `FDOM PROB.I`)
THEN SRW_TAC[][]  
THEN Q.PAT_ASSUM `!x. P x` (MP_TAC o Q.SPEC `vs`)
THEN SRW_TAC[][]
THEN DECIDE_TAC
);


val single_child_ancestors_def = tDefine "single_child_ancestors"
   `single_child_ancestors(PROB, vs) = 
          if(vs SUBSET FDOM(PROB.I) /\ ~(vs = EMPTY)) then
             single_child_parents(PROB, vs) 
              UNION BIGUNION (IMAGE 
                   (\vs'. single_child_ancestors((prob_proj(PROB, (FDOM PROB.I) DIFF vs)), vs')) 
                                  (single_child_parents(PROB, vs)))
          else {}`
(WF_REL_TAC `measure (CARD o FDOM o (\PROB. PROB.I) o FST)`
THEN METIS_TAC[single_child_ancestors_def_2]);

val scc_main_lemma_1_1 = store_thm("scc_main_lemma_1_1",
````,
cheat)

val scc_main_lemma_1_2 = store_thm("scc_main_lemma_1_2",
````,
cheat)
val scc_main_lemma_1 = store_thm("scc_main_lemma_1",
``∀s. FINITE s ⇒  
      ∀S PROB.
       planning_problem PROB ∧ scc_set (PROB,S) ∧
       FDOM PROB.I ⊆ BIGUNION S ∧ (S ≠ ∅ ∧ S ≠ {∅}) ∧ FINITE S ∧
       (s = member_leaves (PROB,S)) ⇒
       problem_plan_bound PROB ≤
       sum_scc_parents (PROB,member_leaves (PROB,S))``,
cheat
(*
MATCH_MP_TAC(simpLib.ASM_SIMP_RULE (srw_ss()) [AND_IMP_INTRO]  (FINITE_INDUCT 
   |> INST_TYPE [alpha |-> ``:'a -> bool``] 
   |> Q.SPEC `(\s. !S PROB. planning_problem PROB ∧ scc_set (PROB,S) 
                   ∧ FDOM PROB.I ⊆ BIGUNION S ∧ (BIGUNION S ≠ ∅ ) ∧ FINITE S 
                   /\ (s = member_leaves(PROB, S)) 
                   ==> problem_plan_bound PROB ≤ sum_scc_parents (PROB,s))`))
THEN SRW_TAC[][]
THENL
[
   Q.PAT_ASSUM `EMPTY = x` (ASSUME_TAC o GSYM)
   THEN SRW_TAC[][]
   ,
]
*)
)

val scc_main_lemma = store_thm("scc_main_lemma",
``!S PROB. planning_problem(PROB) /\ scc_set(PROB, S) /\ FDOM PROB.I SUBSET BIGUNION S /\ ~(BIGUNION S = EMPTY)
           /\ FINITE(S)
           ==>  problem_plan_bound(PROB) <= sum_scc_parents(PROB, (member_leaves(PROB, S)))``,
NTAC 2 STRIP_TAC 
THEN MP_TAC(scc_lemma_1 |> Q.SPECL [`PROB`, `S'`])
THEN SRW_TAC[][]
THEN FULL_SIMP_TAC(srw_ss())[]
THEN METIS_TAC [scc_main_lemma_1]
(*
THEN   Q.UNDISCH_TAC `FINITE (member_leaves (PROB,S'))`
   THEN Q.UNDISCH_TAC `planning_problem PROB`
   THEN Q.UNDISCH_TAC `scc_set (PROB,S')`
   THEN Q.UNDISCH_TAC `FDOM PROB.I ⊆ BIGUNION S'`
   THEN Q.UNDISCH_TAC `S' ≠ ∅`
   THEN Q.UNDISCH_TAC `S' ≠ {∅}`
   THEN Q.UNDISCH_TAC `FINITE S'`
THEN REWRITE_TAC[AND_IMP_INTRO, GSYM CONJ_ASSOC]
THEN Q.SPEC_TAC(`S'`, `S'`)
THEN Q.SPEC_TAC(`PROB`, `PROB`)
THEN MATCH_MP_TAC(simpLib.ASM_SIMP_RULE (bool_ss) [AND_IMP_INTRO]((CONV_RULE RIGHT_IMP_FORALL_CONV) (simpLib.ASM_SIMP_RULE (srw_ss()) [AND_IMP_INTRO] (GSYM(FINITE_INDUCT 
   |> INST_TYPE [alpha |-> ``:'a -> bool``] 
   |> Q.SPEC `(\s. !S PROB. planning_problem PROB ∧ scc_set (PROB,S) 
                   ∧ FDOM PROB.I ⊆ BIGUNION S ∧ (BIGUNION S ≠ ∅ ) ∧ FINITE S 
                   /\ (s = member_leaves(PROB, S)) 
                   ==> problem_plan_bound PROB ≤ sum_scc_parents (PROB,s))`))))) *)
);


val _ = export_theory();