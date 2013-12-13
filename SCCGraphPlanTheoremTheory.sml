structure SCCGraphPlanTheoremTheory :> SCCGraphPlanTheoremTheory =
struct
  val _ = if !Globals.print_thy_loads then print "Loading SCCGraphPlanTheoremTheory ... " else ()
  open Type Term Thm
  infixr -->

  fun C s t ty = mk_thy_const{Name=s,Thy=t,Ty=ty}
  fun T s t A = mk_thy_type{Tyop=s, Thy=t,Args=A}
  fun V s q = mk_var(s,q)
  val U     = mk_vartype
  (*  Parents *)
  local open GraphPlanTheoremTheory
  in end;
  val _ = Theory.link_parents
          ("SCCGraphPlanTheorem",
          Arbnum.fromString "1386898023",
          Arbnum.fromString "336204")
          [("GraphPlanTheorem",
           Arbnum.fromString "1386898008",
           Arbnum.fromString "724995")];
  val _ = Theory.incorporate_types "SCCGraphPlanTheorem" [];

  val idvector = 
    let fun ID(thy,oth) = {Thy = thy, Other = oth}
    in Vector.fromList
  [ID("min", "fun"), ID("num", "num"), ID("pair", "prod"),
   ID("min", "bool"), ID("FM_plan", "problem"), ID("list", "list"),
   ID("bool", "!"), ID("pair", ","), ID("bool", "/\\"),
   ID("prim_rec", "<"), ID("min", "="), ID("min", "==>"), ID("bool", "?"),
   ID("min", "@"), ID("pred_set", "BIGUNION"), ID("pred_set", "CARD"),
   ID("bool", "COND"), ID("pred_set", "DIFF"), ID("pred_set", "DISJOINT"),
   ID("pred_set", "EMPTY"), ID("finite_map", "FDOM"),
   ID("finite_map", "fmap"), ID("list", "FILTER"),
   ID("pred_set", "FINITE"), ID("pair", "FST"), ID("pred_set", "GSPEC"),
   ID("combin", "I"), ID("pred_set", "IMAGE"), ID("bool", "IN"),
   ID("pred_set", "INTER"), ID("list", "SET_TO_LIST"),
   ID("pred_set", "SUBSET"), ID("pred_set", "SUM_IMAGE"),
   ID("relation", "TC"), ID("pred_set", "UNION"), ID("relation", "WF"),
   ID("relation", "WFREC"), ID("bool", "\\/"),
   ID("SCCGraphPlanTheorem", "ancestors"),
   ID("SCCGraphPlanTheorem", "childless_problem_scc_set"),
   ID("SCCGraphPlanTheorem", "childless_svs"),
   ID("SCCGraphPlanTheorem", "childless_vs"),
   ID("GraphPlanTheorem", "dep"), ID("SCCGraphPlanTheorem", "dep_tc"),
   ID("GraphPlanTheorem", "dep_var_set"),
   ID("SCCGraphPlanTheorem", "member_leaves"), ID("pair", "pair_CASE"),
   ID("GraphPlanTheorem", "prob_proj"), ID("FM_plan", "problem_I"),
   ID("GraphPlanTheorem", "problem_plan_bound"),
   ID("SCCGraphPlanTheorem", "scc"), ID("SCCGraphPlanTheorem", "scc_set"),
   ID("SCCGraphPlanTheorem", "single_child_ancestors"),
   ID("SCCGraphPlanTheorem", "single_child_parents"),
   ID("SCCGraphPlanTheorem", "sum_scc_parents"), ID("bool", "~")]
  end;
  local open SharingTables
  in
  val tyvector = build_type_vector idvector
  [TYOP [1], TYOP [3], TYV "'a", TYOP [0, 2, 1], TYOP [0, 3, 1],
   TYOP [4, 2], TYOP [2, 5, 4], TYOP [0, 6, 0], TYOP [2, 5, 3],
   TYOP [0, 8, 4], TYOP [0, 6, 1], TYOP [0, 8, 1], TYOP [5, 3],
   TYOP [0, 6, 12], TYOP [0, 2, 3], TYOP [0, 5, 14], TYOP [0, 5, 4],
   TYOP [0, 8, 3], TYOP [0, 8, 11], TYV "'b", TYOP [2, 5, 19],
   TYOP [0, 19, 1], TYOP [0, 21, 1], TYOP [0, 4, 1], TYOP [0, 23, 1],
   TYOP [0, 11, 1], TYOP [0, 25, 1], TYOP [0, 5, 1], TYOP [0, 27, 1],
   TYOP [2, 2, 2], TYOP [0, 2, 29], TYOP [0, 2, 30], TYOP [2, 2, 1],
   TYOP [0, 1, 32], TYOP [0, 2, 33], TYOP [2, 3, 1], TYOP [0, 1, 35],
   TYOP [0, 3, 36], TYOP [2, 3, 3], TYOP [0, 3, 38], TYOP [0, 3, 39],
   TYOP [0, 3, 8], TYOP [0, 5, 41], TYOP [0, 4, 6], TYOP [0, 5, 43],
   TYOP [2, 5, 29], TYOP [0, 29, 45], TYOP [0, 5, 46], TYOP [2, 5, 38],
   TYOP [0, 38, 48], TYOP [0, 5, 49], TYOP [0, 1, 1], TYOP [0, 1, 51],
   TYOP [0, 0, 1], TYOP [0, 0, 53], TYOP [0, 3, 4], TYOP [0, 14, 1],
   TYOP [0, 14, 56], TYOP [0, 4, 23], TYOP [0, 9, 1], TYOP [0, 9, 59],
   TYOP [0, 12, 1], TYOP [0, 12, 61], TYOP [0, 18, 1], TYOP [0, 63, 18],
   TYOP [0, 23, 4], TYOP [0, 3, 0], TYOP [0, 4, 4], TYOP [0, 4, 67],
   TYOP [0, 1, 68], TYOP [0, 3, 3], TYOP [0, 3, 70], TYOP [21, 2, 1],
   TYOP [0, 72, 3], TYOP [0, 12, 12], TYOP [0, 4, 74], TYOP [0, 20, 5],
   TYOP [0, 2, 32], TYOP [0, 77, 3], TYOP [0, 3, 35], TYOP [0, 79, 4],
   TYOP [0, 55, 58], TYOP [0, 2, 4], TYOP [0, 3, 23], TYOP [0, 4, 12],
   TYOP [0, 4, 0], TYOP [0, 66, 85], TYOP [0, 14, 14], TYOP [0, 20, 1],
   TYOP [0, 20, 88], TYOP [0, 89, 1], TYOP [0, 9, 9], TYOP [0, 91, 9],
   TYOP [0, 18, 92], TYOP [0, 45, 1], TYOP [0, 48, 1], TYOP [0, 5, 55],
   TYOP [0, 96, 4], TYOP [0, 8, 97], TYOP [0, 8, 5], TYOP [0, 5, 72],
   TYOP [0, 5, 0]]
  end
  val _ = Theory.incorporate_consts "SCCGraphPlanTheorem" tyvector
     [("sum_scc_parents", 7), ("single_child_parents", 9),
      ("single_child_ancestors", 9), ("scc_set", 10), ("scc", 11),
      ("member_leaves", 13), ("dep_tc", 15), ("childless_vs", 11),
      ("childless_svs", 10), ("childless_problem_scc_set", 16),
      ("ancestors", 17)];

  local open SharingTables
  in
  val tmvector = build_term_vector idvector tyvector
  [TMV("P", 11), TMV("PROB", 5), TMV("R", 18), TMV("S", 4), TMV("a", 8),
   TMV("s", 3), TMV("single_child_ancestors", 9), TMV("t", 3), TMV("v", 2),
   TMV("v", 5), TMV("v'", 2), TMV("v1", 2), TMV("v1", 3), TMV("v1'", 2),
   TMV("v2", 2), TMV("v2'", 2), TMV("vs", 3), TMV("vs'", 19),
   TMV("vs'", 3), TMV("x", 20), TMV("y", 20), TMC(6, 4), TMC(6, 22),
   TMC(6, 23), TMC(6, 24), TMC(6, 26), TMC(6, 28), TMC(7, 31), TMC(7, 34),
   TMC(7, 37), TMC(7, 40), TMC(7, 42), TMC(7, 44), TMC(7, 47), TMC(7, 50),
   TMC(8, 52), TMC(9, 54), TMC(10, 52), TMC(10, 55), TMC(10, 57),
   TMC(10, 58), TMC(10, 60), TMC(10, 62), TMC(10, 54), TMC(11, 52),
   TMC(12, 4), TMC(13, 64), TMC(14, 65), TMC(15, 66), TMC(16, 69),
   TMC(17, 71), TMC(18, 55), TMC(19, 3), TMC(19, 4), TMC(20, 73),
   TMC(22, 75), TMC(23, 4), TMC(24, 76), TMC(25, 78), TMC(25, 80),
   TMC(26, 67), TMC(27, 81), TMC(28, 82), TMC(28, 83), TMC(29, 71),
   TMC(30, 84), TMC(31, 55), TMC(32, 86), TMC(33, 87), TMC(34, 71),
   TMC(34, 68), TMC(35, 90), TMC(35, 63), TMC(36, 93), TMC(37, 52),
   TMC(38, 17), TMC(39, 16), TMC(40, 10), TMC(41, 11), TMC(42, 94),
   TMC(43, 15), TMC(44, 95), TMC(45, 13), TMC(46, 98), TMC(47, 99),
   TMC(48, 100), TMC(49, 101), TMC(50, 11), TMC(51, 10), TMC(52, 9),
   TMC(53, 9), TMC(54, 7), TMC(55, 51)]
  end
  local
  val DT = Thm.disk_thm val read = Term.read_raw tmvector
  in
  val op dep_tc_def =
    DT([],
       [read"(%26 (|%1. ((%39 (%80 $0)) (%68 (|%13. (|%15. (%79 ((%33 $2) ((%27 $1) $0)))))))))"])
  val op ancestors_def =
    DT(["DISK_THM"],
       [read"(%26 (|%1. (%23 (|%16. ((%38 (%75 ((%31 $1) $0))) (%58 (|%8. ((%28 $0) ((%35 (%45 (|%10. ((%35 ((%62 $0) $2)) (((%80 $3) $1) $0))))) (%21 (|%10. ((%44 ((%62 $0) $2)) (%92 (((%80 $3) $0) $1))))))))))))))"])
  val op scc_def =
    DT(["DISK_THM"],
       [read"(%26 (|%1. (%23 (|%16. ((%37 (%87 ((%31 $1) $0))) ((%35 (%21 (|%11. (%21 (|%14. ((%44 ((%35 ((%62 $1) $2)) ((%62 $0) $2))) ((%35 (((%80 $3) $1) $0)) (((%80 $3) $0) $1)))))))) (%23 (|%18. ((%44 ((%51 $0) $1)) ((%74 (%92 (%81 ((%34 $2) ((%30 $1) $0))))) (%92 (%81 ((%34 $2) ((%30 $0) $1))))))))))))))"])
  val op scc_set_def =
    DT(["DISK_THM"],
       [read"(%26 (|%1. (%24 (|%3. ((%37 (%88 ((%32 $1) $0))) (%23 (|%16. ((%44 ((%35 ((%63 $0) $1)) ((%66 $0) (%54 (%85 $2))))) (%87 ((%31 $2) $0))))))))))"])
  val op sum_scc_parents_def =
    DT(["DISK_THM"],
       [read"(%26 (|%1. (%24 (|%3. ((%43 (%91 ((%32 $1) $0))) ((%67 (|%16. (%86 (%84 ((%31 $2) ((%69 $0) (%75 ((%31 $2) $0)))))))) $0))))))"])
  val op childless_vs_def =
    DT(["DISK_THM"],
       [read"(%26 (|%1. (%23 (|%16. ((%37 (%78 ((%31 $1) $0))) (%23 (|%18. ((%44 ((%51 $1) $0)) (%92 (%81 ((%34 $2) ((%30 $1) $0))))))))))))"])
  val op childless_svs_def =
    DT(["DISK_THM"],
       [read"(%26 (|%1. (%24 (|%3. ((%37 (%77 ((%32 $1) $0))) (%23 (|%16. ((%44 ((%63 $0) $1)) (%78 ((%31 $2) $0))))))))))"])
  val op childless_problem_scc_set_def =
    DT([],
       [read"(%26 (|%1. ((%40 (%76 $0)) (%59 (|%16. ((%29 $0) ((%35 (%87 ((%31 $1) $0))) (%78 ((%31 $1) $0)))))))))"])
  val op member_leaves_def =
    DT(["DISK_THM"],
       [read"(%26 (|%1. (%24 (|%3. ((%42 (%82 ((%32 $1) $0))) ((%55 (|%16. ((%35 (%87 ((%31 $2) $0))) (%78 ((%31 $2) $0))))) (%65 $0)))))))"])
  val op single_child_parents_def =
    DT(["DISK_THM"],
       [read"(%26 (|%1. (%23 (|%16. ((%40 (%90 ((%31 $1) $0))) (%59 (|%18. ((%29 $0) ((%35 ((%66 $0) (%75 ((%31 $2) $1)))) ((%35 (%78 ((%31 (%84 ((%31 $2) ((%50 (%54 (%85 $2))) $1)))) $0))) (%87 ((%31 $2) $0))))))))))))"])
  val op single_child_ancestors_primitive_def =
    DT([],
       [read"((%41 %89) ((%73 (%46 (|%2. ((%35 (%72 $0)) (%26 (|%1. (%23 (|%16. (%23 (|%18. ((%44 ((%35 ((%35 ((%66 $1) (%54 (%85 $2)))) (%92 ((%38 $1) %52)))) ((%63 $0) (%90 ((%31 $2) $1))))) (($3 ((%31 (%84 ((%31 $2) ((%50 (%54 (%85 $2))) $1)))) $0)) ((%31 $2) $1))))))))))))) (|%6. (|%4. ((%83 $0) (|%1. (|%16. (%60 (((%49 ((%35 ((%66 $0) (%54 (%85 $1)))) (%92 ((%38 $0) %52)))) ((%70 (%90 ((%31 $1) $0))) (%47 ((%61 (|%18. ($4 ((%31 (%84 ((%31 $2) ((%50 (%54 (%85 $2))) $1)))) $0)))) (%90 ((%31 $1) $0)))))) %53)))))))))"])
  val op single_child_ancestors_def_1 =
    DT(["cheat"],
       [read"(%71 (|%19. (|%20. ((%36 (%48 (%54 (%85 (%57 $1))))) (%48 (%54 (%85 (%57 $0))))))))"])
  val op single_child_ancestors_def_2_1 =
    DT(["DISK_THM"],
       [read"(%23 (|%5. (%23 (|%7. ((%44 ((%35 (%56 $1)) ((%35 (%56 $0)) ((%66 $1) $0)))) ((%38 ((%64 $0) ((%50 $0) $1))) ((%50 $0) $1)))))))"])
  val op single_child_ancestors_def_2 =
    DT(["DISK_THM"],
       [read"(%26 (|%1. (%23 (|%16. (%22 (|%17. ((%44 ((%35 ((%66 $1) (%54 (%85 $2)))) (%92 ((%38 $1) %52)))) ((%36 (%48 (%54 (%85 (%84 ((%31 $2) ((%50 (%54 (%85 $2))) $1))))))) (%48 (%54 (%85 $2)))))))))))"])
  val op single_child_ancestors_ind =
    DT(["DISK_THM"],
       [read"(%25 (|%0. ((%44 (%26 (|%1. (%23 (|%16. ((%44 (%23 (|%18. ((%44 ((%35 ((%35 ((%66 $1) (%54 (%85 $2)))) (%92 ((%38 $1) %52)))) ((%63 $0) (%90 ((%31 $2) $1))))) ($3 ((%31 (%84 ((%31 $2) ((%50 (%54 (%85 $2))) $1)))) $0)))))) ($2 ((%31 $1) $0)))))))) (%26 (|%9. (%23 (|%12. ($2 ((%31 $1) $0)))))))))"])
  val op single_child_ancestors_def =
    DT(["DISK_THM"],
       [read"(%23 (|%16. (%26 (|%1. ((%40 (%89 ((%31 $0) $1))) (((%49 ((%35 ((%66 $1) (%54 (%85 $0)))) (%92 ((%38 $1) %52)))) ((%70 (%90 ((%31 $0) $1))) (%47 ((%61 (|%18. (%89 ((%31 (%84 ((%31 $1) ((%50 (%54 (%85 $1))) $2)))) $0)))) (%90 ((%31 $0) $1)))))) %53))))))"])
  end
  val _ = DB.bindl "SCCGraphPlanTheorem"
  [("dep_tc_def",dep_tc_def,DB.Def),
   ("ancestors_def",ancestors_def,DB.Def), ("scc_def",scc_def,DB.Def),
   ("scc_set_def",scc_set_def,DB.Def),
   ("sum_scc_parents_def",sum_scc_parents_def,DB.Def),
   ("childless_vs_def",childless_vs_def,DB.Def),
   ("childless_svs_def",childless_svs_def,DB.Def),
   ("childless_problem_scc_set_def",childless_problem_scc_set_def,DB.Def),
   ("member_leaves_def",member_leaves_def,DB.Def),
   ("single_child_parents_def",single_child_parents_def,DB.Def),
   ("single_child_ancestors_primitive_def",
    single_child_ancestors_primitive_def,
    DB.Def),
   ("single_child_ancestors_def_1",single_child_ancestors_def_1,DB.Thm),
   ("single_child_ancestors_def_2_1",
    single_child_ancestors_def_2_1,
    DB.Thm),
   ("single_child_ancestors_def_2",single_child_ancestors_def_2,DB.Thm),
   ("single_child_ancestors_ind",single_child_ancestors_ind,DB.Thm),
   ("single_child_ancestors_def",single_child_ancestors_def,DB.Thm)]

  local open Portable GrammarSpecials Parse
    fun UTOFF f = Feedback.trace("Parse.unicode_trace_off_complaints",0)f
  in
  val _ = mk_local_grms [("GraphPlanTheoremTheory.GraphPlanTheorem_grammars",
                          GraphPlanTheoremTheory.GraphPlanTheorem_grammars)]
  val _ = List.app (update_grms reveal) []
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("dep_tc", (Term.prim_mk_const { Name = "dep_tc", Thy = "SCCGraphPlanTheorem"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("dep_tc", (Term.prim_mk_const { Name = "dep_tc", Thy = "SCCGraphPlanTheorem"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("ancestors", (Term.prim_mk_const { Name = "ancestors", Thy = "SCCGraphPlanTheorem"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("ancestors", (Term.prim_mk_const { Name = "ancestors", Thy = "SCCGraphPlanTheorem"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("scc", (Term.prim_mk_const { Name = "scc", Thy = "SCCGraphPlanTheorem"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("scc", (Term.prim_mk_const { Name = "scc", Thy = "SCCGraphPlanTheorem"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("scc_set", (Term.prim_mk_const { Name = "scc_set", Thy = "SCCGraphPlanTheorem"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("scc_set", (Term.prim_mk_const { Name = "scc_set", Thy = "SCCGraphPlanTheorem"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("sum_scc_parents", (Term.prim_mk_const { Name = "sum_scc_parents", Thy = "SCCGraphPlanTheorem"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("sum_scc_parents", (Term.prim_mk_const { Name = "sum_scc_parents", Thy = "SCCGraphPlanTheorem"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("childless_vs", (Term.prim_mk_const { Name = "childless_vs", Thy = "SCCGraphPlanTheorem"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("childless_vs", (Term.prim_mk_const { Name = "childless_vs", Thy = "SCCGraphPlanTheorem"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("childless_svs", (Term.prim_mk_const { Name = "childless_svs", Thy = "SCCGraphPlanTheorem"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("childless_svs", (Term.prim_mk_const { Name = "childless_svs", Thy = "SCCGraphPlanTheorem"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("childless_problem_scc_set", (Term.prim_mk_const { Name = "childless_problem_scc_set", Thy = "SCCGraphPlanTheorem"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("childless_problem_scc_set", (Term.prim_mk_const { Name = "childless_problem_scc_set", Thy = "SCCGraphPlanTheorem"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("member_leaves", (Term.prim_mk_const { Name = "member_leaves", Thy = "SCCGraphPlanTheorem"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("member_leaves", (Term.prim_mk_const { Name = "member_leaves", Thy = "SCCGraphPlanTheorem"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("single_child_parents", (Term.prim_mk_const { Name = "single_child_parents", Thy = "SCCGraphPlanTheorem"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("single_child_parents", (Term.prim_mk_const { Name = "single_child_parents", Thy = "SCCGraphPlanTheorem"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("single_child_ancestors", (Term.prim_mk_const { Name = "single_child_ancestors", Thy = "SCCGraphPlanTheorem"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("single_child_ancestors", (Term.prim_mk_const { Name = "single_child_ancestors", Thy = "SCCGraphPlanTheorem"}))
  val SCCGraphPlanTheorem_grammars = Parse.current_lgrms()
  end
  val _ = Theory.LoadableThyData.temp_encoded_update {
    thy = "SCCGraphPlanTheorem",
    thydataty = "compute",
    data =
        "SCCGraphPlanTheorem.dep_tc_def SCCGraphPlanTheorem.single_child_ancestors_def SCCGraphPlanTheorem.single_child_parents_def SCCGraphPlanTheorem.sum_scc_parents_def SCCGraphPlanTheorem.member_leaves_def SCCGraphPlanTheorem.childless_problem_scc_set_def SCCGraphPlanTheorem.childless_svs_def SCCGraphPlanTheorem.childless_vs_def SCCGraphPlanTheorem.scc_def SCCGraphPlanTheorem.scc_set_def SCCGraphPlanTheorem.ancestors_def"
  }

val _ = if !Globals.print_thy_loads then print "done\n" else ()
val _ = Theory.load_complete "SCCGraphPlanTheorem"
end
