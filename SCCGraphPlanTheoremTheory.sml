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
  local open GraphPlanTheoremTheory SCCTheory
  in end;
  val _ = Theory.link_parents
          ("SCCGraphPlanTheorem",
          Arbnum.fromString "1388649627",
          Arbnum.fromString "546700")
          [("SCC",
           Arbnum.fromString "1388649624",
           Arbnum.fromString "996080"),
           ("GraphPlanTheorem",
           Arbnum.fromString "1388649612",
           Arbnum.fromString "419336")];
  val _ = Theory.incorporate_types "SCCGraphPlanTheorem" [];

  val idvector = 
    let fun ID(thy,oth) = {Thy = thy, Other = oth}
    in Vector.fromList
  [ID("min", "fun"), ID("num", "num"), ID("pair", "prod"),
   ID("min", "bool"), ID("FM_plan", "problem"), ID("finite_map", "fmap"),
   ID("bool", "!"), ID("arithmetic", "+"), ID("pair", ","),
   ID("bool", "/\\"), ID("arithmetic", "<="), ID("min", "="),
   ID("min", "==>"), ID("bool", "?"), ID("pred_set", "BIGUNION"),
   ID("arithmetic", "BIT1"), ID("pred_set", "DELETE"),
   ID("pred_set", "DIFF"), ID("pred_set", "DISJOINT"),
   ID("finite_map", "DRESTRICT"), ID("pred_set", "EMPTY"),
   ID("finite_map", "FDOM"), ID("pred_set", "FINITE"), ID("pair", "FST"),
   ID("pred_set", "GSPEC"), ID("bool", "IN"), ID("pred_set", "INSERT"),
   ID("pred_set", "INTER"), ID("arithmetic", "NUMERAL"),
   ID("pred_set", "REL_RESTRICT"), ID("SCC", "SCC"), ID("pair", "SND"),
   ID("pred_set", "SUBSET"), ID("pred_set", "SUM_IMAGE"),
   ID("relation", "StrongOrder"), ID("relation", "TC"),
   ID("pred_set", "UNION"), ID("arithmetic", "ZERO"),
   ID("GraphPlanTheorem", "action_proj"),
   ID("SCCGraphPlanTheorem", "ancestors"),
   ID("SCCGraphPlanTheorem", "childless_problem_scc_set"),
   ID("SCCGraphPlanTheorem", "childless_svs"),
   ID("SCCGraphPlanTheorem", "childless_vs"),
   ID("GraphPlanTheorem", "dep"), ID("SCCGraphPlanTheorem", "dep_tc"),
   ID("GraphPlanTheorem", "dep_var_set"),
   ID("SCCGraphPlanTheorem", "member_leaves"),
   ID("FM_plan", "planning_problem"), ID("GraphPlanTheorem", "prob_proj"),
   ID("FM_plan", "problem_A"), ID("FM_plan", "problem_I"),
   ID("GraphPlanTheorem", "problem_plan_bound"),
   ID("SCCGraphPlanTheorem", "problem_scc_set"),
   ID("SCCGraphPlanTheorem", "problem_wo_vs_ancestors"),
   ID("SCCGraphPlanTheorem", "scc_set"),
   ID("SCCGraphPlanTheorem", "scc_vs"),
   ID("SCCGraphPlanTheorem", "single_child_ancestors"),
   ID("SCCGraphPlanTheorem", "single_child_parents"),
   ID("SCCGraphPlanTheorem", "sum_scc_parents"), ID("bool", "~")]
  end;
  local open SharingTables
  in
  val tyvector = build_type_vector idvector
  [TYOP [1], TYOP [3], TYV "'a", TYOP [0, 2, 1], TYOP [0, 3, 1],
   TYOP [4, 2], TYOP [2, 5, 4], TYOP [0, 6, 0], TYOP [2, 5, 3],
   TYOP [0, 8, 4], TYOP [0, 3, 4], TYOP [0, 5, 10], TYOP [0, 8, 1],
   TYOP [0, 6, 1], TYOP [0, 8, 5], TYOP [0, 5, 4], TYOP [0, 6, 4],
   TYOP [0, 2, 3], TYOP [0, 5, 17], TYOP [0, 8, 3], TYV "'c",
   TYOP [5, 2, 20], TYV "'b", TYOP [5, 2, 22], TYOP [2, 23, 21],
   TYOP [5, 2, 1], TYOP [2, 25, 25], TYOP [0, 23, 1], TYOP [0, 27, 1],
   TYOP [0, 4, 1], TYOP [0, 17, 1], TYOP [0, 30, 1], TYOP [0, 29, 1],
   TYOP [0, 5, 1], TYOP [0, 33, 1], TYOP [0, 24, 1], TYOP [0, 35, 1],
   TYOP [0, 26, 1], TYOP [0, 37, 1], TYOP [0, 0, 0], TYOP [0, 0, 39],
   TYOP [2, 2, 2], TYOP [0, 2, 41], TYOP [0, 2, 42], TYOP [2, 2, 1],
   TYOP [0, 1, 44], TYOP [0, 2, 45], TYOP [2, 3, 1], TYOP [0, 1, 47],
   TYOP [0, 3, 48], TYOP [2, 3, 3], TYOP [0, 3, 50], TYOP [0, 3, 51],
   TYOP [0, 3, 8], TYOP [0, 5, 53], TYOP [0, 4, 6], TYOP [0, 5, 55],
   TYOP [2, 5, 41], TYOP [0, 41, 57], TYOP [0, 5, 58], TYOP [2, 5, 50],
   TYOP [0, 50, 60], TYOP [0, 5, 61], TYOP [2, 24, 3], TYOP [0, 3, 63],
   TYOP [0, 24, 64], TYOP [2, 26, 3], TYOP [0, 3, 66], TYOP [0, 26, 67],
   TYOP [0, 1, 1], TYOP [0, 1, 69], TYOP [0, 0, 1], TYOP [0, 0, 71],
   TYOP [0, 17, 30], TYOP [0, 4, 29], TYOP [0, 5, 33], TYOP [0, 4, 3],
   TYOP [0, 4, 10], TYOP [0, 3, 3], TYOP [0, 3, 78], TYOP [0, 3, 23],
   TYOP [0, 23, 80], TYOP [0, 23, 3], TYOP [0, 21, 3], TYOP [0, 25, 3],
   TYOP [0, 24, 23], TYOP [0, 26, 25], TYOP [0, 2, 44], TYOP [0, 87, 3],
   TYOP [0, 3, 47], TYOP [0, 89, 4], TYOP [0, 2, 4], TYOP [0, 3, 29],
   TYOP [0, 26, 38], TYOP [0, 4, 4], TYOP [0, 3, 94], TYOP [0, 4, 94],
   TYOP [0, 3, 17], TYOP [0, 17, 97], TYOP [0, 10, 77], TYOP [0, 17, 4],
   TYOP [0, 24, 21], TYOP [0, 4, 0], TYOP [0, 3, 0], TYOP [0, 103, 102],
   TYOP [0, 10, 1], TYOP [0, 17, 17], TYOP [0, 10, 10], TYOP [0, 63, 24],
   TYOP [0, 66, 26], TYOP [0, 57, 1], TYOP [0, 60, 1], TYOP [0, 5, 37],
   TYOP [0, 5, 25], TYOP [0, 5, 0]]
  end
  val _ = Theory.incorporate_consts "SCCGraphPlanTheorem" tyvector
     [("sum_scc_parents", 7), ("single_child_parents", 9),
      ("single_child_ancestors", 11), ("scc_vs", 12), ("scc_set", 13),
      ("problem_wo_vs_ancestors", 14), ("problem_scc_set", 15),
      ("member_leaves", 16), ("dep_tc", 18), ("childless_vs", 12),
      ("childless_svs", 13), ("childless_problem_scc_set", 15),
      ("ancestors", 19)];

  local open SharingTables
  in
  val tmvector = build_term_vector idvector tyvector
  [TMV("P", 3), TMV("PROB", 5), TMV("R", 17), TMV("R'", 17), TMV("S", 4),
   TMV("S'", 4), TMV("a", 24), TMV("a", 26), TMV("f", 23), TMV("fdom", 3),
   TMV("min", 2), TMV("s", 3), TMV("s", 4), TMV("t", 3), TMV("v", 2),
   TMV("v'", 2), TMV("v1", 2), TMV("v1'", 2), TMV("v2", 2), TMV("v2'", 2),
   TMV("vs", 3), TMV("vs'", 3), TMV("vs''", 3), TMV("vs'''", 3),
   TMV("vs1", 3), TMV("vs2", 3), TMV("x", 2), TMV("x'", 2), TMV("y", 2),
   TMC(6, 4), TMC(6, 28), TMC(6, 29), TMC(6, 31), TMC(6, 32), TMC(6, 34),
   TMC(6, 36), TMC(6, 38), TMC(7, 40), TMC(8, 43), TMC(8, 46), TMC(8, 49),
   TMC(8, 52), TMC(8, 54), TMC(8, 56), TMC(8, 59), TMC(8, 62), TMC(8, 65),
   TMC(8, 68), TMC(9, 70), TMC(10, 72), TMC(11, 70), TMC(11, 10),
   TMC(11, 73), TMC(11, 74), TMC(11, 72), TMC(11, 75), TMC(12, 70),
   TMC(13, 4), TMC(13, 29), TMC(14, 76), TMC(15, 39), TMC(16, 77),
   TMC(17, 79), TMC(18, 10), TMC(19, 81), TMC(20, 3), TMC(20, 4),
   TMC(21, 82), TMC(21, 83), TMC(21, 84), TMC(22, 29), TMC(23, 85),
   TMC(23, 86), TMC(24, 88), TMC(24, 90), TMC(25, 91), TMC(25, 92),
   TMC(25, 93), TMC(26, 95), TMC(27, 96), TMC(28, 39), TMC(29, 98),
   TMC(29, 99), TMC(30, 100), TMC(31, 101), TMC(31, 86), TMC(32, 10),
   TMC(32, 74), TMC(33, 104), TMC(34, 105), TMC(35, 106), TMC(35, 107),
   TMC(36, 79), TMC(37, 0), TMC(38, 108), TMC(38, 109), TMC(39, 19),
   TMC(40, 15), TMC(41, 13), TMC(42, 12), TMC(43, 110), TMC(44, 18),
   TMC(45, 111), TMC(46, 16), TMC(47, 33), TMC(48, 14), TMC(49, 112),
   TMC(50, 113), TMC(51, 114), TMC(52, 15), TMC(53, 14), TMC(54, 13),
   TMC(55, 12), TMC(56, 11), TMC(57, 9), TMC(58, 7), TMC(59, 69)]
  end
  local
  val DT = Thm.disk_thm val read = Term.read_raw tmvector
  in
  val op dep_tc_def =
    DT([],
       [read"(%34 (|%1. ((%52 (%101 $0)) (%90 (|%17. (|%19. (%100 ((%44 $2) ((%38 $1) $0)))))))))"])
  val op ancestors_def =
    DT(["DISK_THM"],
       [read"(%34 (|%1. (%31 (|%20. ((%51 (%96 ((%42 $1) $0))) (%73 (|%14. ((%39 $0) ((%48 (%57 (|%15. ((%48 ((%75 $0) $2)) (((%101 $3) $1) $0))))) (%29 (|%15. ((%56 ((%75 $0) $2)) (%116 (((%101 $3) $0) $1))))))))))))))"])
  val op scc_vs_def =
    DT(["DISK_THM"],
       [read"(%34 (|%1. (%31 (|%20. ((%50 (%112 ((%42 $1) $0))) ((%83 (|%17. (|%19. (%100 ((%44 $3) ((%38 $1) $0)))))) $0))))))"])
  val op scc_set_def =
    DT(["DISK_THM"],
       [read"(%34 (|%1. (%33 (|%4. ((%50 (%111 ((%43 $1) $0))) (%31 (|%20. ((%56 ((%48 ((%76 $0) $1)) (%116 ((%63 $0) (%69 (%107 $2)))))) (%112 ((%42 $2) $0))))))))))"])
  val op sum_scc_parents_def =
    DT(["DISK_THM"],
       [read"(%34 (|%1. (%33 (|%4. ((%54 (%115 ((%43 $1) $0))) ((%37 ((%88 (|%20. (%108 (%105 ((%42 $2) ((%92 $0) (%96 ((%42 $2) $0)))))))) $0)) (%80 (%60 %93))))))))"])
  val op childless_vs_def =
    DT(["DISK_THM"],
       [read"(%34 (|%1. (%31 (|%20. ((%50 (%99 ((%42 $1) $0))) (%31 (|%21. (%116 (%102 ((%45 $2) ((%41 $1) $0)))))))))))"])
  val op childless_svs_def =
    DT(["DISK_THM"],
       [read"(%34 (|%1. (%33 (|%4. ((%50 (%98 ((%43 $1) $0))) (%31 (|%20. ((%56 ((%76 $0) $1)) (%99 ((%42 $2) $0))))))))))"])
  val op problem_scc_set_def =
    DT([],
       [read"(%34 (|%1. ((%53 (%109 $0)) (%74 (|%20. ((%40 $0) (%112 ((%42 $1) $0))))))))"])
  val op childless_problem_scc_set_def =
    DT([],
       [read"(%34 (|%1. ((%53 (%97 $0)) (%74 (|%20. ((%40 $0) ((%48 (%112 ((%42 $1) $0))) (%99 ((%42 $1) $0)))))))))"])
  val op single_child_parents_def =
    DT(["DISK_THM"],
       [read"(%34 (|%1. (%31 (|%20. ((%53 (%114 ((%42 $1) $0))) (%74 (|%21. ((%40 $0) ((%48 ((%86 $0) (%96 ((%42 $2) $1)))) ((%48 (%99 ((%42 (%105 ((%42 $2) ((%62 (%69 (%107 $2))) $1)))) $0))) (%112 ((%42 $2) $0))))))))))))"])
  val op single_child_ancestors_def =
    DT([],
       [read"(%34 (|%1. (%31 (|%20. ((%53 ((%113 $1) $0)) (%74 (|%21. ((%40 $0) ((%48 (%112 ((%42 $2) $0))) ((%48 (((%91 (|%20. (|%21. (%102 ((%45 $4) ((%41 $1) $0)))))) $0) $1)) (%58 (|%23. (%31 (|%22. ((%56 (%102 ((%45 $4) ((%41 $2) $0)))) ((%51 $0) $1))))))))))))))))"])
  val op member_leaves_def =
    DT(["DISK_THM"],
       [read"(%34 (|%1. (%33 (|%4. ((%53 (%103 ((%43 $1) $0))) ((%79 (|%20. ((%48 (%112 ((%42 $2) $0))) (%99 ((%42 $2) $0))))) $0))))))"])
  val op problem_wo_vs_ancestors_def =
    DT(["DISK_THM"],
       [read"(%34 (|%1. (%31 (|%20. ((%55 (%110 ((%42 $1) $0))) (%105 ((%42 $1) ((%62 (%69 (%107 $1))) ((%92 $0) (%59 ((%113 $1) $0)))))))))))"])
  val op scc_main_lemma_x =
    DT(["DISK_THM"],
       [read"(%31 (|%11. (%31 (|%13. (%29 (|%26. ((%56 ((%48 ((%75 $0) $2)) (%116 ((%75 $0) $1)))) (%116 ((%51 $2) $1)))))))))"])
  val op scc_main_lemma_1_xx =
    DT(["DISK_THM"],
       [read"(%34 (|%1. (%31 (|%20. (%31 (|%21. ((%56 ((%48 (%112 ((%42 $2) $1))) ((%48 (%112 ((%42 $2) $0))) (%116 ((%51 $1) $0))))) ((%63 $1) $0))))))))"])
  val op scc_lemma_1_1 =
    DT(["DISK_THM"],
       [read"(%34 (|%1. (%33 (|%4. ((%56 (%70 $0)) (%70 (%103 ((%43 $1) $0))))))))"])
  val op scc_lemma_1_2 =
    DT(["DISK_THM"],
       [read"(%34 (|%1. (%31 (|%20. (%33 (|%4. ((%56 ((%76 $1) (%103 ((%43 $2) $0)))) (%112 ((%42 $2) $1)))))))))"])
  val op scc_lemma_1_3 =
    DT(["DISK_THM"],
       [read"(%34 (|%1. (%31 (|%20. (%33 (|%4. ((%56 ((%76 $1) (%103 ((%43 $2) $0)))) ((%76 $1) $0))))))))"])
  val op scc_lemma_1_5 =
    DT(["DISK_THM"],
       [read"(%34 (|%1. (%31 (|%20. (%33 (|%4. ((%56 ((%76 $1) (%103 ((%43 $2) $0)))) (%99 ((%42 $2) $1)))))))))"])
  val op scc_lemma_1_4_1_1_1 =
    DT(["DISK_THM"],
       [read"(%34 (|%1. (%31 (|%20. (%31 (|%21. ((%56 ((%48 (%112 ((%42 $2) $0))) (%99 ((%42 $2) $0)))) ((%63 $0) (%59 ((%113 $2) $1))))))))))"])
  val op scc_lemma_1_4_1_1_2_1_1_1_1 =
    DT(["DISK_THM"],
       [read"(%31 (|%9. (%31 (|%20. (%29 (|%14. (%30 (|%8. ((%56 ((%48 (%116 ((%75 $1) $2))) ((%48 ((%86 (%67 $0)) $3)) ((%75 $1) (%67 $0))))) ((%75 $1) (%67 ((%64 $0) ((%62 $3) $2)))))))))))))"])
  val op scc_lemma_1_4_1_1_2_1_1_1 =
    DT(["DISK_THM"],
       [read"(%34 (|%1. (%31 (|%20. (%29 (|%14. (%36 (|%7. ((%56 ((%48 (%116 ((%75 $1) $2))) ((%48 ((%77 $0) (%106 $3))) (%104 $3)))) ((%48 ((%56 ((%75 $1) (%69 (%72 $0)))) ((%75 $1) (%69 (%72 (%95 ((%47 $0) ((%62 (%69 (%107 $3))) $2)))))))) ((%56 ((%75 $1) (%69 (%85 $0)))) ((%75 $1) (%69 (%85 (%95 ((%47 $0) ((%62 (%69 (%107 $3))) $2)))))))))))))))))"])
  val op scc_lemma_1_4_1_1_2_1_1 =
    DT(["DISK_THM"],
       [read"(%34 (|%1. (%31 (|%20. (%31 (|%21. (%29 (|%14. (%29 (|%15. ((%56 ((%48 (%104 $4)) ((%48 ((%75 $1) $2)) ((%48 ((%75 $0) $2)) ((%63 $3) $2))))) ((%56 (%100 ((%44 $4) ((%38 $1) $0)))) (%100 ((%44 (%105 ((%42 $4) ((%62 (%69 (%107 $4))) $3)))) ((%38 $1) $0)))))))))))))))"])
  val op scc_lemma_1_4_1_1_2_1_2 =
    DT(["DISK_THM"],
       [read"(%32 (|%2. (%32 (|%3. (%31 (|%0. ((%56 (%29 (|%26. (%29 (|%28. ((%56 ((%48 ($2 $1)) ($2 $0))) ((%48 ((%56 (($4 $1) $0)) (($3 $1) $0))) (((%90 (|%26. (|%28. ((%48 (($6 $1) $0)) ((%48 ($4 $1)) ($4 $0)))))) $1) $0)))))))) (%29 (|%26. (%29 (|%28. ((%56 ((%48 ($2 $1)) ($2 $0))) (((%90 $3) $1) $0)))))))))))))"])
  val op scc_lemma_1_4_1_1_2_1_4 =
    DT(["DISK_THM"],
       [read"(%34 (|%1. (%31 (|%20. (%29 (|%14. (%29 (|%15. ((%56 (%100 ((%44 (%105 ((%42 $3) ((%62 (%69 (%107 $3))) $2)))) ((%38 $1) $0)))) (%100 ((%44 $3) ((%38 $1) $0))))))))))))"])
  val op scc_lemma_1_4_1_1_2_1 =
    DT(["DISK_THM", "cheat"],
       [read"(%34 (|%1. (%31 (|%20. (%31 (|%21. ((%56 ((%48 (%104 $2)) ((%48 (%112 ((%42 $2) $0))) ((%63 $1) $0)))) (%112 ((%42 (%105 ((%42 $2) ((%62 (%69 (%107 $2))) $1)))) $0)))))))))"])
  val op scc_lemma_1_4_1_1_2_2_1_1_1 =
    DT(["DISK_THM"],
       [read"(%35 (|%6. (%31 (|%20. ((%48 ((%86 (%67 (%71 (%94 ((%46 $1) $0))))) (%67 (%71 $1)))) ((%86 (%68 (%84 (%94 ((%46 $1) $0))))) (%68 (%84 $1))))))))"])
  val op scc_lemma_1_4_1_1_2_2_1_1 =
    DT(["DISK_THM"],
       [read"(%35 (|%6. (%29 (|%14. (%31 (|%20. ((%48 ((%56 (%116 ((%75 $1) (%67 (%71 $2))))) (%116 ((%75 $1) (%67 (%71 (%94 ((%46 $2) $0)))))))) ((%56 (%116 ((%75 $1) (%68 (%84 $2))))) (%116 ((%75 $1) (%68 (%84 (%94 ((%46 $2) $0))))))))))))))"])
  val op scc_lemma_1_4_1_1_2_2_1 =
    DT(["DISK_THM"],
       [read"(%34 (|%1. (%31 (|%20. (%31 (|%21. (%31 (|%22. ((%56 (%116 (%102 ((%45 $3) ((%41 $2) $1))))) (%116 (%102 ((%45 (%105 ((%42 $3) $0))) ((%41 $2) $1)))))))))))))"])
  val op scc_lemma_1_4_1_1_2_2 =
    DT(["DISK_THM"],
       [read"(%34 (|%1. (%31 (|%20. (%31 (|%21. ((%56 (%99 ((%42 $2) $0))) (%99 ((%42 (%105 ((%42 $2) ((%62 (%69 (%107 $2))) $1)))) $0)))))))))"])
  val op scc_lemma_1_4_1_1_2 =
    DT(["DISK_THM", "cheat"],
       [read"(%34 (|%1. (%31 (|%20. (%31 (|%21. (%33 (|%4. ((%56 ((%48 (%104 $3)) ((%48 ((%63 $2) $1)) ((%76 $1) (%103 ((%43 $3) $0)))))) ((%76 $1) (%103 ((%43 (%105 ((%42 $3) ((%62 (%69 (%107 $3))) $2)))) $0))))))))))))"])
  val op scc_lemma_1_4_1_1 =
    DT(["DISK_THM", "cheat"],
       [read"(%34 (|%1. (%31 (|%20. (%31 (|%21. (%33 (|%4. ((%56 ((%48 (%104 $3)) ((%48 (%112 ((%42 $3) $2))) ((%48 (%116 ((%51 $2) $1))) ((%76 $1) (%103 ((%43 $3) $0))))))) ((%76 $1) (%103 ((%43 (%110 ((%42 $3) $2))) $0))))))))))))"])
  val op scc_lemma_1_4_1 =
    DT(["DISK_THM", "cheat"],
       [read"(%34 (|%1. (%33 (|%4. (%31 (|%20. ((%56 ((%48 (%104 $2)) (%112 ((%42 $2) $0)))) ((%87 ((%61 (%103 ((%43 $2) $1))) $0)) (%103 ((%43 (%110 ((%42 $2) $0))) $1))))))))))"])
  val op scc_lemma_1_4_2 =
    DT(["cheat"],
       [read"(%34 (|%1. (%31 (|%20. (%31 (|%22. (%33 (|%4. (%31 (|%21. ((%56 ((%48 (%116 ((%76 $0) ((%113 $4) $3)))) ((%48 (%116 ((%76 $0) ((%61 (%103 ((%43 $4) $1))) $2)))) ((%86 $2) $3)))) (%116 ((%76 $0) (%103 ((%43 (%105 ((%42 $4) ((%62 (%69 (%107 $4))) $3)))) $1)))))))))))))))"])
  val op scc_lemma_1_4_3 =
    DT(["cheat"],
       [read"(%34 (|%1. (%31 (|%20. ((%53 ((%113 $1) ((%92 $0) (%59 ((%113 $1) $0))))) %66)))))"])
  val op scc_lemma_1_4_4 =
    DT(["DISK_THM"],
       [read"(%31 (|%11. (%31 (|%13. ((%56 (%29 (|%26. ((%56 (%116 ((%75 $0) $2))) (%116 ((%75 $0) $1)))))) ((%51 ((%62 $0) $1)) %65))))))"])
  val op scc_lemma_1_4 =
    DT(["DISK_THM", "cheat"],
       [read"(%33 (|%4. ((%56 (%70 $0)) (%34 (|%1. (%31 (|%20. (%33 (|%5. ((%56 ((%48 (%104 $2)) ((%48 (%112 ((%42 $2) $1))) ((%48 (%116 ((%76 $1) $0))) ((%53 (%103 ((%43 $2) $3))) ((%78 $1) $0)))))) ((%53 (%103 ((%43 (%110 ((%42 $2) $1))) $3))) $0)))))))))))"])
  val op scc_main_lemma_1_1_1_1_1_1 =
    DT(["DISK_THM"],
       [read"(%34 (|%1. (%29 (|%16. (%29 (|%18. ((%56 ((%48 (%104 $2)) (%100 ((%44 $2) ((%38 $1) $0))))) ((%48 ((%75 $1) (%69 (%107 $2)))) ((%75 $0) (%69 (%107 $2)))))))))))"])
  val op scc_main_lemma_1_1_1_1_1 =
    DT(["DISK_THM"],
       [read"(%34 (|%1. (%29 (|%16. (%29 (|%18. ((%56 ((%48 (%104 $2)) (((%101 $2) $1) $0))) ((%75 $1) (%69 (%107 $2))))))))))"])
  val op scc_main_lemma_1_1_1_1 =
    DT(["DISK_THM"],
       [read"(%34 (|%1. (%31 (|%20. ((%56 ((%48 (%104 $1)) (%112 ((%42 $1) $0)))) ((%86 $0) (%69 (%107 $1))))))))"])
  val op scc_main_lemma_1_1_1_2 =
    DT(["DISK_THM"],
       [read"(%34 (|%1. (%31 (|%20. (%31 (|%21. ((%56 ((%48 (%116 ((%63 $1) $0))) ((%48 (%112 ((%42 $2) $1))) (%112 ((%42 $2) $0))))) ((%51 $1) $0))))))))"])
  val op scc_main_lemma_1_1_1 =
    DT(["DISK_THM"],
       [read"(%34 (|%1. (%33 (|%4. (%31 (|%20. ((%56 ((%48 (%104 $2)) ((%48 ((%86 (%69 (%107 $2))) (%59 $1))) ((%48 (%111 ((%43 $2) $1))) (%112 ((%42 $2) $0)))))) ((%76 $0) $1))))))))"])
  val op scc_main_lemma_1_1 =
    DT(["DISK_THM"],
       [read"(%34 (|%1. (%33 (|%4. ((%56 ((%48 (%104 $1)) ((%48 ((%86 (%69 (%107 $1))) (%59 $0))) (%111 ((%43 $1) $0))))) ((%53 (%97 $1)) (%103 ((%43 $1) $0))))))))"])
  val op scc_main_lemma_1_2_1 =
    DT(["DISK_THM"],
       [read"(%34 (|%1. ((%56 (%104 $0)) ((%56 ((%51 (%69 (%107 $0))) %65)) (%31 (|%20. (%116 (%112 ((%42 $1) $0)))))))))"])
  val op scc_main_lemma_1_2_2_1 =
    DT(["cheat"],
       [read"(%34 (|%1. (%89 ((%82 (%91 (|%24. (|%25. (%102 ((%45 $2) ((%41 $0) $1))))))) (%109 $0)))))"])
  val op scc_main_lemma_1_2_2_2 =
    DT(["cheat"], [read"(%34 (|%1. (%70 (%109 $0))))"])
  val op scc_main_lemma_1_2_2_3 =
    DT(["cheat"],
       [read"(%34 (|%1. ((%56 ((%48 (%116 ((%51 (%69 (%107 $0))) %65))) (%104 $0))) (%58 (|%20. (%112 ((%42 $1) $0)))))))"])
  val op scc_main_lemma_1_2_2_4 =
    DT(["cheat"],
       [read"(%32 (|%2. (%31 (|%11. (%29 (|%10. ((%56 (%29 (|%26. ((%56 ((((%81 (%90 $3)) $2) $0) $1)) (%116 ((%75 $0) $2)))))) (%29 (|%27. ((%56 ((%75 $0) $2)) (%116 (($3 $0) $1))))))))))))"])
  val op scc_main_lemma_1_2_2 =
    DT(["cheat"],
       [read"(%34 (|%1. ((%56 ((%48 (%104 $0)) (%116 ((%51 (%69 (%107 $0))) %65)))) (%58 (|%20. ((%48 (%112 ((%42 $1) $0))) (%99 ((%42 $1) $0))))))))"])
  val op scc_main_lemma_1_2 =
    DT(["DISK_THM", "cheat"],
       [read"(%34 (|%1. ((%56 (%104 $0)) ((%50 ((%51 (%69 (%107 $0))) %65)) ((%53 (%97 $0)) %66)))))"])
  val op scc_main_lemma_1_3 =
    DT(["cheat"],
       [read"(%34 (|%1. (%33 (|%4. (%33 (|%5. ((%56 ((%48 (%111 ((%43 $2) $1))) ((%87 $0) $1))) (%111 ((%43 (%105 ((%42 $2) ((%62 (%69 (%107 $2))) (%59 $0))))) $1)))))))))"])
  val op scc_main_lemma_1_4 =
    DT(["cheat"],
       [read"(%34 (|%1. (%31 (|%20. (%33 (|%4. ((%56 ((%48 (%111 ((%43 $2) $0))) ((%48 (%112 ((%42 $2) $1))) ((%86 (%69 (%107 $2))) (%59 $0))))) ((%87 ((%113 $2) $1)) $0))))))))"])
  val op scc_main_lemma_1_5 =
    DT(["cheat"],
       [read"(%34 (|%1. (%31 (|%20. (%31 (|%21. ((%56 ((%86 (%69 (%107 $2))) $1)) ((%86 (%69 (%107 (%105 ((%42 $2) $0))))) $1))))))))"])
  val op scc_main_lemma_1_6 =
    DT(["cheat"],
       [read"(%34 (|%1. (%31 (|%20. (%33 (|%4. (%33 (|%5. ((%56 ((%48 ((%53 (%103 ((%43 $3) $1))) ((%78 $2) $0))) (%116 ((%76 $2) $0)))) ((%54 (%115 ((%43 (%110 ((%42 $3) $2))) (%103 ((%43 (%110 ((%42 $3) $2))) $1))))) (%115 ((%43 $3) $0))))))))))))"])
  val op scc_main_lemma_1_7 =
    DT(["cheat"],
       [read"(%34 (|%1. (%31 (|%20. ((%56 ((%48 (%99 ((%42 $1) $0))) (%112 ((%42 $1) $0)))) ((%49 (%108 $1)) ((%37 (%108 (%110 ((%42 $1) $0)))) (%108 (%105 ((%42 $1) ((%92 $0) (%96 ((%42 $1) $0)))))))))))))"])
  val op scc_main_lemma_1 =
    DT(["DISK_THM", "cheat"],
       [read"(%33 (|%12. ((%56 (%70 $0)) (%33 (|%4. (%34 (|%1. ((%56 ((%48 (%104 $0)) ((%48 (%111 ((%43 $0) $1))) ((%48 ((%86 (%69 (%107 $0))) (%59 $1))) ((%48 ((%48 (%116 ((%53 $1) %66))) (%116 ((%53 $1) ((%78 %65) %66))))) ((%48 (%70 $1)) ((%53 $2) (%103 ((%43 $0) $1))))))))) ((%49 (%108 $0)) (%115 ((%43 $0) (%103 ((%43 $0) $1)))))))))))))"])
  val op scc_main_lemma =
    DT(["DISK_THM", "cheat"],
       [read"(%33 (|%4. (%34 (|%1. ((%56 ((%48 (%104 $0)) ((%48 (%111 ((%43 $0) $1))) ((%48 ((%86 (%69 (%107 $0))) (%59 $1))) ((%48 (%116 ((%51 (%59 $1)) %65))) (%70 $1)))))) ((%49 (%108 $0)) (%115 ((%43 $0) (%103 ((%43 $0) $1))))))))))"])
  end
  val _ = DB.bindl "SCCGraphPlanTheorem"
  [("dep_tc_def",dep_tc_def,DB.Def),
   ("ancestors_def",ancestors_def,DB.Def),
   ("scc_vs_def",scc_vs_def,DB.Def), ("scc_set_def",scc_set_def,DB.Def),
   ("sum_scc_parents_def",sum_scc_parents_def,DB.Def),
   ("childless_vs_def",childless_vs_def,DB.Def),
   ("childless_svs_def",childless_svs_def,DB.Def),
   ("problem_scc_set_def",problem_scc_set_def,DB.Def),
   ("childless_problem_scc_set_def",childless_problem_scc_set_def,DB.Def),
   ("single_child_parents_def",single_child_parents_def,DB.Def),
   ("single_child_ancestors_def",single_child_ancestors_def,DB.Def),
   ("member_leaves_def",member_leaves_def,DB.Def),
   ("problem_wo_vs_ancestors_def",problem_wo_vs_ancestors_def,DB.Def),
   ("scc_main_lemma_x",scc_main_lemma_x,DB.Thm),
   ("scc_main_lemma_1_xx",scc_main_lemma_1_xx,DB.Thm),
   ("scc_lemma_1_1",scc_lemma_1_1,DB.Thm),
   ("scc_lemma_1_2",scc_lemma_1_2,DB.Thm),
   ("scc_lemma_1_3",scc_lemma_1_3,DB.Thm),
   ("scc_lemma_1_5",scc_lemma_1_5,DB.Thm),
   ("scc_lemma_1_4_1_1_1",scc_lemma_1_4_1_1_1,DB.Thm),
   ("scc_lemma_1_4_1_1_2_1_1_1_1",scc_lemma_1_4_1_1_2_1_1_1_1,DB.Thm),
   ("scc_lemma_1_4_1_1_2_1_1_1",scc_lemma_1_4_1_1_2_1_1_1,DB.Thm),
   ("scc_lemma_1_4_1_1_2_1_1",scc_lemma_1_4_1_1_2_1_1,DB.Thm),
   ("scc_lemma_1_4_1_1_2_1_2",scc_lemma_1_4_1_1_2_1_2,DB.Thm),
   ("scc_lemma_1_4_1_1_2_1_4",scc_lemma_1_4_1_1_2_1_4,DB.Thm),
   ("scc_lemma_1_4_1_1_2_1",scc_lemma_1_4_1_1_2_1,DB.Thm),
   ("scc_lemma_1_4_1_1_2_2_1_1_1",scc_lemma_1_4_1_1_2_2_1_1_1,DB.Thm),
   ("scc_lemma_1_4_1_1_2_2_1_1",scc_lemma_1_4_1_1_2_2_1_1,DB.Thm),
   ("scc_lemma_1_4_1_1_2_2_1",scc_lemma_1_4_1_1_2_2_1,DB.Thm),
   ("scc_lemma_1_4_1_1_2_2",scc_lemma_1_4_1_1_2_2,DB.Thm),
   ("scc_lemma_1_4_1_1_2",scc_lemma_1_4_1_1_2,DB.Thm),
   ("scc_lemma_1_4_1_1",scc_lemma_1_4_1_1,DB.Thm),
   ("scc_lemma_1_4_1",scc_lemma_1_4_1,DB.Thm),
   ("scc_lemma_1_4_2",scc_lemma_1_4_2,DB.Thm),
   ("scc_lemma_1_4_3",scc_lemma_1_4_3,DB.Thm),
   ("scc_lemma_1_4_4",scc_lemma_1_4_4,DB.Thm),
   ("scc_lemma_1_4",scc_lemma_1_4,DB.Thm),
   ("scc_main_lemma_1_1_1_1_1_1",scc_main_lemma_1_1_1_1_1_1,DB.Thm),
   ("scc_main_lemma_1_1_1_1_1",scc_main_lemma_1_1_1_1_1,DB.Thm),
   ("scc_main_lemma_1_1_1_1",scc_main_lemma_1_1_1_1,DB.Thm),
   ("scc_main_lemma_1_1_1_2",scc_main_lemma_1_1_1_2,DB.Thm),
   ("scc_main_lemma_1_1_1",scc_main_lemma_1_1_1,DB.Thm),
   ("scc_main_lemma_1_1",scc_main_lemma_1_1,DB.Thm),
   ("scc_main_lemma_1_2_1",scc_main_lemma_1_2_1,DB.Thm),
   ("scc_main_lemma_1_2_2_1",scc_main_lemma_1_2_2_1,DB.Thm),
   ("scc_main_lemma_1_2_2_2",scc_main_lemma_1_2_2_2,DB.Thm),
   ("scc_main_lemma_1_2_2_3",scc_main_lemma_1_2_2_3,DB.Thm),
   ("scc_main_lemma_1_2_2_4",scc_main_lemma_1_2_2_4,DB.Thm),
   ("scc_main_lemma_1_2_2",scc_main_lemma_1_2_2,DB.Thm),
   ("scc_main_lemma_1_2",scc_main_lemma_1_2,DB.Thm),
   ("scc_main_lemma_1_3",scc_main_lemma_1_3,DB.Thm),
   ("scc_main_lemma_1_4",scc_main_lemma_1_4,DB.Thm),
   ("scc_main_lemma_1_5",scc_main_lemma_1_5,DB.Thm),
   ("scc_main_lemma_1_6",scc_main_lemma_1_6,DB.Thm),
   ("scc_main_lemma_1_7",scc_main_lemma_1_7,DB.Thm),
   ("scc_main_lemma_1",scc_main_lemma_1,DB.Thm),
   ("scc_main_lemma",scc_main_lemma,DB.Thm)]

  local open Portable GrammarSpecials Parse
    fun UTOFF f = Feedback.trace("Parse.unicode_trace_off_complaints",0)f
  in
  val _ = mk_local_grms [("SCCTheory.SCC_grammars",SCCTheory.SCC_grammars),
                         ("GraphPlanTheoremTheory.GraphPlanTheorem_grammars",
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
       ("scc_vs", (Term.prim_mk_const { Name = "scc_vs", Thy = "SCCGraphPlanTheorem"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("scc_vs", (Term.prim_mk_const { Name = "scc_vs", Thy = "SCCGraphPlanTheorem"}))
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
       ("problem_scc_set", (Term.prim_mk_const { Name = "problem_scc_set", Thy = "SCCGraphPlanTheorem"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("problem_scc_set", (Term.prim_mk_const { Name = "problem_scc_set", Thy = "SCCGraphPlanTheorem"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("childless_problem_scc_set", (Term.prim_mk_const { Name = "childless_problem_scc_set", Thy = "SCCGraphPlanTheorem"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("childless_problem_scc_set", (Term.prim_mk_const { Name = "childless_problem_scc_set", Thy = "SCCGraphPlanTheorem"}))
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
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("member_leaves", (Term.prim_mk_const { Name = "member_leaves", Thy = "SCCGraphPlanTheorem"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("member_leaves", (Term.prim_mk_const { Name = "member_leaves", Thy = "SCCGraphPlanTheorem"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("problem_wo_vs_ancestors", (Term.prim_mk_const { Name = "problem_wo_vs_ancestors", Thy = "SCCGraphPlanTheorem"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("problem_wo_vs_ancestors", (Term.prim_mk_const { Name = "problem_wo_vs_ancestors", Thy = "SCCGraphPlanTheorem"}))
  val SCCGraphPlanTheorem_grammars = Parse.current_lgrms()
  end
  val _ = Theory.LoadableThyData.temp_encoded_update {
    thy = "SCCGraphPlanTheorem",
    thydataty = "compute",
    data =
        "SCCGraphPlanTheorem.dep_tc_def SCCGraphPlanTheorem.single_child_ancestors_def SCCGraphPlanTheorem.problem_wo_vs_ancestors_def SCCGraphPlanTheorem.member_leaves_def SCCGraphPlanTheorem.single_child_parents_def SCCGraphPlanTheorem.sum_scc_parents_def SCCGraphPlanTheorem.childless_problem_scc_set_def SCCGraphPlanTheorem.problem_scc_set_def SCCGraphPlanTheorem.childless_svs_def SCCGraphPlanTheorem.childless_vs_def SCCGraphPlanTheorem.scc_set_def SCCGraphPlanTheorem.scc_vs_def SCCGraphPlanTheorem.ancestors_def"
  }

val _ = if !Globals.print_thy_loads then print "done\n" else ()
val _ = Theory.load_complete "SCCGraphPlanTheorem"
end
