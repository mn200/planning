structure FM_planTheory :> FM_planTheory =
struct
  val _ = if !Globals.print_thy_loads then print "Loading FM_planTheory ... " else ()
  open Type Term Thm
  infixr -->

  fun C s t ty = mk_thy_const{Name=s,Thy=t,Ty=ty}
  fun T s t A = mk_thy_type{Tyop=s, Thy=t,Args=A}
  fun V s q = mk_var(s,q)
  val U     = mk_vartype
  (*  Parents *)
  local open finite_mapTheory sublistTheory
  in end;
  val _ = Theory.link_parents
          ("FM_plan",
          Arbnum.fromString "1389312279",
          Arbnum.fromString "964668")
          [("sublist",
           Arbnum.fromString "1389312277",
           Arbnum.fromString "459717"),
           ("finite_map",
           Arbnum.fromString "1378778625",
           Arbnum.fromString "519479")];
  val _ = Theory.incorporate_types "FM_plan" [("problem", 1)];

  val idvector = 
    let fun ID(thy,oth) = {Thy = thy, Other = oth}
    in Vector.fromList
  [ID("min", "fun"), ID("finite_map", "fmap"), ID("min", "bool"),
   ID("pair", "prod"), ID("list", "list"), ID("num", "num"),
   ID("FM_plan", "problem"), ID("ind_type", "recspace"), ID("min", "ind"),
   ID("bool", "!"), ID("arithmetic", "+"), ID("pair", ","),
   ID("bool", "/\\"), ID("num", "0"), ID("prim_rec", "<"),
   ID("arithmetic", "<="), ID("min", "="), ID("min", "==>"),
   ID("arithmetic", ">"), ID("arithmetic", ">="), ID("bool", "?"),
   ID("min", "@"), ID("list", "APPEND"), ID("bool", "ARB"),
   ID("arithmetic", "BIT1"), ID("arithmetic", "BIT2"),
   ID("ind_type", "BOTTOM"), ID("pred_set", "CARD"), ID("bool", "COND"),
   ID("list", "CONS"), ID("ind_type", "CONSTR"), ID("bool", "DATATYPE"),
   ID("pred_set", "DISJOINT"), ID("pred_set", "EMPTY"),
   ID("arithmetic", "EXP"), ID("bool", "F"), ID("finite_map", "FDOM"),
   ID("pred_set", "FINITE"), ID("list", "FRONT"), ID("pair", "FST"),
   ID("finite_map", "FUNION"), ID("finite_map", "FUPDATE"),
   ID("pred_set", "GSPEC"), ID("combin", "I"), ID("pred_set", "IMAGE"),
   ID("bool", "IN"), ID("pred_set", "INJ"), ID("pred_set", "INSERT"),
   ID("rich_list", "IS_SUFFIX"), ID("combin", "K"), ID("list", "LAST"),
   ID("list", "LENGTH"), ID("list", "LIST_TO_SET"), ID("list", "NIL"),
   ID("arithmetic", "NUMERAL"), ID("pair", "SND"),
   ID("finite_map", "SUBMAP"), ID("pred_set", "SUBSET"), ID("num", "SUC"),
   ID("bool", "T"), ID("bool", "TYPE_DEFINITION"), ID("pred_set", "UNION"),
   ID("relation", "WF"), ID("relation", "WFREC"), ID("arithmetic", "ZERO"),
   ID("basicSize", "bool_size"), ID("FM_plan", "exec_plan"),
   ID("finite_map", "fmap_size"), ID("list", "isPREFIX"),
   ID("list", "list_CASE"), ID("combin", "o"), ID("pair", "pair_CASE"),
   ID("FM_plan", "plan"), ID("FM_plan", "planning_problem"),
   ID("FM_plan", "problem_A"), ID("FM_plan", "problem_A_fupd"),
   ID("FM_plan", "problem_CASE"), ID("FM_plan", "problem_G"),
   ID("FM_plan", "problem_G_fupd"), ID("FM_plan", "problem_I"),
   ID("FM_plan", "problem_I_fupd"), ID("FM_plan", "problem_size"),
   ID("FM_plan", "state_list"), ID("FM_plan", "state_set"),
   ID("FM_plan", "state_succ"), ID("sublist", "sublist"), ID("bool", "~")]
  end;
  local open SharingTables
  in
  val tyvector = build_type_vector idvector
  [TYOP [2], TYV "'a", TYOP [1, 1, 0], TYOP [3, 2, 2], TYOP [0, 3, 2],
   TYOP [0, 2, 4], TYOP [4, 1], TYOP [0, 6, 0], TYOP [0, 6, 7],
   TYOP [4, 2], TYOP [4, 3], TYOP [3, 2, 10], TYOP [0, 11, 9], TYOP [5],
   TYOP [6, 1], TYOP [0, 14, 13], TYOP [0, 1, 13], TYOP [0, 16, 15],
   TYOP [0, 14, 14], TYOP [0, 2, 2], TYOP [0, 19, 18], TYOP [0, 14, 2],
   TYV "'b", TYOP [0, 2, 22], TYOP [0, 3, 0], TYOP [0, 24, 23],
   TYOP [0, 2, 25], TYOP [0, 26, 22], TYOP [0, 14, 27], TYOP [0, 24, 24],
   TYOP [0, 29, 18], TYOP [0, 14, 24], TYOP [0, 2, 14], TYOP [0, 24, 32],
   TYOP [0, 2, 33], TYOP [0, 14, 0], TYOP [3, 14, 10], TYOP [0, 36, 0],
   TYOP [0, 11, 2], TYOP [3, 24, 2], TYOP [3, 2, 39], TYOP [7, 40],
   TYOP [0, 41, 0], TYOP [0, 1, 0], TYOP [3, 1, 22], TYOP [0, 44, 0],
   TYOP [0, 11, 0], TYOP [0, 11, 46], TYOP [0, 1, 22], TYOP [0, 22, 13],
   TYOP [0, 14, 22], TYOP [0, 22, 14], TYOP [8], TYOP [0, 2, 0],
   TYOP [0, 24, 53], TYOP [0, 2, 54], TYOP [0, 52, 55], TYOP [0, 14, 41],
   TYOP [0, 43, 0], TYOP [0, 22, 0], TYOP [0, 59, 0], TYOP [0, 53, 0],
   TYOP [0, 48, 0], TYOP [0, 62, 0], TYOP [0, 58, 0], TYOP [0, 16, 0],
   TYOP [0, 65, 0], TYOP [0, 49, 0], TYOP [0, 67, 0], TYOP [0, 51, 0],
   TYOP [0, 69, 0], TYOP [0, 19, 0], TYOP [0, 71, 0], TYOP [0, 26, 0],
   TYOP [0, 73, 0], TYOP [0, 29, 0], TYOP [0, 75, 0], TYOP [0, 35, 0],
   TYOP [0, 77, 0], TYOP [0, 45, 0], TYOP [0, 79, 0], TYOP [0, 24, 0],
   TYOP [0, 81, 0], TYOP [0, 46, 0], TYOP [0, 83, 0], TYOP [0, 42, 0],
   TYOP [0, 85, 0], TYOP [0, 7, 0], TYOP [0, 9, 0], TYOP [0, 88, 0],
   TYOP [0, 10, 0], TYOP [0, 90, 0], TYOP [0, 13, 0], TYOP [0, 92, 0],
   TYOP [0, 13, 13], TYOP [0, 13, 94], TYOP [0, 22, 44], TYOP [0, 1, 96],
   TYOP [3, 1, 0], TYOP [0, 0, 98], TYOP [0, 1, 99], TYOP [3, 2, 0],
   TYOP [0, 0, 101], TYOP [0, 2, 102], TYOP [0, 10, 11], TYOP [0, 2, 104],
   TYOP [0, 39, 40], TYOP [0, 2, 106], TYOP [0, 2, 39], TYOP [0, 24, 108],
   TYOP [0, 10, 36], TYOP [0, 14, 110], TYOP [0, 0, 0], TYOP [0, 0, 112],
   TYOP [0, 13, 92], TYOP [0, 1, 43], TYOP [0, 22, 59], TYOP [0, 2, 53],
   TYOP [0, 43, 58], TYOP [0, 51, 69], TYOP [0, 53, 61], TYOP [0, 7, 87],
   TYOP [0, 18, 0], TYOP [0, 18, 122], TYOP [0, 24, 81], TYOP [0, 38, 0],
   TYOP [0, 38, 125], TYOP [0, 12, 0], TYOP [0, 12, 127], TYOP [0, 9, 88],
   TYOP [0, 10, 90], TYOP [0, 14, 35], TYOP [0, 41, 42], TYOP [0, 50, 0],
   TYOP [0, 133, 0], TYOP [0, 57, 0], TYOP [0, 135, 0], TYOP [0, 47, 0],
   TYOP [0, 137, 47], TYOP [0, 6, 6], TYOP [0, 6, 139], TYOP [0, 10, 10],
   TYOP [0, 10, 141], TYOP [0, 43, 13], TYOP [0, 59, 13], TYOP [0, 53, 13],
   TYOP [0, 7, 13], TYOP [0, 88, 13], TYOP [0, 2, 19], TYOP [0, 0, 148],
   TYOP [0, 1, 139], TYOP [0, 9, 9], TYOP [0, 2, 151], TYOP [0, 3, 141],
   TYOP [0, 13, 41], TYOP [0, 154, 41], TYOP [0, 40, 155],
   TYOP [0, 13, 156], TYOP [0, 2, 43], TYOP [0, 98, 2], TYOP [0, 2, 159],
   TYOP [0, 2, 101], TYOP [0, 161, 53], TYOP [0, 43, 59],
   TYOP [0, 48, 163], TYOP [0, 53, 53], TYOP [0, 19, 165], TYOP [0, 7, 7],
   TYOP [0, 139, 167], TYOP [0, 88, 53], TYOP [0, 9, 2],
   TYOP [0, 170, 169], TYOP [0, 1, 58], TYOP [0, 2, 61], TYOP [0, 6, 87],
   TYOP [0, 9, 89], TYOP [0, 3, 81], TYOP [0, 88, 61], TYOP [0, 170, 177],
   TYOP [0, 43, 43], TYOP [0, 1, 179], TYOP [0, 6, 167], TYOP [0, 24, 29],
   TYOP [0, 6, 1], TYOP [0, 6, 13], TYOP [0, 9, 13], TYOP [0, 10, 13],
   TYOP [0, 6, 43], TYOP [0, 9, 53], TYOP [0, 10, 24], TYOP [0, 42, 135],
   TYOP [0, 43, 179], TYOP [0, 53, 165], TYOP [0, 38, 38],
   TYOP [0, 193, 38], TYOP [0, 47, 194], TYOP [0, 12, 12],
   TYOP [0, 196, 12], TYOP [0, 47, 197], TYOP [0, 0, 13], TYOP [0, 2, 13],
   TYOP [0, 199, 200], TYOP [0, 16, 201], TYOP [0, 10, 2],
   TYOP [0, 3, 203], TYOP [0, 204, 2], TYOP [0, 2, 205], TYOP [0, 10, 206],
   TYOP [0, 10, 9], TYOP [0, 3, 208], TYOP [0, 209, 9], TYOP [0, 9, 210],
   TYOP [0, 10, 211], TYOP [0, 19, 19], TYOP [0, 19, 213],
   TYOP [0, 29, 29], TYOP [0, 29, 215], TYOP [0, 51, 51],
   TYOP [0, 18, 217], TYOP [0, 18, 18], TYOP [0, 18, 219],
   TYOP [0, 2, 203], TYOP [0, 221, 2], TYOP [0, 11, 222], TYOP [0, 2, 208],
   TYOP [0, 224, 9], TYOP [0, 11, 225]]
  end
  val _ = Theory.incorporate_consts "FM_plan" tyvector
     [("state_succ", 5), ("state_set", 8), ("state_list", 12),
      ("problem_size", 17), ("problem_I_fupd", 20), ("problem_I", 21),
      ("problem_G_fupd", 20), ("problem_G", 21), ("problem_CASE", 28),
      ("problem_A_fupd", 30), ("problem_A", 31), ("problem", 34),
      ("planning_problem", 35), ("plan", 37), ("exec_plan", 38)];

  local open SharingTables
  in
  val tmvector = build_term_vector idvector tyvector
  [TMV("'problem'", 42), TMV("A", 24), TMV("G", 2), TMV("I", 2),
   TMV("I'", 2), TMV("M", 14), TMV("M'", 14), TMV("P", 43), TMV("P", 35),
   TMV("P", 45), TMV("P", 46), TMV("PROB", 14), TMV("R", 47), TMV("X", 43),
   TMV("X", 6), TMV("a", 3), TMV("a'", 11), TMV("a0", 2), TMV("a0'", 2),
   TMV("a0'", 41), TMV("a1", 24), TMV("a1'", 24), TMV("a2", 2),
   TMV("a2'", 2), TMV("as", 10), TMV("as'", 10), TMV("as1", 10),
   TMV("as2", 10), TMV("as3", 10), TMV("as_a", 10), TMV("as_b", 10),
   TMV("e", 1), TMV("e", 6), TMV("exec_plan", 38), TMV("f", 2),
   TMV("f", 48), TMV("f", 16), TMV("f", 49), TMV("f", 19), TMV("f", 26),
   TMV("f", 29), TMV("f'", 26), TMV("f0", 24), TMV("f01", 24),
   TMV("f02", 24), TMV("f1", 2), TMV("f11", 2), TMV("f12", 2),
   TMV("f2", 2), TMV("f2", 19), TMV("f2", 29), TMV("fn", 50), TMV("g", 19),
   TMV("g", 29), TMV("h", 1), TMV("h", 2), TMV("h", 51), TMV("h", 3),
   TMV("k", 1), TMV("l", 6), TMV("l", 13), TMV("l1", 6), TMV("l2", 6),
   TMV("l3", 6), TMV("n", 13), TMV("p", 1), TMV("p", 22), TMV("p", 14),
   TMV("p'", 1), TMV("p'", 22), TMV("p1", 14), TMV("p2", 14),
   TMV("pp", 14), TMV("prob", 1), TMV("problem", 52), TMV("record", 56),
   TMV("rep", 57), TMV("s", 1), TMV("s", 2), TMV("s", 43), TMV("s", 6),
   TMV("s0", 2), TMV("s1", 6), TMV("s2", 6), TMV("seq", 6), TMV("sl", 6),
   TMV("slist", 9), TMV("slist_1", 9), TMV("slist_2", 9), TMV("ss", 6),
   TMV("state_list", 12), TMV("t", 43), TMV("t", 6), TMV("t", 10),
   TMV("v", 0), TMV("v", 2), TMV("v1", 10), TMV("x", 1), TMV("x", 6),
   TMV("x", 9), TMV("x1", 6), TMV("x2", 6), TMV("y", 1), TMV("y", 6),
   TMV("y", 9), TMC(9, 58), TMC(9, 60), TMC(9, 61), TMC(9, 63), TMC(9, 64),
   TMC(9, 66), TMC(9, 68), TMC(9, 70), TMC(9, 72), TMC(9, 74), TMC(9, 76),
   TMC(9, 78), TMC(9, 80), TMC(9, 82), TMC(9, 84), TMC(9, 86), TMC(9, 87),
   TMC(9, 89), TMC(9, 91), TMC(9, 93), TMC(9, 77), TMC(9, 81), TMC(9, 85),
   TMC(10, 95), TMC(11, 97), TMC(11, 100), TMC(11, 103), TMC(11, 105),
   TMC(11, 107), TMC(11, 109), TMC(11, 111), TMC(12, 113), TMC(13, 13),
   TMC(14, 114), TMC(15, 114), TMC(16, 115), TMC(16, 116), TMC(16, 113),
   TMC(16, 117), TMC(16, 118), TMC(16, 119), TMC(16, 120), TMC(16, 121),
   TMC(16, 123), TMC(16, 124), TMC(16, 126), TMC(16, 128), TMC(16, 8),
   TMC(16, 129), TMC(16, 130), TMC(16, 114), TMC(16, 131), TMC(16, 132),
   TMC(17, 113), TMC(18, 114), TMC(19, 114), TMC(20, 58), TMC(20, 60),
   TMC(20, 61), TMC(20, 134), TMC(20, 136), TMC(20, 82), TMC(20, 89),
   TMC(20, 91), TMC(20, 77), TMC(21, 138), TMC(22, 140), TMC(22, 142),
   TMC(23, 14), TMC(24, 94), TMC(25, 94), TMC(26, 41), TMC(27, 143),
   TMC(27, 144), TMC(27, 145), TMC(27, 146), TMC(27, 147), TMC(28, 149),
   TMC(29, 150), TMC(29, 152), TMC(29, 153), TMC(30, 157), TMC(31, 112),
   TMC(32, 118), TMC(33, 7), TMC(34, 95), TMC(35, 0), TMC(36, 158),
   TMC(37, 58), TMC(37, 61), TMC(37, 87), TMC(38, 139), TMC(39, 4),
   TMC(40, 148), TMC(41, 160), TMC(42, 162), TMC(43, 19), TMC(43, 151),
   TMC(44, 164), TMC(44, 166), TMC(44, 168), TMC(44, 171), TMC(45, 172),
   TMC(45, 173), TMC(45, 174), TMC(45, 175), TMC(45, 176), TMC(46, 178),
   TMC(47, 180), TMC(47, 181), TMC(48, 8), TMC(49, 148), TMC(49, 182),
   TMC(50, 183), TMC(50, 170), TMC(51, 184), TMC(51, 185), TMC(51, 186),
   TMC(52, 187), TMC(52, 188), TMC(52, 189), TMC(53, 6), TMC(53, 9),
   TMC(53, 10), TMC(54, 94), TMC(55, 4), TMC(56, 117), TMC(57, 118),
   TMC(57, 120), TMC(57, 124), TMC(58, 94), TMC(59, 0), TMC(60, 190),
   TMC(61, 191), TMC(61, 192), TMC(62, 137), TMC(63, 195), TMC(63, 198),
   TMC(64, 13), TMC(65, 199), TMC(66, 38), TMC(67, 202), TMC(68, 8),
   TMC(68, 130), TMC(69, 207), TMC(69, 212), TMC(70, 214), TMC(70, 216),
   TMC(70, 218), TMC(70, 220), TMC(71, 223), TMC(71, 226), TMC(72, 37),
   TMC(73, 35), TMC(6, 34), TMC(74, 31), TMC(75, 30), TMC(76, 28),
   TMC(77, 21), TMC(78, 20), TMC(79, 21), TMC(80, 20), TMC(81, 17),
   TMC(82, 12), TMC(83, 8), TMC(83, 129), TMC(84, 5), TMC(85, 130),
   TMC(86, 112)]
  end
  local
  val DT = Thm.disk_thm val read = Term.read_raw tmvector
  in
  val op problem_TY_DEF =
    DT(["DISK_THM"],
       [read"(%165 (|%76. ((%237 (|%19. (%120 (|%0. ((%158 (%127 (|%19. ((%158 (%163 (|%17. (%166 (|%20. (%163 (|%22. ((%157 $3) ((((|%17. (|%20. (|%22. (((%186 %137) ((%133 $2) ((%134 $1) $0))) (|%64. %176))))) $2) $1) $0))))))))) ($1 $0))))) ($0 $1)))))) $0)))"])
  val op problem_case_def =
    DT(["DISK_THM"],
       [read"(%107 (|%17. (%118 (|%20. (%107 (|%22. (%114 (|%39. ((%141 ((%262 (((%259 $3) $2) $1)) $0)) ((($0 $3) $2) $1))))))))))"])
  val op problem_size_def =
    DT(["DISK_THM"],
       [read"(%110 (|%36. (%107 (|%17. (%118 (|%20. (%107 (|%22. ((%155 ((%267 $3) (((%259 $2) $1) $0))) ((%128 (%229 (%174 %243))) ((%128 (((%246 (|%58. %137)) (|%94. ((%128 (%229 (%174 %243))) (%244 $0)))) $2)) (((%246 (|%58. %137)) (|%94. ((%128 (%229 (%174 %243))) (%244 $0)))) $0))))))))))))"])
  val op problem_I =
    DT(["DISK_THM"],
       [read"(%107 (|%34. (%118 (|%42. (%107 (|%45. ((%143 (%265 (((%259 $2) $1) $0))) $2)))))))"])
  val op problem_A =
    DT(["DISK_THM"],
       [read"(%107 (|%34. (%118 (|%42. (%107 (|%45. ((%149 (%260 (((%259 $2) $1) $0))) $1)))))))"])
  val op problem_G =
    DT(["DISK_THM"],
       [read"(%107 (|%34. (%118 (|%42. (%107 (|%45. ((%143 (%263 (((%259 $2) $1) $0))) $0)))))))"])
  val op problem_I_fupd =
    DT(["DISK_THM"],
       [read"(%113 (|%49. (%107 (|%34. (%118 (|%42. (%107 (|%45. ((%156 ((%266 $3) (((%259 $2) $1) $0))) (((%259 ($3 $2)) $1) $0))))))))))"])
  val op problem_A_fupd =
    DT(["DISK_THM"],
       [read"(%115 (|%50. (%107 (|%34. (%118 (|%42. (%107 (|%45. ((%156 ((%261 $3) (((%259 $2) $1) $0))) (((%259 $2) ($3 $1)) $0))))))))))"])
  val op problem_G_fupd =
    DT(["DISK_THM"],
       [read"(%113 (|%49. (%107 (|%34. (%118 (|%42. (%107 (|%45. ((%156 ((%264 $3) (((%259 $2) $1) $0))) (((%259 $2) $1) ($3 $0)))))))))))"])
  val op planning_problem_def =
    DT([],
       [read"(%125 (|%11. ((%142 (%258 $0)) ((%136 (%126 (|%15. ((%158 ((%211 $0) (%260 $1))) ((%136 ((%232 (%192 (%230 $0))) (%192 (%265 $1)))) ((%232 (%192 (%197 $0))) (%192 (%265 $1)))))))) ((%144 (%192 (%263 $0))) (%192 (%265 $0)))))))"])
  val op state_succ_def =
    DT([],
       [read"(%107 (|%78. (%126 (|%15. ((%143 ((%271 $1) $0)) (((%182 ((%231 (%197 $0)) $1)) ((%198 (%230 $0)) $1)) $1))))))"])
  val op exec_plan_primitive_def =
    DT([],
       [read"((%150 %245) ((%241 (%170 (|%12. ((%136 (%240 $0)) (%123 (|%24. (%126 (|%15. (%107 (|%78. (($3 ((%132 ((%271 $0) $1)) $2)) ((%132 $0) ((%185 $1) $2))))))))))))) (|%33. (|%16. ((%255 $0) (|%78. (|%96. (((%249 $0) (%201 $1)) (|%15. (|%24. (%201 ($5 ((%132 ((%271 $3) $1)) $0)))))))))))))"])
  val op plan_def =
    DT(["DISK_THM"],
       [read"(%125 (|%11. (%123 (|%24. ((%142 (%257 ((%135 $1) $0))) ((%136 ((%136 (%258 $1)) ((%143 (%245 ((%132 (%265 $1)) $0))) (%263 $1)))) ((%234 (%225 $0)) (%260 $1))))))))"])
  val op state_list_primitive_def =
    DT([],
       [read"((%151 %268) ((%242 (%170 (|%12. ((%136 (%240 $0)) (%123 (|%24. (%126 (|%15. (%107 (|%78. (($3 ((%132 ((%271 $0) $1)) $2)) ((%132 $0) ((%185 $1) $2))))))))))))) (|%90. (|%16. ((%256 $0) (|%78. (|%96. (((%250 $0) (%202 %227)) (|%15. (|%24. (%202 ((%184 $3) ($5 ((%132 ((%271 $3) $1)) $0))))))))))))))"])
  val op state_set_def =
    DT(["DISK_THM"],
       [read"((%136 (%105 (|%77. (%121 (|%89. ((%147 (%269 ((%183 $1) $0))) ((%214 ((%183 $1) %226)) ((%205 (%183 $1)) (%269 $0))))))))) ((%147 (%269 %226)) %189))"])
  val op problem_accessors =
    DT(["DISK_THM"],
       [read"((%136 (%107 (|%34. (%118 (|%42. (%107 (|%45. ((%143 (%265 (((%259 $2) $1) $0))) $2)))))))) ((%136 (%107 (|%34. (%118 (|%42. (%107 (|%45. ((%149 (%260 (((%259 $2) $1) $0))) $1)))))))) (%107 (|%34. (%118 (|%42. (%107 (|%45. ((%143 (%263 (((%259 $2) $1) $0))) $0)))))))))"])
  val op problem_fn_updates =
    DT(["DISK_THM"],
       [read"((%136 (%113 (|%49. (%107 (|%34. (%118 (|%42. (%107 (|%45. ((%156 ((%266 $3) (((%259 $2) $1) $0))) (((%259 ($3 $2)) $1) $0))))))))))) ((%136 (%115 (|%50. (%107 (|%34. (%118 (|%42. (%107 (|%45. ((%156 ((%261 $3) (((%259 $2) $1) $0))) (((%259 $2) ($3 $1)) $0))))))))))) (%113 (|%49. (%107 (|%34. (%118 (|%42. (%107 (|%45. ((%156 ((%264 $3) (((%259 $2) $1) $0))) (((%259 $2) $1) ($3 $0)))))))))))))"])
  val op problem_accfupds =
    DT(["DISK_THM"],
       [read"((%136 (%125 (|%67. (%115 (|%40. ((%143 (%265 ((%261 $0) $1))) (%265 $1))))))) ((%136 (%125 (|%67. (%113 (|%38. ((%143 (%265 ((%264 $0) $1))) (%265 $1))))))) ((%136 (%125 (|%67. (%113 (|%38. ((%149 (%260 ((%266 $0) $1))) (%260 $1))))))) ((%136 (%125 (|%67. (%113 (|%38. ((%149 (%260 ((%264 $0) $1))) (%260 $1))))))) ((%136 (%125 (|%67. (%113 (|%38. ((%143 (%263 ((%266 $0) $1))) (%263 $1))))))) ((%136 (%125 (|%67. (%115 (|%40. ((%143 (%263 ((%261 $0) $1))) (%263 $1))))))) ((%136 (%125 (|%67. (%113 (|%38. ((%143 (%265 ((%266 $0) $1))) ($0 (%265 $1)))))))) ((%136 (%125 (|%67. (%115 (|%40. ((%149 (%260 ((%261 $0) $1))) ($0 (%260 $1)))))))) (%125 (|%67. (%113 (|%38. ((%143 (%263 ((%264 $0) $1))) ($0 (%263 $1)))))))))))))))"])
  val op problem_fupdfupds =
    DT(["DISK_THM"],
       [read"((%136 (%125 (|%67. (%113 (|%52. (%113 (|%38. ((%156 ((%266 $0) ((%266 $1) $2))) ((%266 ((%251 $0) $1)) $2))))))))) ((%136 (%125 (|%67. (%115 (|%53. (%115 (|%40. ((%156 ((%261 $0) ((%261 $1) $2))) ((%261 ((%252 $0) $1)) $2))))))))) (%125 (|%67. (%113 (|%52. (%113 (|%38. ((%156 ((%264 $0) ((%264 $1) $2))) ((%264 ((%251 $0) $1)) $2))))))))))"])
  val op problem_fupdfupds_comp =
    DT(["DISK_THM"],
       [read"((%136 ((%136 (%113 (|%52. (%113 (|%38. ((%148 ((%254 (%266 $0)) (%266 $1))) (%266 ((%251 $0) $1)))))))) (%112 (|%56. (%113 (|%52. (%113 (|%38. ((%145 ((%253 (%266 $0)) ((%253 (%266 $1)) $2))) ((%253 (%266 ((%251 $0) $1))) $2)))))))))) ((%136 ((%136 (%115 (|%53. (%115 (|%40. ((%148 ((%254 (%261 $0)) (%261 $1))) (%261 ((%252 $0) $1)))))))) (%112 (|%56. (%115 (|%53. (%115 (|%40. ((%145 ((%253 (%261 $0)) ((%253 (%261 $1)) $2))) ((%253 (%261 ((%252 $0) $1))) $2)))))))))) ((%136 (%113 (|%52. (%113 (|%38. ((%148 ((%254 (%264 $0)) (%264 $1))) (%264 ((%251 $0) $1)))))))) (%112 (|%56. (%113 (|%52. (%113 (|%38. ((%145 ((%253 (%264 $0)) ((%253 (%264 $1)) $2))) ((%253 (%264 ((%251 $0) $1))) $2)))))))))))"])
  val op problem_fupdcanon =
    DT(["DISK_THM"],
       [read"((%136 (%125 (|%67. (%113 (|%52. (%115 (|%40. ((%156 ((%261 $0) ((%266 $1) $2))) ((%266 $1) ((%261 $0) $2)))))))))) ((%136 (%125 (|%67. (%113 (|%52. (%113 (|%38. ((%156 ((%264 $0) ((%266 $1) $2))) ((%266 $1) ((%264 $0) $2)))))))))) (%125 (|%67. (%115 (|%53. (%113 (|%38. ((%156 ((%264 $0) ((%261 $1) $2))) ((%261 $1) ((%264 $0) $2)))))))))))"])
  val op problem_fupdcanon_comp =
    DT(["DISK_THM"],
       [read"((%136 ((%136 (%113 (|%52. (%115 (|%40. ((%148 ((%254 (%261 $0)) (%266 $1))) ((%254 (%266 $1)) (%261 $0)))))))) (%112 (|%56. (%113 (|%52. (%115 (|%40. ((%145 ((%253 (%261 $0)) ((%253 (%266 $1)) $2))) ((%253 (%266 $1)) ((%253 (%261 $0)) $2))))))))))) ((%136 ((%136 (%113 (|%52. (%113 (|%38. ((%148 ((%254 (%264 $0)) (%266 $1))) ((%254 (%266 $1)) (%264 $0)))))))) (%112 (|%56. (%113 (|%52. (%113 (|%38. ((%145 ((%253 (%264 $0)) ((%253 (%266 $1)) $2))) ((%253 (%266 $1)) ((%253 (%264 $0)) $2))))))))))) ((%136 (%115 (|%53. (%113 (|%38. ((%148 ((%254 (%264 $0)) (%261 $1))) ((%254 (%261 $1)) (%264 $0)))))))) (%112 (|%56. (%115 (|%53. (%113 (|%38. ((%145 ((%253 (%264 $0)) ((%253 (%261 $1)) $2))) ((%253 (%261 $1)) ((%253 (%264 $0)) $2))))))))))))"])
  val op problem_component_equality =
    DT(["DISK_THM"],
       [read"(%125 (|%70. (%125 (|%71. ((%142 ((%156 $1) $0)) ((%136 ((%143 (%265 $1)) (%265 $0))) ((%136 ((%149 (%260 $1)) (%260 $0))) ((%143 (%263 $1)) (%263 $0)))))))))"])
  val op problem_updates_eq_literal =
    DT(["DISK_THM"],
       [read"(%125 (|%67. (%107 (|%45. (%118 (|%42. (%107 (|%34. ((%156 ((%266 (%216 $2)) ((%261 (%217 $1)) ((%264 (%216 $0)) $3)))) ((%266 (%216 $2)) ((%261 (%217 $1)) ((%264 (%216 $0)) %173))))))))))))"])
  val op problem_literal_nchotomy =
    DT(["DISK_THM"],
       [read"(%125 (|%67. (%163 (|%45. (%166 (|%42. (%163 (|%34. ((%156 $3) ((%266 (%216 $2)) ((%261 (%217 $1)) ((%264 (%216 $0)) %173))))))))))))"])
  val op FORALL_problem =
    DT(["DISK_THM"],
       [read"(%116 (|%8. ((%142 (%125 (|%67. ($1 $0)))) (%107 (|%45. (%118 (|%42. (%107 (|%34. ($3 ((%266 (%216 $2)) ((%261 (%217 $1)) ((%264 (%216 $0)) %173)))))))))))))"])
  val op EXISTS_problem =
    DT(["DISK_THM"],
       [read"(%116 (|%8. ((%142 (%169 (|%67. ($1 $0)))) (%163 (|%45. (%166 (|%42. (%163 (|%34. ($3 ((%266 (%216 $2)) ((%261 (%217 $1)) ((%264 (%216 $0)) %173)))))))))))))"])
  val op problem_literal_11 =
    DT(["DISK_THM"],
       [read"(%107 (|%46. (%118 (|%43. (%107 (|%45. (%107 (|%47. (%118 (|%44. (%107 (|%48. ((%142 ((%156 ((%266 (%216 $5)) ((%261 (%217 $4)) ((%264 (%216 $3)) %173)))) ((%266 (%216 $2)) ((%261 (%217 $1)) ((%264 (%216 $0)) %173))))) ((%136 ((%143 $5) $2)) ((%136 ((%149 $4) $1)) ((%143 $3) $0))))))))))))))))"])
  val op datatype_problem =
    DT(["DISK_THM"], [read"(%187 ((((%75 %74) %3) %1) %2))"])
  val op problem_11 =
    DT(["DISK_THM"],
       [read"(%107 (|%17. (%118 (|%20. (%107 (|%22. (%107 (|%18. (%118 (|%21. (%107 (|%23. ((%142 ((%156 (((%259 $5) $4) $3)) (((%259 $2) $1) $0))) ((%136 ((%143 $5) $2)) ((%136 ((%149 $4) $1)) ((%143 $3) $0))))))))))))))))"])
  val op problem_case_cong =
    DT(["DISK_THM"],
       [read"(%125 (|%5. (%125 (|%6. (%114 (|%39. ((%158 ((%136 ((%156 $2) $1)) (%107 (|%17. (%118 (|%20. (%107 (|%22. ((%158 ((%156 $4) (((%259 $2) $1) $0))) ((%141 ((($3 $2) $1) $0)) (((%41 $2) $1) $0))))))))))) ((%141 ((%262 $2) $0)) ((%262 $1) %41)))))))))"])
  val op problem_nchotomy =
    DT(["DISK_THM"],
       [read"(%125 (|%72. (%163 (|%34. (%166 (|%42. (%163 (|%45. ((%156 $3) (((%259 $2) $1) $0))))))))))"])
  val op problem_Axiom =
    DT(["DISK_THM"],
       [read"(%114 (|%39. (%164 (|%51. (%107 (|%17. (%118 (|%20. (%107 (|%22. ((%141 ($3 (((%259 $2) $1) $0))) ((($4 $2) $1) $0))))))))))))"])
  val op problem_induction =
    DT(["DISK_THM"],
       [read"(%116 (|%8. ((%158 (%107 (|%34. (%118 (|%42. (%107 (|%45. ($3 (((%259 $2) $1) $0))))))))) (%125 (|%67. ($1 $0))))))"])
  val op exec_plan_ind =
    DT(["DISK_THM"],
       [read"(%119 (|%10. ((%158 ((%136 (%107 (|%78. (%126 (|%15. (%123 (|%24. ((%158 ($3 ((%132 ((%271 $2) $1)) $0))) ($3 ((%132 $2) ((%185 $1) $0))))))))))) (%107 (|%78. ($1 ((%132 $0) %228)))))) (%107 (|%95. (%123 (|%96. ($2 ((%132 $1) $0)))))))))"])
  val op exec_plan_def =
    DT(["DISK_THM"],
       [read"((%136 (%107 (|%78. (%123 (|%24. (%126 (|%15. ((%143 (%245 ((%132 $2) ((%185 $0) $1)))) (%245 ((%132 ((%271 $2) $0)) $1)))))))))) (%107 (|%78. ((%143 (%245 ((%132 $0) %228))) $0))))"])
  val op exec_plan_Append =
    DT(["DISK_THM"],
       [read"(%123 (|%29. (%123 (|%30. (%107 (|%78. ((%143 (%245 ((%132 $0) ((%172 $2) $1)))) (%245 ((%132 (%245 ((%132 $0) $2))) $1)))))))))"])
  val op cycle_removal_lemma =
    DT(["DISK_THM"],
       [read"(%125 (|%11. (%123 (|%26. (%123 (|%27. (%123 (|%28. ((%158 ((%136 (%257 ((%135 $3) ((%172 ((%172 $2) $1)) $0)))) ((%136 ((%143 (%245 ((%132 (%265 $3)) ((%172 $2) $1)))) (%245 ((%132 (%265 $3)) $2)))) (%273 ((%154 $1) %228))))) (%257 ((%135 $3) ((%172 $2) $0))))))))))))"])
  val op general_theorem =
    DT(["DISK_THM"],
       [read"(%109 (|%7. (%110 (|%36. (%124 (|%60. ((%158 (%105 (|%65. ((%158 ((%136 ($3 $0)) ((%159 ($2 $0)) $1))) (%161 (|%68. ((%136 ($4 $0)) ((%138 ($3 $0)) ($3 $1))))))))) (%105 (|%65. ((%158 ($3 $0)) (%161 (|%68. ((%136 ($4 $0)) ((%139 ($3 $0)) $2))))))))))))))"])
  val op general_theorem' =
    DT(["DISK_THM"],
       [read"(%117 (|%9. (%111 (|%37. (%124 (|%60. (%105 (|%73. ((%158 (%106 (|%66. ((%158 ((%136 ($4 ((%129 $1) $0))) ((%159 ($3 $0)) $2))) (%162 (|%69. ((%136 ($5 ((%129 $2) $0))) ((%138 ($4 $0)) ($4 $1))))))))) (%106 (|%66. ((%158 ($4 ((%129 $1) $0))) (%162 (|%69. ((%136 ($5 ((%129 $2) $0))) ((%139 ($4 $0)) $3))))))))))))))))"])
  val op construction_of_all_possible_states_lemma =
    DT(["DISK_THM"],
       [read"(%105 (|%31. (%109 (|%13. ((%158 (%273 ((%207 $1) $0))) ((%146 (%200 (|%78. ((%131 $0) ((%144 (%192 $0)) ((%213 $2) $1)))))) ((%239 ((%204 (|%78. ((%199 $0) ((%130 $2) %236)))) (%200 (|%78. ((%131 $0) ((%144 (%192 $0)) $1)))))) ((%204 (|%78. ((%199 $0) ((%130 $2) %191)))) (%200 (|%78. ((%131 $0) ((%144 (%192 $0)) $1))))))))))))"])
  val op card_union' =
    DT(["DISK_THM"],
       [read"((%158 ((%136 (%193 %79)) ((%136 (%193 %91)) ((%188 %79) %91)))) ((%155 (%177 ((%238 %79) %91))) ((%128 (%177 %79)) (%177 %91))))"])
  val op FINITE_states =
    DT(["DISK_THM"],
       [read"(%109 (|%13. ((%158 (%193 $0)) (%194 (%200 (|%78. ((%131 $0) ((%144 (%192 $0)) $1))))))))"])
  val op CARD_INJ_IMAGE_2 =
    DT(["DISK_THM"],
       [read"(%108 (|%35. (%109 (|%79. ((%158 (%193 $0)) ((%158 (%105 (|%97. (%105 (|%102. ((%158 ((%136 ((%207 $1) $2)) ((%207 $0) $2))) ((%142 ((%141 ($3 $1)) ($3 $0))) ((%140 $1) $0)))))))) ((%155 (%178 ((%203 $1) $0))) (%177 $0))))))))"])
  val op card_of_set_of_all_possible_states =
    DT(["DISK_THM"],
       [read"(%109 (|%13. ((%158 (%193 $0)) ((%155 (%179 (%200 (|%78. ((%131 $0) ((%144 (%192 $0)) $1)))))) ((%190 (%229 (%175 %243))) (%177 $0))))))"])
  val op state_list_ind =
    DT(["DISK_THM"],
       [read"(%119 (|%10. ((%158 ((%136 (%107 (|%78. (%126 (|%15. (%123 (|%24. ((%158 ($3 ((%132 ((%271 $2) $1)) $0))) ($3 ((%132 $2) ((%185 $1) $0))))))))))) (%107 (|%78. ($1 ((%132 $0) %228)))))) (%107 (|%95. (%123 (|%96. ($2 ((%132 $1) $0)))))))))"])
  val op state_list_def =
    DT(["DISK_THM"],
       [read"((%136 (%107 (|%78. (%123 (|%24. (%126 (|%15. ((%153 (%268 ((%132 $2) ((%185 $0) $1)))) ((%184 $2) (%268 ((%132 ((%271 $2) $0)) $1))))))))))) (%107 (|%78. ((%153 (%268 ((%132 $0) %228))) %227))))"])
  val op empty_state_list_lemma =
    DT(["DISK_THM"],
       [read"(%123 (|%24. (%107 (|%78. ((%142 ((%153 %227) (%268 ((%132 $0) $1)))) ((%154 $1) %228))))))"])
  val op state_list_length_lemma =
    DT(["DISK_THM"],
       [read"(%123 (|%24. (%107 (|%78. ((%155 (%222 $1)) (%221 (%268 ((%132 $0) $1))))))))"])
  val op state_set_thm =
    DT(["DISK_THM"],
       [read"(%121 (|%82. ((%142 ((%209 $0) (%269 %83))) ((%136 ((%247 $0) %83)) (%273 ((%152 $0) %226))))))"])
  val op state_set_finite =
    DT(["DISK_THM"], [read"(%121 (|%14. (%195 (%269 $0))))"])
  val op LENGTH_state_set =
    DT(["DISK_THM"],
       [read"(%121 (|%14. (%121 (|%32. ((%158 ((%209 $0) (%269 $1))) ((%139 (%220 $0)) (%220 $1)))))))"])
  val op lemma_temp =
    DT(["DISK_THM"],
       [read"(%122 (|%99. (%125 (|%11. (%123 (|%24. (%107 (|%55. ((%158 (%257 ((%135 $2) $1))) ((%158 ((%210 $3) (%270 (%268 ((%132 (%265 $2)) $1))))) ((%159 (%221 ((%184 $0) (%268 ((%132 (%265 $2)) $1))))) (%221 $3))))))))))))"])
  val op NIL_NOTIN_stateset =
    DT(["DISK_THM"], [read"(%121 (|%14. (%273 ((%209 %226) (%269 $0)))))"])
  val op state_set_card =
    DT(["DISK_THM"],
       [read"(%121 (|%14. ((%155 (%180 (%269 $0))) (%220 $0))))"])
  val op FDOM_state_succ =
    DT(["DISK_THM"],
       [read"((%158 ((%232 (%192 (%230 %15))) (%192 %78))) ((%144 (%192 ((%271 %78) %15))) (%192 %78)))"])
  val op lemma_1_1_1 =
    DT(["DISK_THM"],
       [read"(%125 (|%11. ((%158 ((%136 (%258 $0)) ((%144 (%192 %4)) (%192 (%265 $0))))) (%258 ((%266 (%216 %4)) $0)))))"])
  val op lemma_1_1 =
    DT(["DISK_THM"],
       [read"(%125 (|%11. (%123 (|%24. (%126 (|%57. ((%158 (%257 ((%135 $2) ((%185 $0) $1)))) (%257 ((%135 ((%266 (%216 ((%271 (%265 $2)) $0))) $2)) $1)))))))))"])
  val op plan_CONS =
    DT(["DISK_THM"],
       [read"((%142 (%257 ((%135 %11) ((%185 %57) %24)))) ((%136 (%257 ((%135 ((%266 (%216 ((%271 (%265 %11)) %57))) %11)) %24))) ((%136 ((%211 %57) (%260 %11))) (%258 %11))))"])
  val op IS_SUFFIX_MEM =
    DT(["DISK_THM"],
       [read"((%158 ((%215 %80) ((%183 %54) %92))) ((%207 %54) (%223 %80)))"])
  val op IS_PREFIX_MEM =
    DT(["DISK_THM"],
       [read"(%121 (|%103. ((%158 ((%247 %98) $0)) (%105 (|%31. ((%158 ((%207 $0) (%223 %98))) ((%207 $0) (%223 $1))))))))"])
  val op MEM_LAST' =
    DT(["DISK_THM"],
       [read"((%158 (%273 ((%152 %84) %226))) ((%207 (%218 %84)) (%223 %84)))"])
  val op MEM_statelist_FDOM =
    DT(["DISK_THM"],
       [read"(%125 (|%11. (%107 (|%55. (%123 (|%24. (%107 (|%81. ((%158 ((%136 (%257 ((%135 $3) $1))) ((%136 ((%144 (%192 $0)) (%192 (%265 $3)))) ((%208 $2) (%224 (%268 ((%132 $0) $1))))))) ((%144 (%192 $2)) (%192 (%265 $3))))))))))))"])
  val op lemma_1 =
    DT(["DISK_THM"],
       [read"(%123 (|%24. (%125 (|%11. ((%158 (%257 ((%135 $0) $1))) ((%233 ((%206 %219) (%270 (%268 ((%132 (%265 $0)) $1))))) (%200 (|%78. ((%131 $0) ((%144 (%192 $0)) (%192 (%265 $1))))))))))))"])
  val op lemma_2_1_1_1 =
    DT(["DISK_THM"],
       [read"(%123 (|%24. (%122 (|%99. (%125 (|%11. ((%158 ((%136 (%273 ((%154 $2) %228))) (%257 ((%135 $0) $2)))) ((%158 ((%210 $1) (%270 (%268 ((%132 (%265 $0)) $2))))) ((%139 (%221 $1)) (%222 $2))))))))))"])
  val op lemma_2_1_1_2 =
    DT(["DISK_THM"],
       [read"(%121 (|%61. (%121 (|%62. ((%158 ((%159 (%220 $1)) (%220 $0))) (%273 ((%152 $1) $0)))))))"])
  val op lemma_2_1_1 =
    DT(["DISK_THM"],
       [read"(%123 (|%24. (%125 (|%11. (%126 (|%57. ((%158 (%257 ((%135 $1) ((%185 $0) $2)))) ((%155 (%181 (%270 (%268 ((%132 (%265 $1)) ((%185 $0) $2)))))) (%235 (%181 (%270 (%268 ((%132 (%265 ((%266 (%216 ((%271 (%265 $1)) $0))) $1))) $2)))))))))))))"])
  val op lemma_2_1 =
    DT(["DISK_THM"],
       [read"(%123 (|%24. (%125 (|%11. ((%158 (%257 ((%135 $0) $1))) ((%155 (%222 $1)) (%181 (%270 (%268 ((%132 (%265 $0)) $1))))))))))"])
  val op LENGTH_INJ_PREFIXES =
    DT(["DISK_THM"],
       [read"(%121 (|%100. (%121 (|%101. ((%158 ((%136 ((%247 $1) %103)) ((%247 $0) %103))) ((%142 ((%155 (%220 $1)) (%220 $0))) ((%152 $1) $0)))))))"])
  val op lemma_2_2_1 =
    DT(["DISK_THM"],
       [read"(%123 (|%24. (%122 (|%99. (%122 (|%104. (%125 (|%11. ((%158 ((%136 (%257 ((%135 $0) $3))) ((%136 ((%210 $2) (%270 (%268 ((%132 (%265 $0)) $3))))) ((%136 ((%210 $1) (%270 (%268 ((%132 (%265 $0)) $3))))) (%273 ((%153 $2) $1)))))) (%273 ((%155 (%221 $2)) (%221 $1))))))))))))"])
  val op lemma_2_2 =
    DT(["DISK_THM"],
       [read"(%123 (|%24. (%125 (|%11. ((%158 (%257 ((%135 $0) $1))) ((%158 (%273 (((%212 %219) (%270 (%268 ((%132 (%265 $0)) $1)))) (%200 (|%78. ((%131 $0) ((%144 (%192 $0)) (%192 (%265 $1))))))))) (%167 (|%87. (%167 (|%88. ((%136 ((%210 $1) (%270 (%268 ((%132 (%265 $2)) $3))))) ((%136 ((%210 $0) (%270 (%268 ((%132 (%265 $2)) $3))))) ((%136 ((%143 (%219 $1)) (%219 $0))) (%273 ((%155 (%221 $1)) (%221 $0))))))))))))))))"])
  val op lemma_2_3_1_1 =
    DT(["DISK_THM"], [read"(%121 (|%85. (%273 ((%209 %226) (%269 $0)))))"])
  val op lemma_2_3_1_2_1 =
    DT(["DISK_THM"],
       [read"(%121 (|%85. ((%158 (%273 ((%152 $0) %226))) ((%209 $0) (%269 $0)))))"])
  val op lemma_2_3_1_3_1 =
    DT(["DISK_THM"],
       [read"(%125 (|%11. (%126 (|%57. (%123 (|%24. ((%158 (%257 ((%135 $2) ((%185 $1) $0)))) ((%143 (%263 $2)) (%263 ((%266 (%216 ((%271 (%265 $2)) $1))) $2))))))))))"])
  val op lemma_2_3_1_4 =
    DT(["DISK_THM"],
       [read"(%121 (|%59. ((%158 (%273 ((%152 $0) %226))) ((%247 (%196 $0)) $0))))"])
  val op lemma_2_3_1_2 =
    DT(["DISK_THM"],
       [read"(%107 (|%78. (%122 (|%86. (%126 (|%57. (%123 (|%93. ((%158 ((%136 (%273 ((%153 $2) %227))) ((%210 ((%184 $3) $2)) (%270 (%268 ((%132 $3) ((%185 $1) $0))))))) ((%210 $2) (%270 (%268 ((%132 ((%271 $3) $1)) $0)))))))))))))"])
  val op lemma_2_3_1_thm =
    DT(["DISK_THM"],
       [read"(%122 (|%86. (%123 (|%24. (%125 (|%11. ((%158 ((%136 (%273 ((%154 $1) %228))) ((%136 (%273 ((%153 $2) %227))) (%257 ((%135 $0) $1))))) ((%158 ((%210 $2) (%270 (%268 ((%132 (%265 $0)) $1))))) (%168 (|%25. ((%136 ((%248 $0) $2)) ((%136 ((%143 (%245 ((%132 (%265 $1)) $0))) (%219 $3))) ((%155 (%221 $3)) (%235 (%222 $0)))))))))))))))"])
  val op lemma_2_3_2_1 =
    DT(["DISK_THM"], [read"(%121 (|%59. ((%160 (%220 $0)) %137)))"])
  val op lemma_2_3_2 =
    DT(["DISK_THM"],
       [read"(%121 (|%59. (%121 (|%61. (%121 (|%62. ((%158 ((%136 ((%159 (%220 $0)) (%220 $1))) ((%136 ((%247 $1) $2)) ((%247 $0) $2)))) ((%247 $1) $0))))))))"])
  val op lemma_2 =
    DT(["DISK_THM"],
       [read"(%125 (|%11. (%123 (|%24. ((%158 (%257 ((%135 $1) $0))) ((%158 ((%159 (%222 $0)) ((%190 (%229 (%175 %243))) (%177 (%192 (%265 $1)))))) (%168 (|%26. (%168 (|%27. (%168 (|%28. ((%136 ((%154 ((%172 ((%172 $2) $1)) $0)) $3)) ((%136 ((%143 (%245 ((%132 (%265 $4)) ((%172 $2) $1)))) (%245 ((%132 (%265 $4)) $2)))) (%273 ((%154 $1) %228))))))))))))))))"])
  val op lemma_3_1 =
    DT(["DISK_THM"],
       [read"(%121 (|%61. (%121 (|%62. (%121 (|%63. ((%158 (%273 ((%152 $1) %226))) ((%138 (%220 ((%171 $2) $0))) (%220 ((%171 ((%171 $2) $1)) $0))))))))))"])
  val op lemma_3 =
    DT(["DISK_THM"],
       [read"(%123 (|%24. (%125 (|%11. ((%158 ((%136 (%257 ((%135 $0) $1))) ((%159 (%222 $1)) ((%190 (%229 (%175 %243))) (%177 (%192 (%265 $0))))))) (%168 (|%25. ((%136 (%257 ((%135 $1) $0))) ((%136 ((%138 (%222 $0)) (%222 $2))) ((%272 $0) $2))))))))))"])
  val op main_lemma =
    DT(["DISK_THM"],
       [read"(%125 (|%11. (%123 (|%24. ((%158 (%257 ((%135 $1) $0))) (%168 (|%25. ((%136 (%257 ((%135 $2) $0))) ((%136 ((%272 $0) $1)) ((%139 (%222 $0)) ((%190 (%229 (%175 %243))) (%177 (%192 (%265 $2))))))))))))))"])
  end
  val _ = DB.bindl "FM_plan"
  [("problem_TY_DEF",problem_TY_DEF,DB.Def),
   ("problem_case_def",problem_case_def,DB.Def),
   ("problem_size_def",problem_size_def,DB.Def),
   ("problem_I",problem_I,DB.Def), ("problem_A",problem_A,DB.Def),
   ("problem_G",problem_G,DB.Def),
   ("problem_I_fupd",problem_I_fupd,DB.Def),
   ("problem_A_fupd",problem_A_fupd,DB.Def),
   ("problem_G_fupd",problem_G_fupd,DB.Def),
   ("planning_problem_def",planning_problem_def,DB.Def),
   ("state_succ_def",state_succ_def,DB.Def),
   ("exec_plan_primitive_def",exec_plan_primitive_def,DB.Def),
   ("plan_def",plan_def,DB.Def),
   ("state_list_primitive_def",state_list_primitive_def,DB.Def),
   ("state_set_def",state_set_def,DB.Def),
   ("problem_accessors",problem_accessors,DB.Thm),
   ("problem_fn_updates",problem_fn_updates,DB.Thm),
   ("problem_accfupds",problem_accfupds,DB.Thm),
   ("problem_fupdfupds",problem_fupdfupds,DB.Thm),
   ("problem_fupdfupds_comp",problem_fupdfupds_comp,DB.Thm),
   ("problem_fupdcanon",problem_fupdcanon,DB.Thm),
   ("problem_fupdcanon_comp",problem_fupdcanon_comp,DB.Thm),
   ("problem_component_equality",problem_component_equality,DB.Thm),
   ("problem_updates_eq_literal",problem_updates_eq_literal,DB.Thm),
   ("problem_literal_nchotomy",problem_literal_nchotomy,DB.Thm),
   ("FORALL_problem",FORALL_problem,DB.Thm),
   ("EXISTS_problem",EXISTS_problem,DB.Thm),
   ("problem_literal_11",problem_literal_11,DB.Thm),
   ("datatype_problem",datatype_problem,DB.Thm),
   ("problem_11",problem_11,DB.Thm),
   ("problem_case_cong",problem_case_cong,DB.Thm),
   ("problem_nchotomy",problem_nchotomy,DB.Thm),
   ("problem_Axiom",problem_Axiom,DB.Thm),
   ("problem_induction",problem_induction,DB.Thm),
   ("exec_plan_ind",exec_plan_ind,DB.Thm),
   ("exec_plan_def",exec_plan_def,DB.Thm),
   ("exec_plan_Append",exec_plan_Append,DB.Thm),
   ("cycle_removal_lemma",cycle_removal_lemma,DB.Thm),
   ("general_theorem",general_theorem,DB.Thm),
   ("general_theorem'",general_theorem',DB.Thm),
   ("construction_of_all_possible_states_lemma",
    construction_of_all_possible_states_lemma,
    DB.Thm), ("card_union'",card_union',DB.Thm),
   ("FINITE_states",FINITE_states,DB.Thm),
   ("CARD_INJ_IMAGE_2",CARD_INJ_IMAGE_2,DB.Thm),
   ("card_of_set_of_all_possible_states",
    card_of_set_of_all_possible_states,
    DB.Thm), ("state_list_ind",state_list_ind,DB.Thm),
   ("state_list_def",state_list_def,DB.Thm),
   ("empty_state_list_lemma",empty_state_list_lemma,DB.Thm),
   ("state_list_length_lemma",state_list_length_lemma,DB.Thm),
   ("state_set_thm",state_set_thm,DB.Thm),
   ("state_set_finite",state_set_finite,DB.Thm),
   ("LENGTH_state_set",LENGTH_state_set,DB.Thm),
   ("lemma_temp",lemma_temp,DB.Thm),
   ("NIL_NOTIN_stateset",NIL_NOTIN_stateset,DB.Thm),
   ("state_set_card",state_set_card,DB.Thm),
   ("FDOM_state_succ",FDOM_state_succ,DB.Thm),
   ("lemma_1_1_1",lemma_1_1_1,DB.Thm), ("lemma_1_1",lemma_1_1,DB.Thm),
   ("plan_CONS",plan_CONS,DB.Thm), ("IS_SUFFIX_MEM",IS_SUFFIX_MEM,DB.Thm),
   ("IS_PREFIX_MEM",IS_PREFIX_MEM,DB.Thm), ("MEM_LAST'",MEM_LAST',DB.Thm),
   ("MEM_statelist_FDOM",MEM_statelist_FDOM,DB.Thm),
   ("lemma_1",lemma_1,DB.Thm), ("lemma_2_1_1_1",lemma_2_1_1_1,DB.Thm),
   ("lemma_2_1_1_2",lemma_2_1_1_2,DB.Thm),
   ("lemma_2_1_1",lemma_2_1_1,DB.Thm), ("lemma_2_1",lemma_2_1,DB.Thm),
   ("LENGTH_INJ_PREFIXES",LENGTH_INJ_PREFIXES,DB.Thm),
   ("lemma_2_2_1",lemma_2_2_1,DB.Thm), ("lemma_2_2",lemma_2_2,DB.Thm),
   ("lemma_2_3_1_1",lemma_2_3_1_1,DB.Thm),
   ("lemma_2_3_1_2_1",lemma_2_3_1_2_1,DB.Thm),
   ("lemma_2_3_1_3_1",lemma_2_3_1_3_1,DB.Thm),
   ("lemma_2_3_1_4",lemma_2_3_1_4,DB.Thm),
   ("lemma_2_3_1_2",lemma_2_3_1_2,DB.Thm),
   ("lemma_2_3_1_thm",lemma_2_3_1_thm,DB.Thm),
   ("lemma_2_3_2_1",lemma_2_3_2_1,DB.Thm),
   ("lemma_2_3_2",lemma_2_3_2,DB.Thm), ("lemma_2",lemma_2,DB.Thm),
   ("lemma_3_1",lemma_3_1,DB.Thm), ("lemma_3",lemma_3,DB.Thm),
   ("main_lemma",main_lemma,DB.Thm)]

  local open Portable GrammarSpecials Parse
    fun UTOFF f = Feedback.trace("Parse.unicode_trace_off_complaints",0)f
  in
  val _ = mk_local_grms [("sublistTheory.sublist_grammars",
                          sublistTheory.sublist_grammars),
                         ("finite_mapTheory.finite_map_grammars",
                          finite_mapTheory.finite_map_grammars)]
  val _ = List.app (update_grms reveal) []
  val _ = update_grms
       temp_type_abbrev
       ("state", T"fmap" "finite_map" [alpha, bool])
  val _ = update_grms temp_add_type "problem"
  val _ = update_grms temp_add_type "problem"




  val _ = update_grms
       (UTOFF temp_overload_on)
       ("problem", (Term.prim_mk_const { Name = "problem", Thy = "FM_plan"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("problem", (Term.prim_mk_const { Name = "problem", Thy = "FM_plan"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("problem_CASE", (Term.prim_mk_const { Name = "problem_CASE", Thy = "FM_plan"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("problem_size", (Term.prim_mk_const { Name = "problem_size", Thy = "FM_plan"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("problem_I", (Term.prim_mk_const { Name = "problem_I", Thy = "FM_plan"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("problem_A", (Term.prim_mk_const { Name = "problem_A", Thy = "FM_plan"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("problem_G", (Term.prim_mk_const { Name = "problem_G", Thy = "FM_plan"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("problem_I_fupd", (Term.prim_mk_const { Name = "problem_I_fupd", Thy = "FM_plan"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("problem_A_fupd", (Term.prim_mk_const { Name = "problem_A_fupd", Thy = "FM_plan"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("problem_G_fupd", (Term.prim_mk_const { Name = "problem_G_fupd", Thy = "FM_plan"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       (" _ record selectI", (Term.prim_mk_const { Name = "problem_I", Thy = "FM_plan"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       (" _ record selectA", (Term.prim_mk_const { Name = "problem_A", Thy = "FM_plan"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       (" _ record selectG", (Term.prim_mk_const { Name = "problem_G", Thy = "FM_plan"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("I_fupd", (Term.prim_mk_const { Name = "problem_I_fupd", Thy = "FM_plan"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("A_fupd", (Term.prim_mk_const { Name = "problem_A_fupd", Thy = "FM_plan"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("G_fupd", (Term.prim_mk_const { Name = "problem_G_fupd", Thy = "FM_plan"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       (" _ record fupdateI", (Term.prim_mk_const { Name = "problem_I_fupd", Thy = "FM_plan"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       (" _ record fupdateA", (Term.prim_mk_const { Name = "problem_A_fupd", Thy = "FM_plan"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       (" _ record fupdateG", (Term.prim_mk_const { Name = "problem_G_fupd", Thy = "FM_plan"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("planning_problem", (Term.prim_mk_const { Name = "planning_problem", Thy = "FM_plan"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("planning_problem", (Term.prim_mk_const { Name = "planning_problem", Thy = "FM_plan"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("state_succ", (Term.prim_mk_const { Name = "state_succ", Thy = "FM_plan"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("state_succ", (Term.prim_mk_const { Name = "state_succ", Thy = "FM_plan"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("exec_plan", (Term.prim_mk_const { Name = "exec_plan", Thy = "FM_plan"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("exec_plan", (Term.prim_mk_const { Name = "exec_plan", Thy = "FM_plan"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("plan", (Term.prim_mk_const { Name = "plan", Thy = "FM_plan"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("plan", (Term.prim_mk_const { Name = "plan", Thy = "FM_plan"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("state_list", (Term.prim_mk_const { Name = "state_list", Thy = "FM_plan"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("state_list", (Term.prim_mk_const { Name = "state_list", Thy = "FM_plan"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("state_set", (Term.prim_mk_const { Name = "state_set", Thy = "FM_plan"}))
  val FM_plan_grammars = Parse.current_lgrms()
  end


  val _ =
    TypeBase.write [
      let
        open TypeBasePure
        val tyinfo0 = mk_datatype_info
          {ax=ORIG problem_Axiom,
           case_def=problem_case_def,
           case_cong=problem_case_cong,
           induction=ORIG problem_induction,
           nchotomy=problem_nchotomy,
           size=SOME(Parse.Term`(FM_plan$problem_size) :('a -> (num$num)) -> ('a FM_plan$problem) -> (num$num)`,
                     ORIG problem_size_def),
           encode = NONE,
           lift=NONE,
           one_one=SOME problem_11,
           distinct=NONE,
           fields=let fun T t s A = mk_thy_type{Thy=t,Tyop=s,Args=A}
    val U = mk_vartype
in
[("I",T"finite_map" "fmap" [alpha, bool]),
 ("A",(T"pair" "prod"
        [T"finite_map" "fmap" [alpha, bool],
         T"finite_map" "fmap" [alpha, bool]] --> bool)),
 ("G",T"finite_map" "fmap" [alpha, bool])] end,
           accessors=Drule.CONJUNCTS problem_accessors,
           updates=Drule.CONJUNCTS problem_fn_updates,
           recognizers=[],
           destructors=[]}
        val tyinfo0 = RecordType.update_tyinfo NONE [problem_accessors, problem_updates_eq_literal, problem_accfupds, problem_fupdfupds, problem_literal_11, problem_fupdfupds_comp, problem_fupdcanon, problem_fupdcanon_comp] tyinfo0
        val () = computeLib.write_datatype_info tyinfo0
      in
        tyinfo0
      end
    ];
  val _ = Theory.LoadableThyData.temp_encoded_update {
    thy = "FM_plan",
    thydataty = "compute",
    data =
        "FM_plan.planning_problem_def FM_plan.state_list_def FM_plan.state_set_def FM_plan.state_succ_def FM_plan.plan_def FM_plan.exec_plan_def"
  }
  val _ = Theory.LoadableThyData.temp_encoded_update {
    thy = "FM_plan",
    thydataty = "BasicProvers.stateful_simpset",
    data =
        "FM_plan.state_set_finite FM_plan.NIL_NOTIN_stateset FM_plan.state_set_card"
  }

val _ = if !Globals.print_thy_loads then print "done\n" else ()
val _ = Theory.load_complete "FM_plan"
end
