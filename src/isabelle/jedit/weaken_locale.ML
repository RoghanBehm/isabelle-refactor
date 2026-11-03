
(* List of (source, target), morphism *)
fun mk_deps thy =
    Locale.dest_dependencies [@{theory Main}] thy
                             |> map (fn {source, target, morphism, ...} => ((source, target), morphism));


(* Locale dep graph edges, source \<sqsupseteq> target *)
fun mk_edges deps = map fst deps;   

fun strip_local nm =
    Long_Name.explode nm
                      |> filter (fn s => s <> "local")
                      |> Long_Name.implode

(* Takes a locale c, returns the list of all locales h where c \<sqsubseteq> h *)
fun above edges c =
    let fun step reached =
            let val next = edges |> map_filter (fn (s,t) =>
                  if member (op =) reached t andalso not (member (op =) reached s)
                  then SOME s else NONE)
            in if null next then reached else step (union (op =) next reached) end
    in step [c] end;

(* Sorted list of locales in theory, ordered by weakness *)
fun mk_cs edges =
    edges |> maps (fn (s,t) => [s,t]) |> distinct (op =)
          |> map (fn c => (c, length (above edges c)))
          |> sort (int_ord o apply2 snd) |> map fst;

(* Work backwards through long name until we find something matching a locale *)
fun locale_prefix thy nm =
    let val parts = Long_Name.explode nm
        fun try i = if i <= 0 then NONE
                    else let val cand = Long_Name.implode (take i parts)
                         in if Locale.defined thy (Locale.intern thy cand)
                            then SOME (Locale.intern thy cand) else try (i-1) end
    in try (length parts - 1) end;

(* If locale_prefix didn't work, our locale might be attached to an _* suffix *)
fun predicate_locale thy nm =
    get_first (fn sfx =>
if String.isSuffix sfx nm then
  let val base = String.substring (nm, 0, size nm - size sfx)
  in if Locale.defined thy base then SOME base else NONE end
else NONE) ["_axioms_def","_axioms","_def"];


(* Try to read the home off thm_deps results *)
fun home_of_name thy nm =
    (case locale_prefix thy nm of SOME l => SOME l | NONE => predicate_locale thy nm);

(* Non-dependency output of thm_deps *)
fun is_machinery thy nm = is_some (predicate_locale thy nm);

fun fixes_of thy loc =
    map (fst o fst) (Locale.params_of thy (Locale.intern thy loc));

(* The theory that declares locale `loc`, i.e. the file a lemma moved into `loc` lands in *)
fun defining_theory thy loc =
    Theory.nodes_of thy |> find_first (fn t =>
         Locale.defined t loc andalso
         not (exists (fn p => Locale.defined p loc) (Theory.parents_of t)));

(* Is the statement expressible in `target`? *)
fun statement_expressible_in thy target t =
    let
      val loc = Locale.intern thy target
      val frees_ok = subset (op =) (Term.add_free_names t [], fixes_of thy loc)
      val consts_ok =
          (case defining_theory thy loc of
            NONE => false
          | SOME tthy => forall (Sign.declared_const tthy) (Term.add_const_names t []))
    in frees_ok andalso consts_ok end;

(* base name -> fully-qualified name(s) for facts defined in thy *)
fun local_name_index thy =
    let
      val facts = Global_Theory.facts_of thy
      val prev  = map Global_Theory.facts_of (Theory.parents_of thy)
      val local_ = Facts.dest_all (Context.Theory thy) false prev facts
    in
      fold (fn (full, _) => Symtab.cons_list (Long_Name.base_name full, full)) local_ Symtab.empty
    end

(* Rejects a candidate locale if a fact the proof depends on does not exist in the theory that
   declares it (e.g. a lemma proved from a global lemma of a later theory) *)
fun deps_resolve_in thy target dep_names =
    (case defining_theory thy (Locale.intern thy target) of
      NONE => false
    | SOME tthy =>
        let val facts = Global_Theory.facts_of tthy
            val failures = filter_out (Facts.defined facts) dep_names
        in null failures end);



(**** ABSTRACTION ****)

(* FIXME: this is over-specialised to lambda f instantiations right now *)
fun abs_pattern base (fixv, abs) =
    let
      val abs'        = Envir.beta_eta_contract abs
      val (bs, body) = Term.strip_abs abs'
      val holes      = map_index (fn (i, (x, T)) => Var ((x, base + i), T)) bs
      val pat        = Term.subst_bounds (rev holes, body)  (* poke holes in bounds *)
      val rhs        = list_comb (fixv, holes)              (* put it back together *)
    in (pat, rhs) end

fun body_text body =
    let fun tt (XML.Text s) = s
          | tt (XML.Elem (_, ts)) = implode (map tt ts)
    in implode (map tt body) end;

(* same term once every type variable is collapsed (contexts name type variables differently) *)
fun same_modulo_tvars t u =
    let
      val collapse = Term.map_types (Term.map_atyps
                                         (fn TFree _ => TFree ("'a", []) | TVar _ => TFree ("'a", []) | T => T))
    in collapse t aconv collapse u end


(* Rewrite rules undoing phi's instantiation of `parent`'s parameters, plus the names of
   the parameters phi passes through unchanged *)
fun abstraction_rules thy parent phi base =
    let
      val (kept, moved) =
          Locale.params_of thy (Locale.intern thy parent)
                           |> map (fn ((x, T), _) => Free (x, T))
                           |> map (fn p => (p, Envir.beta_norm (Morphism.term phi p)))
                           |> List.partition (uncurry same_modulo_tvars)
    in (map (abs_pattern base) moved, map (fst o dest_Free o fst) kept) end;

(* Reverse the instantiation along one registration (parent -> home) with morphism phi.
   NONE if a parameter of `home` survives *)
fun abstract_term thy (parent, phi) home t =
    let
      val (rules, passthrough) = abstraction_rules thy parent phi (Term.maxidx_of_term t + 1)
      val t' = Pattern.rewrite_term thy rules [] t
      val bad = subtract (op =) passthrough (fixes_of thy home)
    in
      if Term.exists_subterm (fn Free (n, _) => member (op =) bad n | _ => false) t'
      then NONE else SOME t'
    end;

(* Abstract each statement token separately so the editor can splice them back one at a time
   NONE if any token cannot be handled *)
fun abstract_tokens thy (parent, phi) home target toks =
    let
      val hctxt = Locale.init (Locale.intern thy home) thy
      val tctxt = Locale.init (Locale.intern thy target) thy
      val pctxt =
          Locale.init (Locale.intern thy parent) thy
                      |> Config.put show_types false
                      |> Config.put show_sorts false
                      |> Config.put show_markup false
      fun print t = body_text (YXML.parse_body (Syntax.string_of_term pctxt t))

      fun one tok =
          let
            (* SOME result if tok parses with `read`, NONE otherwise *)
            fun via read =
                let fun reads_as s t = (case try (read tctxt) s of SOME u => same_modulo_tvars u t | NONE => false)
                in
                  (case try (read hctxt) tok of
                    NONE => NONE
                  | SOME t =>
                      (case abstract_term thy (parent, phi) home t of
                        NONE => SOME NONE
                      | SOME t' =>
                          if t aconv t' andalso reads_as tok t then SOME (SOME tok)
                          else
                            let val s = print t'
                            in if reads_as s t' then SOME (SOME s) else SOME NONE end))
                end
          in
            (case via Syntax.read_prop of
              SOME r => r
            | NONE =>
                (case via Syntax.read_term of
                  SOME r => r
                | NONE => if can (Syntax.read_typ hctxt) tok then SOME tok else NONE))
          end

      val results = map one toks
    in
      if forall is_some results then SOME (map the results) else NONE
    end;


(*********************)

(* Mandatory qualifier under which the parent's facts appear in the child, e.g. "aczel" *)
fun qualifier_of phi =
    Binding.prefix_of (Morphism.binding phi (Binding.name "x"))
                      |> filter snd |> map fst |> Long_Name.implode;

(* Locales whose predicate occurs in the statement, e.g. wf_digraph in "wf_digraph G" *)
fun predicate_locales thy edges home t =
    Term.add_const_names t []
                         |> map_filter (fn c =>
          if Locale.defined thy c then SOME c
          else
            (case try (unsuffix "_axioms") c of
              SOME l => if Locale.defined thy l then SOME l else NONE
            | NONE => NONE))
                         |> filter (member (op =) (above edges home))


val _ =
    Query_Operation.register {name = "weakest_locale", pri = 0}
                             (fn {state, args, writelns_result, ...} =>
let
  val thy = Proof_Context.theory_of (Toplevel.context_of state)
  val ctxt = Proof_Context.init_global thy

  val dep_graph  = mk_deps thy
  val edges = mk_edges dep_graph
  val cs    = mk_cs edges
  val show  = Locale.extern ctxt

  val index = local_name_index thy
  val plain_edges =
      dep_graph
          |> filter (fn ((p, _), phi) =>
null (fst (abstraction_rules thy p phi 0)) andalso qualifier_of phi = "")
          |> map fst

  (* one lemma *)
  fun analyse_one (base, toks) =
      (case Symtab.lookup_list index base of
        [] => (base, false, "", [], [], base ^ ": not found in this theory")
      | full :: rest =>
          let
            val _ = if null rest then () else warning ("ambiguous base name: " ^ base)
            val thm  = Global_Theory.get_thm thy full
            val home = home_of_name thy full
            val deps =
                Thm_Deps.thm_deps thy [thm]
                                  |> map (fn (_, (dn, _)) => dn)
                                  |> filter_out (is_machinery thy)
                                  |> distinct (op =)

            (* The lemma's real proposition in its home locale *)
            val prop =
                (case home of
                  SOME h => Thm.prop_of (Proof_Context.get_thm (Locale.init h thy) base)
                | NONE => Thm.prop_of thm)
            val homes =
                map_filter (home_of_name thy) deps @
                (case home of SOME h => predicate_locales thy edges h prop | NONE => [])
                    |> distinct (op =)



            (* Can the statement live in c as is? *)
            fun valid prop c =
                forall (fn hh => member (op =) (above edges c) hh) homes
                andalso statement_expressible_in thy c prop
                andalso deps_resolve_in thy c deps

            (* Do rewritten statement chunks still parse in c? *)
            fun parses_in c toks =
                let val ctxt = Locale.init (Locale.intern thy c) thy
                in
                  toks |> forall (fn tok =>
    can (Syntax.read_prop ctxt) tok orelse can (Syntax.read_term ctxt) tok
    orelse can (Syntax.read_typ ctxt) tok)
                end

            fun strength (l, _, _, _) = length (above edges l)

            (* Weakest placement reachable from l: an ordinary lift, or an abstraction along a
            registration into any locale the statement can lift to, followed by further search *)
            fun search (l, prop, toks, quals) =
                let
                  val plain =
                      cs |> filter (fn c =>
      member (op =) (above plain_edges l) c andalso valid prop c
      andalso parses_in c toks)
(* weakest placement reachable by plain lifts alone *)
                  val by_plain = (case plain of c :: _ => SOME (c, prop, toks, quals) | [] => NONE)
                                     (* Try to abstract along each edge in `by_plain` *)
                  val by_abs =
                      plain |> maps (fn c =>
       dep_graph |> map_filter (fn ((p, t), phi) =>
  if t <> c then NONE
  else
    let val instantiates = not (null (fst (abstraction_rules thy p phi 0))) in
      (case abstract_term thy (p, phi) c prop of
        NONE => NONE
      | SOME prop' =>
          if prop' aconv prop andalso (instantiates orelse qualifier_of phi = "") then NONE
          else
            (case abstract_tokens thy (p, phi) c p toks of
              NONE => NONE
            | SOME toks' => search (p, prop', toks', quals @ [qualifier_of phi])))
    end))
                in
                    (* Takes best of by_abs and by_plain *)
                  fold (fn s => fn best =>
(case best of
  SOME b => if strength s < strength b then SOME s else best
| NONE => SOME s))
                       by_abs by_plain
                end
            (***************)

            val (movable, target_s, abstracted, qual, msg) =
                (case home of
                  SOME h =>
                    (case search (h, prop, toks, []) of
                      NONE => (false, "", [], [], base ^ ": no valid placement")
                    | SOME (l, _, toks', quals) =>
                        if l = h then (false, "", [], [], base ^ " already weakest (" ^ show h ^ ")")
                        else if null quals then (true, show l, [], [], base ^ ":  " ^ show h ^ "  ->  " ^ show l)
                        else (true, show l, toks', quals,
                              base ^ ":  " ^ show h ^ "  ->  " ^ show l ^ "  (via abstraction)"))
                | NONE => (false, "", [], [], base ^ ": not stated in a locale"))
          in (base, movable, target_s, abstracted, qual,
              msg ^ "  [homes: " ^ commas (map show homes) ^ "]"
              ^ "  [deps: " ^ commas (filter (is_some o home_of_name thy) deps) ^ "]"
              ^ (if null rest then "" else "  [AMBIGUOUS: " ^ commas (full :: rest) ^ "]"))
          end)
  fun groups (nm :: n :: rest) =
      let val k = the_default 0 (Int.fromString n)
      in (nm, take k rest) :: groups (drop k rest) end
    | groups _ = []
  val paired = groups args
  val results = (* Results of analysis of all proofs in a locale *)
      Par_List.map (fn (p as (nm0, _)) =>
(case Exn.result analyse_one p of
  Exn.Res r => r
| Exn.Exn exn =>
    if Exn.is_interrupt exn then Exn.reraise exn
    else (strip_local nm0, false, "", [], [],
          "EXN " ^ nm0 ^ ": " ^ @{make_string} exn)))
                   paired

  (* Debug output, surfaces in stdout (prints to console wherever Isabelle as launched from) *)
  val diag =
      XML.Elem (("finding", [("name", "__diag__"), ("movable", "true")]),
                [XML.Text ("args=" ^ string_of_int (length args)
                           ^ " lemmas=" ^ string_of_int (length paired)
                           ^ " results=" ^ string_of_int (length results))])
  (* Structures results of a singular analysis as an XML element *)
  fun finding (nm, movable, target, abstracted, qual, msg) =
      XML.Elem (("finding",
                 [("name", nm),
                  ("movable", Value.print_bool movable),
                  ("target", target),
                  ("qualifier", Long_Name.implode (filter_out (fn q => q = "") qual)),
                  ("nabs", Value.print_int (length abstracted))] @
                 map_index (fn (i, s) => ("abs" ^ Value.print_int i, s)) abstracted),
                [XML.Text msg])
in
  writelns_result (* What the Scala side reads *)
      [YXML.string_of (XML.Elem (("weakest_locale", []), diag :: map finding results))]
end)
