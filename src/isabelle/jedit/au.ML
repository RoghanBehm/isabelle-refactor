(* au: least-general-generalisation of two typed terms.
  The class algebra comes from the context of each query.  Registers the "anti_unify" query operation.

*)

type aup = {gen: term, ctx: (typ * typ) list, lhs: term, rhs: term}
type state = {next: int, solved: aup list, tmemo: ((typ*typ) * typ) list}

fun memo_lookup key ({tmemo, ...}: state) = AList.lookup (op =) tmemo key;
fun memo_add (k, v) ({next, solved, tmemo}: state) =
  {next = next, solved = solved, tmemo = (k, v) :: tmemo};

fun join_sort algebra (T1, T2) =
  Sorts.minimize_sort algebra
    (filter (fn c => Sorts.of_sort algebra (T1, [c]) andalso Sorts.of_sort algebra (T2, [c]))
            (Sorts.all_classes algebra));

fun fresh_tvar S ({next, solved, tmemo}: state) =
  (TVar (("'T", next), S), {next = next + 1, solved = solved, tmemo = tmemo});
fun fresh T ({next, solved, tmemo}: state) =
  (Var (("G", next), T), {next = next + 1, solved = solved, tmemo = tmemo});

fun rigid (Var _) = false | rigid _ = true

fun disagree algebra (T1, T2) st =
  case memo_lookup (T1, T2) st of
    SOME v => (v, st)
  | NONE   => let val (v, st') = fresh_tvar (join_sort algebra (T1, T2)) st
              in (v, memo_add ((T1, T2), v) st') end

fun lg algebra (T1, T2) st =
  if T1 = T2 then (T1, st)
  else case (T1, T2) of
    (Type (a, ts), Type (b, ss)) =>
      if a = b
      then let val (gs, st') = fold_map (lg algebra) (ts ~~ ss) st in (Type (a, gs), st') end
      else disagree algebra (T1, T2) st
  | _ => disagree algebra (T1, T2) st

fun chk (l, r) (fwd, bwd) =
    case (Inttab.lookup fwd l, Inttab.lookup bwd r) of
        (NONE, NONE) => SOME (Inttab.update (l, r) fwd, Inttab.update (r, l) bwd)
      | (SOME r', _) => if r' = r then SOME (fwd, bwd) else NONE
      | (_, SOME l') => if l' = l then SOME (fwd, bwd) else NONE

fun col depth (a, b) (fwd, bwd) =
    case (a, b) of
        (Const p, Const q) => if p = q then SOME (fwd, bwd) else NONE
      | (Free p, Free q)   => if p = q then SOME (fwd, bwd) else NONE
      | (Bound i, Bound j) =>
          if i < depth orelse j < depth
          then (if i = j then SOME (fwd, bwd) else NONE)
          else chk (i - depth, j - depth) (fwd, bwd)
      | (Abs (_, Ta, a'), Abs (_, Tb, b')) =>
          if Ta = Tb then col (depth + 1) (a', b') (fwd, bwd) else NONE
      | (f $ x, g $ y) =>
          (case col depth (f, g) (fwd, bwd) of SOME acc' => col depth (x, y) acc' | NONE => NONE)
      | _ => NONE

fun find_reuse ({solved, ...}: state) cur_ctx (cur_lhs, cur_rhs) =
    let
      val empty = (Inttab.empty, Inttab.empty)
      fun try [] = NONE
        | try ({gen, ctx = stored_ctx, lhs, rhs} :: rest) =
            (case col 0 (cur_lhs, lhs) empty of
               NONE => try rest
             | SOME acc =>
                 (case col 0 (cur_rhs, rhs) acc of
                    NONE => try rest
                  | SOME (_, b) =>
                    let
                      val stored_ys = sort_distinct int_ord (loose_bnos lhs @ loose_bnos rhs)
                      val types_ok =
                        forall (fn z => nth stored_ctx z = nth cur_ctx (the (Inttab.lookup b z)))
                               stored_ys
                        andalso Term.fastype_of1 (map fst stored_ctx, lhs)
                                 = Term.fastype_of1 (map fst cur_ctx, cur_lhs)
                        andalso Term.fastype_of1 (map snd stored_ctx, rhs)
                                 = Term.fastype_of1 (map snd cur_ctx, cur_rhs)
                    in
                      if types_ok
                      then SOME (gen, map (fn z => Bound (the (Inttab.lookup b z))) stored_ys)
                      else try rest
                    end))
    in try solved end

fun store aup ({next, solved, tmemo}: state) =
  {next = next, solved = aup :: solved, tmemo = tmemo}

fun anti_unif algebra ({gen, ctx, lhs, rhs}: aup, S) =
    case (lhs, rhs) of
      (Abs (_, T1, t'), Abs (_, T2, s')) =>                                (* abs *)
      let
        val (TG, S') = lg algebra (T1, T2) S
        val (body, S'') = anti_unif algebra ({gen = gen, ctx = (T1, T2) :: ctx, lhs = t', rhs = s'}, S')
      in (Abs ("", TG, body), S'') end
| _ =>
      let
        val (h1, ts) = strip_comb lhs
        val (h2, ss) = strip_comb rhs
        (* same symbol, possibly at a different type instance:
           give back the two head types to generalise + a rebuilder *)
        fun same_head (Const (c, T1), Const (d, T2)) =
              if c = d then SOME (T1, T2, fn T => Const (c, T)) else NONE
          | same_head (Free (a, T1), Free (b, T2)) =
              if a = b then SOME (T1, T2, fn T => Free (a, T)) else NONE
          | same_head (Bound i, Bound j) =
              if i = j then SOME (dummyT, dummyT, fn _ => Bound i) else NONE
          | same_head _ = NONE
      in
        case (if length ts = length ss then same_head (h1, h2) else NONE) of
          SOME (T1, T2, mk) =>                                             (* dec *)
          let
            val (TH, S0) = lg algebra (T1, T2) S
            val (gs, S') =
              fold_map (fn (t, s) => fn S'' =>
                  anti_unif algebra ({gen = gen, ctx = ctx, lhs = t, rhs = s}, S''))
                (ts ~~ ss) S0
          in (list_comb (mk TH, gs), S') end
        | NONE =>
          (case find_reuse S ctx (lhs, rhs) of
             SOME (Y, args) => (list_comb (Y, args), S)                    (* mer *)
           | NONE =>                                                       (* sol *)
             let
               val TsL = map fst ctx and TsR = map snd ctx
               val ys  = sort_distinct int_ord (loose_bnos lhs @ loose_bnos rhs)
               val (argTs, S1) = fold_map (fn y => lg algebra (nth TsL y, nth TsR y)) ys S
               val (TR, S2) =
                 lg algebra (Term.fastype_of1 (TsL, lhs), Term.fastype_of1 (TsR, rhs)) S1
               val (Y, S3) = fresh (argTs ---> TR) S2
             in (list_comb (Y, map Bound ys),
                 store {gen = Y, ctx = ctx, lhs = lhs, rhs = rhs} S3) end)
      end

fun anti_unify algebra (t, s) =
  (* Start naming counter from max index to avoid TVar indexname collision *)
  let val a = Int.max (Term.maxidx_of_term t, Term.maxidx_of_term s)
  in #1 (anti_unif algebra ({gen = Var (("G", 0), dummyT), ctx = [], lhs = t, rhs = s},
                            {next = a + 1, solved = [], tmemo = []}))
  end


(* turn input schematic Vars into Frees so they count as rigid heads *)
fun prep t =
  Term.map_aterms (fn Var ((n, i), T) => Free ("?" ^ n ^ string_of_int i, T) | a => a) t


fun prop_of_rule ctxt name =
    Proof_Context.get_thm ctxt name
                          |> Object_Logic.rulify ctxt
                          |> Thm.prop_of
                          |> Envir.eta_long []

(* Print the generalisation as fixes/shows with explicit types and sorts, so that reading
   the inserted lemma back gives exactly this term.  Printing the bare proposition lets type
   inference re-read the variables at the weakest sort their constants need (e.g. 'a::ord,
   where transitivity is not a theorem). *)
fun isar_statement ctxt t =
  let
    fun group [] = []
      | group ((x, T) :: rest) =
          let val (same, others) = List.partition (fn (_, U) => U = T) rest
          in (x :: map fst same, T) :: group others end
    val typ_str = Syntax.string_of_typ (Config.put show_sorts true ctxt)
    val prop_str = Syntax.string_of_term (Config.put show_types false ctxt)
    val fixes =
      group (rev (Term.add_frees t []))
      |> map (fn (xs, T) => space_implode " " xs ^ " :: " ^ quote (typ_str T))
  in
    (if null fixes then "" else "  fixes " ^ space_implode " and " fixes ^ "\n") ^
    "  shows " ^ quote (prop_str t)
  end

val _ =
  Query_Operation.register {name = "anti_unify", pri = 0}
    (fn {state, args, writelns_result, ...} =>
      case args of
        [n1, n2] =>
          let
            val ctxt = Toplevel.context_of state
            val algebra = Sign.classes_of (Proof_Context.theory_of ctxt)
            val t1 = prop_of_rule ctxt n1
            val t2 = prop_of_rule ctxt n2
            val gen = anti_unify algebra (prep t1, prep t2)
            fun post t =
              let
                fun strip n = if String.isPrefix "?" n then String.extract (n, 1, NONE) else n
              in
                t |> Term.map_aterms
                     (fn Var ((n, i), T) => Free (strip n ^ string_of_int i, T)   (* real holes: G0, G1, \<dots> *)
                       | Free (n, T)      => Free (strip n, T)                     (* prep frees: ?n0 -> n0 *)
                       | a => a)
                  |> Term.map_types (Term.map_atyps
                     (fn TVar ((n, i), S) => TFree (strip n ^ string_of_int i, S)
                       | a => a))
              end
            val s = isar_statement ctxt (post gen)
          in writelns_result [YXML.string_of (XML.Elem (("anti_unify", []), [XML.Text s]))] end
      | _ => writelns_result
               [YXML.string_of (XML.Elem (("anti_unify_error", []), [XML.Text "expected two names"]))])
