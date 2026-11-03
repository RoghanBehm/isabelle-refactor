(* Query operations for have-block promotion.

   Both operations take as their first argument the name of the locale (or class) the
   lifted lemma will be stated in, or "" for none. Whatever that target already provides
   (fixed params, assms and facts defined under the same name)
   are left out of the lemma's fixes and premises, since the lemma is stated inside it.

   Errors are reported as <liftable_check_error>/<chained_facts_error>, and a state that is
   not a proof as <liftable_check_not_in_proof>/<chained_facts_not_in_proof>. *)

local


fun plain_text s =
  let
    fun tt (XML.Text s) = s
      | tt (XML.Elem (_, ts)) = implode (map tt ts)
  in implode (map tt (YXML.parse_body s)) end;

fun plain_ctxt ctxt =
  ctxt
  |> Config.put show_markup false
  |> Config.put show_types false
  |> Config.put show_sorts false;

fun print_term ctxt t = plain_text (Syntax.string_of_term (plain_ctxt ctxt) t);

(* Types for `fixes` keep their sorts *)
fun print_typ ctxt T =
  plain_text (Syntax.string_of_typ (plain_ctxt ctxt |> Config.put show_sorts true) T);


(* Local facts *)

fun unlocal name = the_default name (try (unprefix "local.") name);

val reserved_names = ["this", "calculation", "that", "assms"];

(* Local facts consisting of one theorem *)
fun single_local_facts ctxt =
  let val thy = Proof_Context.theory_of ctxt in
    Facts.dest_all (Context.Proof ctxt) false [Global_Theory.facts_of thy]
      (Proof_Context.facts_of ctxt)
    |> map_filter (fn (name, [th]) => SOME (unlocal name, th) | _ => NONE)
    |> filter_out (fn (name, _) => member (op =) reserved_names name)
  end;

(* A statement with its schematic variables bound again. *)
fun close_schematic t =
  fold_rev Logic.all (map Var (rev (Term.add_vars t []))) t;

fun same_stmt (t, u) = close_schematic t aconv close_schematic u;

(* Names under which statement t is available as a single local fact *)
fun names_for facts t =
  facts
  |> map_filter (fn (name, th) => if same_stmt (Thm.prop_of th, t) then SOME name else NONE)
  |> distinct (op =);

(* Locally fixed variables occurring in any of ts *)
fun fixed_vars ctxt ts =
  let
    val frees = fold Term.add_frees ts []
    val fixed = fold (Variable.add_fixed_names ctxt) ts []
  in filter (fn (n, _) => member (op =) fixed n) frees |> distinct (op =) end;


(* The lifted lemma's target *)

fun split_args (target :: rest) = (target, rest)
  | split_args [] = ("", []);

fun target_context thy target =
  if target = "" then NONE
  else try (fn () => Locale.init (Locale.intern thy target) thy) ();

type provided =
  {fixed: string list, prems: term list, has_fact: string * thm list -> bool};

(* Deps the target already provides *)
fun provided_by NONE : provided = {fixed = [], prems = [], has_fact = K false}
  | provided_by (SOME tctxt) =
      {fixed = maps (fn (a, b) => [a, b]) (Variable.dest_fixes tctxt),
       prems = map Thm.prop_of (Assumption.all_prems_of tctxt),
       has_fact = fn (name, ths) =>
         (case try (Proof_Context.get_fact tctxt) (Facts.named name) of
           SOME ths' =>
             length ths = length ths' andalso
             forall (fn (a, b) => Thm.prop_of a aconv Thm.prop_of b) (ths ~~ ths')
         | NONE => false)};

fun target_fixed (prov: provided) ctxt (n, _) =
  member (op =) (#fixed prov) n orelse
  member (op =) (#fixed prov) (Variable.revert_fixed ctxt n);


(* XML *)

fun elem name body = XML.Elem ((name, []), body);
fun text_elem name s = elem name [XML.Text s];

fun fixes_xml ctxt vars =
  elem "fixes" (vars |> map (fn (n, T) =>
    elem "var" [text_elem "name" (Variable.revert_fixed ctxt n),
                text_elem "typ" (print_typ ctxt T)]));

fun stmt_xml ctxt facts tag t =
  elem tag (text_elem "prop" (print_term ctxt (close_schematic t)) ::
    map (text_elem "name") (names_for facts t));

fun report_errors tag writelns_result f =
  (case Exn.capture f () of
    Exn.Res _ => ()
  | Exn.Exn exn =>
      if Exn.is_interrupt exn then Exn.reraise exn
      else writelns_result
        [YXML.string_of (text_elem (tag ^ "_error") (@{make_string} exn))]);

in

val _ =
  Query_Operation.register {name = "check_liftable", pri = 0}
    (fn {state, args, writelns_result, ...} =>
      if not (Toplevel.is_proof state) then
        writelns_result [YXML.string_of (elem "liftable_check_not_in_proof" [])]
      else report_errors "liftable_check" writelns_result (fn () =>
        let
          val (target, refs) = split_args args
          val proof = Toplevel.proof_of state
          val ctxt = Proof.context_of proof
          val thy = Proof_Context.theory_of ctxt
          val prov = provided_by (target_context thy target)
          val fact = Proof.the_fact proof
          val prop = Thm.prop_of fact
          val facts = single_local_facts ctxt

          (* local facts the block refers to, plus any non-global thm_deps names *)
          val dep_names =
            (Thm_Deps.thm_deps thy [fact]
              |> map (fn (_, (name, _)) => name)
              |> filter_out (Facts.defined (Global_Theory.facts_of thy))
              |> map unlocal)
            @ refs
            |> filter (fn n => n <> "")
            |> distinct (op =)
          val lookups =
            map (fn n => (n, try (Proof_Context.get_fact ctxt) (Facts.named n))) dep_names
          val resolved = map_filter (fn (n, SOME ths) => SOME (n, ths) | _ => NONE) lookups
          val unresolved = map_filter (fn (n, NONE) => SOME n | _ => NONE) lookups

          (* facts available to the lifted lemma according to target *)
          val own_deps = filter_out (#has_fact prov) resolved

          (* hyps that are already available without explicit assumes clause *)
          val covered = maps (map Thm.prop_of o snd) resolved @ #prems prov
          val open_hyps =
            Thm.hyps_of fact
            |> filter_out (fn h => exists (fn p => same_stmt (p, h)) covered)

          val fixes =
            fixed_vars ctxt (prop :: open_hyps @ maps (map Thm.prop_of o snd) own_deps)
            |> filter_out (target_fixed prov ctxt)

          val report =
            elem "liftable_check" [
              fixes_xml ctxt fixes,
              elem "deps" (own_deps |> map (fn (n, ths) =>
                elem "dep" (text_elem "name" n ::
                  map (text_elem "prop" o print_term ctxt o close_schematic o Thm.prop_of)
                    ths))),
              elem "unresolved" (map (text_elem "name") unresolved),
              elem "hyps" (map (stmt_xml ctxt facts "hyp") open_hyps)]
        in writelns_result [YXML.string_of report] end));

val _ =
  Query_Operation.register {name = "chained_facts", pri = 0}
    (fn {state, args, writelns_result, ...} =>
      if not (Toplevel.is_proof state) then
        writelns_result [YXML.string_of (elem "chained_facts_not_in_proof" [])]
      else report_errors "chained_facts" writelns_result (fn () =>
        let
          val (target, refs) = split_args args
          val proof = Toplevel.proof_of state
          val ctxt = Proof.context_of proof
          val thy = Proof_Context.theory_of ctxt
          val prov = provided_by (target_context thy target)
          val facts = single_local_facts ctxt

          (* global facts named by the chaining command can be used by the lemma *)
          val globals = filter (Facts.defined (Global_Theory.facts_of thy)) refs
          val global_ths = maps (fn n => Proof_Context.get_fact ctxt (Facts.named n)) globals
          val chained =
            Proof.the_facts proof
            |> filter_out (fn th => exists (fn g => Thm.eq_thm_prop (g, th)) global_ths)

          (* chained facts the target provides can be used, the rest need premises *)
          fun from_target th =
            let val t = Thm.prop_of th in
              exists (fn p => same_stmt (p, t)) (#prems prov) orelse
              exists (fn n => #has_fact prov (n, [th])) (names_for facts t)
            end
          val (usable, own) = List.partition from_target chained
          val own_props = map Thm.prop_of own

          val report =
            elem "chained_facts" [
              elem "globals" (map (text_elem "name") globals),
              fixes_xml ctxt (fixed_vars ctxt own_props |> filter_out (target_fixed prov ctxt)),
              elem "usable" (map (stmt_xml ctxt facts "fact" o Thm.prop_of) usable),
              elem "facts" (map (stmt_xml ctxt facts "fact") own_props)]
        in writelns_result [YXML.string_of report] end));

end;
