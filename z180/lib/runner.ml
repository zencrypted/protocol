(* lib/runner.ml -- scenario execution and verdicts.

   The runner owns exactly one idea: an `expect` is judged against the
   observation the *last step of the same speaker* produced, and if there was
   no such step, against the mailbox that reader is currently owed.  That is
   the whole delivery model in one sentence, and it is why the runner is not
   allowed to grow a notion of "the response" of its own.

   Nothing here turns a FAIL into a PASS, and nothing here counts a SKIP as
   a PASS.  A scenario whose assertions were all skipped is reported as such,
   because the superseded oracle's failure mode was precisely a green run that
   asserted nothing.                                        *)

open Kernel
open Semantics

type line = { idx : int; src : string; verdict : verdict }

type report = {
  name : string;
  lines : line list;
  passed : int;
  failed : int;
  skipped : int;
  asserted : int;  (* expectations judged, so an all-skip run is visible *)
}

let pp_verdict = function
  | Pass -> "PASS"
  | Fail m -> "FAIL " ^ m
  | Skip m -> "SKIP " ^ m

(* What a reader is owed when the scenario asserts without asking.  L1
   multicast pushes; a bare `expect message` after `session bob` is a claim
   about the delivery queue, and the queue is a fold over the log. *)
let owed w reader = obs reader Ch_inbox (List.map item_of (pending w reader))

(* ---- rendering, for the report only ---- *)

let describe nm = function
  | KS_actor a -> "session " ^ nm a
  | KS_tier T_l1 -> "tier l1"
  | KS_tier T_l2 -> "tier l2"
  | KS_given gf -> "given " ^ (match gf with
      | GF_clearance (a, l) -> nm a ^ " clearance " ^ l
      | GF_branch (a, b) -> nm a ^ " branch " ^ b
      | GF_feed_branch (f, b) -> nm f ^ " branch " ^ b
      | GF_org (a, o) -> nm a ^ " org " ^ o
      | GF_class (m, l) -> "message " ^ nm m ^ " class " ^ l
      | GF_field_level (m, f, h, l) ->
          "message " ^ nm m ^ " field " ^ nm f ^ (if h then " hidden" else " visible")
          ^ " at " ^ l
      | GF_rel (a, k, b) -> nm a ^ " " ^ k ^ " " ^ nm b
      | GF_msg (fd, seq, from, body, mid, al) ->
          "feed " ^ nm fd.feed_a ^ " seq " ^ string_of_int seq ^ " from " ^ nm from
          ^ " id " ^ nm mid ^ " " ^ body
          ^ (match al with Some x -> " as " ^ nm x | None -> "")
      | GF_read (a, fd, up) -> nm a ^ " read " ^ nm fd.feed_a ^ " up to " ^ string_of_int up
      | GF_exists (w_, n) -> w_ ^ " " ^ nm n
      | GF_role (a, r, g) -> nm a ^ " " ^ r ^ " of " ^ nm g
      | GF_notmember (a, g) -> nm a ^ " not in " ^ nm g
      | GF_ban (a, sc) -> nm a ^ " banned" ^ (match sc with Some x -> " in " ^ nm x | None -> ""))
  | KS_probe (a, p) ->
      "when " ^ nm a ^ " "
      ^ (match p with
         | P_sends -> "sends"
         | P_inbox -> "queries inbox"
         | P_home -> "queries home"
         | P_events f -> "queries events for " ^ nm f.feed_a
         | P_search f -> "queries search in " ^ nm f.feed_a
         | P_reads f -> "reads " ^ nm f.feed_a)
  | KS_cmd (_, c) ->
      "do "
      ^ (match c with
         | C_connect _ -> "connect"
         | C_disconnect -> "disconnect"
         | C_reconnect -> "reconnect"
         | C_auth _ -> "auth"
         | C_renew -> "renew"
         | C_revoke -> "revoke"
         | C_post (kf, _, _) -> "send " ^ (match kf with KF f -> nm f.feed_a | KF_self -> "self" | KF_focus -> "focus")
         | C_read _ -> "read"
         | C_typing a -> "typing " ^ nm a
         | C_ack m -> "ack " ^ nm m
         | C_edit _ -> "edit"
         | C_delete m -> "delete " ^ nm m
         | C_group_new g -> "create group " ^ nm g
         | C_group_del g -> "delete group " ^ nm g
         | C_add _ -> "add"
         | C_remove _ -> "remove"
         | C_ban _ -> "ban"
         | C_query q -> "query " ^ (match q with
             | Q_inbox _ -> "inbox" | Q_inbox_cont -> "inbox continue"
             | Q_events _ -> "events" | Q_cursor _ -> "cursor read"
             | Q_home _ -> "home" | Q_home_cont -> "home continue"
             | Q_roster -> "roster" | Q_groups -> "groups"
             | Q_members _ -> "members" | Q_moderation _ -> "moderation"
             | Q_subs -> "subscriptions" | Q_search _ -> "search"
             | Q_search_cont -> "search continue" | Q_discover s -> "discover " ^ s)
         | C_bootstrap _ -> "bootstrap"
         | C_authority (m, _) -> "authority " ^ m)
  | KS_expect k ->
      "expect "
      ^ (match k with
         | J_msg { neg; _ } -> (if neg then "not " else "") ^ "message"
         | J_vis { hidden; _ } -> "message " ^ (if hidden then "hidden" else "visible")
         | J_field _ -> "message field"
         | J_ack _ -> "ack"
         | J_state s -> s
         | J_event { fam; kind; _ } -> fam ^ " " ^ kind
         | J_access b -> "access " ^ (if b then "allowed" else "denied")
         | J_error (c, neg) -> (if neg then "not " else "") ^ "error " ^ c
         | J_coll { what; _ } -> what
         | J_flag s -> s
         | J_rel { actor; _ } -> nm actor ^ " in roster"
         | J_ban (a, _) -> nm a ^ " banned"
         | J_exists (w_, n) -> w_ ^ " " ^ nm n ^ " exists"
         | J_role (a, r, g) -> nm a ^ " " ^ r ^ " of " ^ nm g
         | J_cursor (s, _) -> "read cursor " ^ s
         | J_feature f -> "feature " ^ f
         | J_vsn v -> "selectedVsn " ^ v)
  | KS_wait ms -> "wait " ^ string_of_int ms ^ "ms"
  | KS_skip -> "skip"

(* ---- execution ---- *)

type state = {
  w : world;
  actor : aid;
  last : obs option;
  acc : line list;
  pass : int;
  fail : int;
  skip : int;
  asserted : int;
}

let record st idx src v =
  { st with
    acc = { idx; src; verdict = v } :: st.acc;
    pass = st.pass + (match v with Pass -> 1 | _ -> 0);
    fail = st.fail + (match v with Fail _ -> 1 | _ -> 0);
    skip = st.skip + (match v with Skip _ -> 1 | _ -> 0) }

let run ?(names = []) (name : string) (kss : kstmt list) : report =
  let rev = List.map (fun (n, a) -> (a, n)) names in
  let nm a =
    match List.assoc_opt a rev with
    | Some s -> s
    | None ->
        if a = no_principal then "<none>"
        else if a >= 1_000_000 then "id:" ^ string_of_int a
        else "#" ^ string_of_int a
  in
  let step_st st k =
    let src = describe nm k in
    match k with
    | KS_actor a ->
        (* A new speaker inherits no observation: alice's reply is not what
           bob was shown, and sharing it would assert across principals. *)
        ({ st with w = st.w; actor = a; last = None }, src, Pass)
    | KS_tier t -> ({ st with w = { st.w with w_tier = t } }, src, Pass)
    | KS_given gf ->
        let w = apply_fact st.w gf in
        (* A seeded message claims a feed ordinal.  The ordinal is derived by
           folding the log, so the claim is checked against the derivation
           rather than trusted -- a scenario that seeds "message 3" as the
           second post is wrong, and saying so beats renumbering it. *)
        let v =
          (match gf with
           | GF_msg (f, seq, _, _, mid, _) ->
               (match feed_seq w.w_log f mid with
                | Some n when n = seq -> Pass
                | Some n -> Fail (Printf.sprintf "seeded seq %d is ordinal %d" seq n)
                | None -> Fail "seeded message absent from the log")
           | _ -> Pass)
        in
        ({ st with w }, src, v)
    | KS_probe (a, p) ->
        (* `when` observes and does not act: the world is returned untouched. *)
        let o = probe st.w a p in
        ({ st with last = Some o }, src, Pass)
    | KS_cmd (a, c) ->
        let w, o = step st.w a c in
        let note =
          match o.o_out with
          | Accepted -> ""
          | Rejected code -> " [rejected: " ^ code ^ "]"
          | Unsupported f -> " [unsupported: " ^ f ^ "]"
        in
        ({ st with w; last = Some o }, src ^ note, Pass)
    | KS_expect kj ->
        let o =
          match st.last with
          | Some o -> Some o
          | None -> if st.actor = no_principal then None else Some (owed st.w st.actor)
        in
        (match o with
         | None ->
             (* Not an elaboration abort, and not a pass.  An assertion with
                no speaker and no preceding observation is exactly as
                uninformative as the oracle's vacuous green, so the report
                carries that sentence rather than a checkmark. *)
             (st, src, Fail "no speaker and no prior observation to assert about")
         | Some o ->
             let v, ids = evaluate st.w o kj in
             let w = if ids = [] then st.w else consume st.w o.o_actor ids in
             ({ st with w; asserted = st.asserted + 1 }, src, v))
    | KS_wait ms ->
        (st, src, Skip (Printf.sprintf "real time (%d ms) is not modelled" ms))
    | KS_skip -> (st, src, Skip "explicit skip in the scenario")
  in
  let rec go st i = function
    | [] -> st
    | k :: rest ->
        let st', src, v = step_st st k in
        go (record st' i src v) (i + 1) rest
  in
  let st = go { w = empty_world (); actor = no_principal; last = None; acc = []
              ; pass = 0; fail = 0; skip = 0; asserted = 0 } 1 kss in
  { name; lines = List.rev st.acc; passed = st.pass; failed = st.fail
  ; skipped = st.skip; asserted = st.asserted }

let outcome (r : report) =
  match r.asserted, r.failed with
  | 0, 0 -> `Nothing
  | _, 0 -> `Green
  | _ -> `Red

(* One line per scenario, in the order the gate reads it.  `asserted` is
   reported because a scenario with zero assertions is not a pass, whatever
   its other counts say. *)
let summary (r : report) =
  Printf.sprintf "pass %2d fail %2d skip %2d asserted %2d"
    r.passed r.failed r.skipped r.asserted

let tag (r : report) =
  match outcome r with `Green -> "OK" | `Red -> "FAIL" | `Nothing -> "NOASSERT"

let failures (r : report) =
  List.filter_map
    (fun (l : line) ->
      match l.verdict with
      | Fail m -> Some (l.idx, l.src, m)
      | _ -> None)
    r.lines

let detail (r : report) =
  let b = Buffer.create 256 in
  Printf.bprintf b "%s\n" r.name;
  List.iter
    (fun (l : line) ->
      Printf.bprintf b "  %3d  %-44s  %s\n" l.idx
        (String.sub l.src 0 (min 44 (String.length l.src)))
        (pp_verdict l.verdict))
    r.lines;
  Buffer.contents b
