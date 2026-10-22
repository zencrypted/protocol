(* lib/semantics.ml -- the world machine of the Z.180 model.

   Layering, and why it is this way:

     kernel.ml      truth: an append-only log and folds over it.  No policy,
                    no sessions, no notions of permission.
     semantics.ml   this file.  A deterministic step machine over a world,
                    plus judgments evaluated against the observation a step
                    produced.  Policy can refuse an action; it can never
                    rewrite the log (invariant P4).
     elaborator.ml  surface AST -> the kernel terms used here.  The only
                    place names become aids, and the only place sugar dies.
     runner.ml      scenario execution and verdicts.

   Two properties are enforced structurally rather than by tests:

   - `when <actor> <probe>` produces an observation without touching the
     world.  A policy probe that mutated state would make "alice may read
     the feed" and "alice did read the feed" the same fact;
   - a judgment over a channel that does not exist evaluates to *false*,
     including a negated judgment.  The superseded Python oracle raised an
     unconditional `error gap` on `after 0`, so its negative assertions
     passed on errored replies.  That is the vacuous gate: a green run that
     asserted nothing.  Here, `Ch_none` and `Rejected` make every content
     judgment fail loudly, which is what makes the corpus meaningful. *)

open Kernel

(* ---- policy vocabulary ---- *)

type kcmp =
  | KCeq of int
  | KCle of int
  | KCgt of int
  | KCnonempty
  | KCplain

(* The clearance lattice.  X.422.2 carries labels, not ordinals, so the
   model fixes one order and says so: an unknown label is incomparable and
   therefore *denies*, because a policy that fails open is not a policy.
   Any change here is a normative change to the book, not a bug fix. *)
let level_rank (l : string) : int option =
  match String.lowercase_ascii l with
  | "public" | "unclassified" -> Some 0
  | "internal" -> Some 1
  | "confidential" | "restricted" -> Some 2
  | "secret" -> Some 3
  | "top" | "cosmic" -> Some 4
  | _ -> None

let clears reader classification =
  match reader, classification with
  | None, None -> true
  | _, None -> true
  | None, Some _ -> false
  | Some r, Some c ->
      (match level_rank r, level_rank c with
       | Some a, Some b -> a >= b
       | _ -> false)

(* ---- observations ---- *)

(* An observation is what a principal learns from one step.  The channel
   is part of the observation, not an ambient assumption: it is what stops
   `expect not message from bob` from being satisfied by a reply that never
   had a message channel at all. *)
type chan =
  | Ch_none
  | Ch_inbox
  | Ch_events
  | Ch_home
  | Ch_search
  | Ch_roster
  | Ch_groups
  | Ch_members
  | Ch_moderation
  | Ch_subs
  | Ch_acks
  | Ch_auth
  | Ch_access
  | Ch_mutation
  | Ch_discovery
  | Ch_authority
  | Ch_presence

type outcome =
  | Accepted
  | Rejected of string
  | Unsupported of string

type item =
  (* An item carries a Kernel.post: the address, the feed ordinal, the
     author and the payload the reader is given.  Using the kernel record
     rather than a parallel shape is what keeps "what the reader was shown"
     and "what the log says" from drifting apart. *)
  | Itmsg of post
  | Itfeed of { feed : feed; unread : int }
  | Itname of aid
  | Itflag of string

type obs = {
  o_actor : aid;
  o_chan : chan;
  o_out : outcome;
  o_items : item list;
  o_more : bool;
  o_state : (string * datum) list;
}

let no_obs actor = {
  o_actor = actor; o_chan = Ch_none; o_out = Accepted; o_items = [];
  o_more = false; o_state = [];
}

let obs actor ch items = { (no_obs actor) with o_chan = ch; o_items = items }

let with_state o st = { o with o_state = st }
let with_more o m = { o with o_more = m }
let rejected o code = { o with o_out = Rejected code; o_items = []; o_state = [] }
let unsupported o feature = { o with o_out = Unsupported feature; o_items = [] }

(* ---- kernel commands (elaborated, interned, tier-stamped) ---- *)

type kauth =
  | KA_bare
  | KA_password of string
  | KA_token of string
  | KA_resume
  | KA_vsn of string list
  | KA_method of string

type kmut =
  | KM_body of string
  | KM_field of aid * datum

type kadd = KA_group of aid | KA_roster

type kboundary =
  | KB_seq of int
  | KB_cursor
  | KB_snapshot
  | KB_next
  | KB_last

type kquery =
  | Q_inbox of feed * int option
  | Q_inbox_cont
  | Q_events of feed * kboundary * int option
  | Q_cursor of feed * int
  | Q_home of int option * int option
  | Q_home_cont
  | Q_roster
  | Q_groups
  | Q_members of aid
  | Q_moderation of feed option
  | Q_subs
  | Q_search of feed option * string * int option
  | Q_search_cont
  | Q_discover of string

(* kfeed: where a message goes when the scenario did not say.  `send file`
   has no target in the grammar and `send read` may have none; the corpus is
   silent about both, so the model states the rule out loud instead of
   inventing one silently: a file lands in the sender's own mailbox, and a
   bare read addresses the feed the session last touched. *)
type kfeed = KF of feed | KF_focus | KF_self

type kcmd =
  | C_connect of aid option
  | C_disconnect
  | C_reconnect
  | C_auth of kauth
  | C_renew
  | C_revoke
  | C_post of kfeed * payload * aid option
  | C_read of kfeed option * int option
  | C_typing of aid
  | C_ack of aid
  | C_edit of aid * kmut
  | C_delete of aid
  | C_group_new of aid
  | C_group_del of aid
  | C_add of aid * kadd
  | C_remove of aid * kadd
  | C_ban of aid * aid option * bool
  | C_query of kquery
  | C_bootstrap of int option * int option
  | C_authority of string * aid option

(* ---- probes: `when`, which never executes ---- *)

type kprobe =
  | P_sends
  | P_inbox
  | P_home
  | P_events of feed
  | P_search of feed
  | P_reads of feed

(* ---- judgments: `expect`, compiled ---- *)

type kjudg =
  | J_msg of { from : aid option; neg : bool; inbound : bool
             ; body : string option; fields : (aid * datum) list }
  | J_vis of { m : aid; field : aid option; hidden : bool }
  | J_field of aid * aid * datum
  | J_ack of aid
  | J_state of string
  | J_event of { fam : string; kind : string; actor : aid option
               ; up_to : int option; m : aid option; seq : int option }
  | J_access of bool
  | J_error of string * bool
  | J_coll of { what : string; cmp : kcmp; neg : bool }
  | J_flag of string
  | J_rel of { actor : aid; kind : string; neg : bool }
  | J_ban of aid * aid option
  | J_exists of string * aid
  | J_role of aid * string * aid
  | J_cursor of string * feed option
  | J_feature of string
  | J_vsn of string

type kstmt =
  (* Both identities of the acting name: the incidence that owns the session
     state, and the principal it speaks as.  `KS_actor` is the only place the
     mapping enters the world. *)
  | KS_actor of aid * aid
  | KS_tier of tier
  | KS_given of gfact
  | KS_probe of aid * kprobe
  | KS_cmd of aid * kcmd
  | KS_expect of kjudg
  | KS_wait of int
  | KS_skip

(* `given` facts are seed state: they describe the world before the first
   action, and they are the only way to place a message without exercising
   the send path. *)
and gfact =
  | GF_clearance of aid * string
  | GF_branch of aid * string
  | GF_feed_branch of aid * string
  | GF_org of aid * string
  | GF_class of aid * string
  | GF_field_level of aid * aid * bool * string
  | GF_rel of aid * string * aid
  | GF_msg of feed * int * aid * string * aid * aid option
  | GF_read of aid * feed * int
  | GF_exists of string * aid
  | GF_role of aid * string * aid
  | GF_notmember of aid * aid
  | GF_ban of aid * aid option

(* ---- the world ---- *)

type group = {
  gr_name : aid;
  gr_feed : feed;
  gr_owner : aid option;
  gr_members : aid list;
  gr_banned : aid list;
  gr_exists : bool;
}

type session = {
  ss_actor : aid;                 (* who this session speaks as                *)
  ss_connected : bool;
  ss_token : int;                 (* opaque token identity; regenerated by
                                     `renew`, preserved by `resume`            *)
  ss_epoch : int;                 (* session incarnation: `same session`
                                     compares epochs, never token strings      *)
  ss_fresh : bool;                (* the current incarnation was *opened*, not
                                     carried over.  A session fact, not an
                                     observation fact: `connect / auth / expect
                                     session created` asserts two things about
                                     two different steps, and only the world
                                     can carry the first across the second.    *)
  ss_renewed : bool;              (* a token has been rotated for this session *)
  ss_alias : string;              (* surface name, diagnostics only            *)
}

type pevent = { pv_actor : aid; pv_sid : aid; pv_kind : string }
(* A presence event names both the incidence that moved and the principal it
   moves as, because a scenario may assert either: `expect event offline
   alice2` is about the connection, `expect event offline alice` is about the
   user.  Matching either spelling is a decision, recorded here rather than
   buried in a pattern. *)

type world = {
  w_tier : tier;
  w_log : event list;                     (* THE truth.  Append-only.       *)
  w_groups : (aid * group) list;
  w_roster : (aid * aid list) list;
  w_subs : (aid * aid list) list;
  w_clearance : (aid * string) list;
  w_branch : (aid * string) list;
  w_org : (aid * string) list;
  w_class : (aid * string) list;          (* message id -> label            *)
  w_field_hidden : (aid * aid * string) list; (* msg id, field, level       *)
  w_ban : (aid * aid option) list;        (* actor, scope feed or global    *)
  w_speaker : (aid * aid) list;     (* incidence -> principal.  Absent means
        "the name is its own principal", which is every scenario that never
        writes `session x as y`.  Two incidences of one principal then exist,
        which both X.422.2 IncidenceId and a Z.120 instance line require:
        presence, cursors, focus, pages, acks and consumption are per
        incidence, while authorship, feed membership, clearance, roster and
        bans are per principal.  Without the split, `session alice1 as alice`
        and `session alice2 as alice` collapse into one identity and
        `expect event offline alice2` cannot even be stated. *)
  w_sessions : (aid * session) list;  (* keyed by INCIDENCE: one identity,
      and the epoch distinguishes incarnations.  `session alice as a1` names
      the same identity; two live incarnations of one principal in one
      scenario is not expressible, and no scenario in the corpus needs it. *)
  w_presence : (aid * bool) list;         (* online/offline                 *)
  w_pstream : pevent list;                (* orthogonal to the log          *)
  w_acks : (aid * aid) list;              (* reader -> message ids seen     *)
  w_seen : (aid * aid list) list;         (* reader -> consumed by expect   *)
  w_token : int;
  w_epoch : int;
  w_vsn : string;
  w_supported : string list;
  w_selected : string option;
  w_features : string list;
  w_pages : (aid * int) list;             (* continuation cursors per chan *)
  w_focus : (aid * feed) list;             (* last feed the session touched  *)
  w_last_cursor : (aid * feed * int) list; (* for `read cursor unchanged`   *)
  w_authority : (string * aid list) list;  (* L1 authority table state       *)
  w_next_mid : aid;                       (* mint counter for protocol ids  *)
  w_env : (aid * mref) list;               (* captured bindings, in the world
                    so that step and judge stay pure functions: a capture is
                    a fact about the run, not ambient test-harness state.     *)
}

let empty_world () = {
  w_tier = T_l2;
  w_log = []; w_groups = []; w_roster = []; w_subs = [];
  w_clearance = []; w_branch = []; w_org = []; w_class = [];
  w_field_hidden = []; w_ban = []; w_speaker = []; w_sessions = []; w_presence = [];
  w_pstream = []; w_acks = []; w_seen = [];
  w_token = 0; w_epoch = 0;
  (* The capability set of the reference model, written down rather than
     discovered: negotiation can only select from `w_supported`, and
     `expect feature X` is refutable precisely because this list is finite
     and is this one.  A scenario asserting a feature absent from the table
     fails, and the fix is the protocol text or the scenario -- never here. *)
  w_vsn = "v1"; w_supported = [ "v1"; "v2"; "v3" ]; w_selected = None;
  w_features =
    [ "protocol.version"; "auth.methods"; "auth.token"; "feed.replay"
    ; "extension.search"; "query"; "events"; "home"; "roster"; "members"
    ; "moderation"; "token"; "renew"; "resume"; "ack"; "file" ];
  w_pages = []; w_focus = []; w_last_cursor = []; w_authority = [];
  (* aid space: the interner hands out surface names from 1; protocol ids
     minted by a Post come from this disjoint range, so an interned alias can
     never be confused with a minted id, in either direction. *)
  w_next_mid = 1_000_000; w_env = [];
}

(* ---- identity: incidence vs principal ---- *)

(* The acting name is an incidence; the identity it acts as is a principal.
   A name never declared as an incidence of somebody else *is* that somebody
   -- which is what leaves every `session alice` scenario unchanged.  Presence,
   sessions, cursors, focus, pages and acks are per incidence (Z.120 instance
   lines; X.422.2 IncidenceId); membership, clearance, authorship, the roster,
   subscriptions and bans are per principal, and every one of those reads goes
   through `principal` so that two incarnations of one person cannot acquire
   two identities. *)
let principal w a =
  match List.assoc_opt a w.w_speaker with Some p -> p | None -> a

let set_speaker w sid pr =
  { w with w_speaker = (sid, pr) :: List.remove_assoc sid w.w_speaker }

(* Online as a principal: some incidence of theirs is online. *)
let online_as w pr =
  List.exists (fun (sid, on) -> on && principal w sid = pr) w.w_presence

(* ---- membership: who is in a feed, and what that costs ---- *)

let group_of w name = List.assoc_opt name w.w_groups

(* Chan feeds are public publications: anyone may read and post, which is
   what X.422.1 multicast means.  Group feeds are closed.  Private feeds
   are the two principals, canonicalised so the pair is one object. *)
let feed_members w f =
  match f.f_kind with
  | K_private -> [ f.feed_a; f.feed_b ]
  | K_group -> (match group_of w f.feed_a with
                | Some g when g.gr_exists -> g.gr_members
                | _ -> [])
  | K_chan -> [ f.feed_a ]                  (* the channel itself, plus all *)
  | K_mailbox -> [ f.feed_a ]

let in_feed w actor f =
  match f.f_kind with
  | K_private -> actor = f.feed_a || actor = f.feed_b
  | K_group -> (match group_of w f.feed_a with
                | Some g -> g.gr_exists && List.mem actor g.gr_members
                | None -> false)
  | K_chan | K_mailbox -> true

(* Banning is scoped: a global ban blocks the principal everywhere, a group
   ban only inside that group.  It is policy, and policy is consulted at the
   gate -- never by rewriting the log. *)
let is_banned w actor f =
  let global = List.exists (fun (a, s) -> a = actor && s = None) w.w_ban in
  let scoped =
    match f.f_kind with
    | K_group -> List.exists (fun (a, s) -> a = actor
                                        && (match s with
                                            | Some g -> g = f.feed_a
                                            | None -> false)) w.w_ban
    | _ -> false
  in
  global || scoped

(* ---- visibility: policy applied to a payload for one reader ---- *)

let classification w id = List.assoc_opt id w.w_class
let clearance w actor = List.assoc_opt actor w.w_clearance

(* Field-level hiding masks a field for readers below the level.  A masked
   field is *removed* from the payload the reader receives: the corpus
   documents both "removed" and "replaced by a tombstone marker", and the
   two are observationally different for `expect message ... field x`.  We
   choose removal, because a marker leaks the field's existence, and the
   field-level claim in the X.422.2 text is about existence. *)
let mask w reader payload id =
  let drop =
    List.filter_map
      (fun (m, fld, lvl) ->
        if m = id && not (clears (clearance w (principal w reader)) (Some lvl))
        then Some fld
        else None)
      w.w_field_hidden
  in
  let fields = List.filter (fun (n, _) -> not (List.mem n drop)) payload.pp_fields in
  let body =
    if List.mem body_field drop then None else payload.pp_body
  in
  { pp_body = body; pp_fields = fields }

let readable w reader _payload id =
  clears (clearance w (principal w reader)) (classification w id)

(* ---- feed construction ---- *)

let ensure_feed w f =
  match f.f_kind with
  | K_group ->
      if List.mem_assoc f.feed_a w.w_groups then w
      else { w with w_groups = (f.feed_a,
               { gr_name = f.feed_a; gr_feed = f; gr_owner = None
               ; gr_members = []; gr_banned = []; gr_exists = true }) :: w.w_groups }
  | _ -> w

(* Text of a datum, for the search haystack only.  Field names are not
   searched: a term is a value in the payload, not a schema key. *)
let datum_text = function
  | Dtext s -> s
  | Datom s -> s
  | Dint n -> string_of_int n

(* ---- the delivery queue ---- *)

(* What a reader is owed: live posts in feeds it belongs to, that it has not
   already consumed by a previous `expect message`, and that survive policy.
   This is derived from the log every time -- a stored queue would be a
   second truth, and the corpus's replay contradictions come from exactly
   that kind of duplicate. *)
let log_feeds w =
  let rec go seen = function
    | [] -> List.rev seen
    | EvPost (f, _, _, _) :: t
    | EvEdit (f, _, _) :: t
    | EvDelete (f, _) :: t
    | EvRead (_, f, _) :: t ->
        go (if List.exists (feed_eq f) seen then seen else f :: seen) t
    | EvAck _ :: t -> go seen t
  in go [] w.w_log

(* What a reader is owed, in log order: live, unmasked, policy-readable
   posts in feeds it belongs to, minus what a previous `expect message`
   already consumed.  Folded from the log on every call, so the queue can
   never disagree with the truth -- the class of bug the corpus's
   "replay shows tombstones but live read does not" contradiction came
   from.  Redelivery is absorbed exactly as Kernel.project absorbs it, and
   a later Edit rewrites the queued payload rather than adding to it. *)
let pending w reader =
  let seen = try List.assoc reader w.w_seen with Not_found -> [] in
  let rec go acc = function
    | [] -> List.rev acc
    | EvPost (f, m, a, p) :: t ->
        let dup = List.exists (fun ps -> mref_eq ps.ps_ref (f, m)) acc in
        let keep =
          in_feed w (principal w reader) f && not (List.mem m seen) && not dup
        in
        go (if keep then { ps_ref = (f, m); ps_seq = 0; ps_author = a; ps_payload = p } :: acc
            else acc) t
    | EvEdit (f, m, p) :: t ->
        go (List.map (fun ps -> if mref_eq ps.ps_ref (f, m)
                                then { ps with ps_payload = p } else ps) acc) t
    | EvDelete (f, m) :: t ->
        go (List.filter (fun ps -> not (mref_eq ps.ps_ref (f, m))) acc) t
    | _ :: t -> go acc t
  in
  List.filter_map
    (fun ps ->
      let f = fst ps.ps_ref and m = snd ps.ps_ref in
      if readable w reader ps.ps_payload m then
        let n = match feed_seq w.w_log f m with Some n -> n | None -> 0 in
        Some { ps with ps_seq = n; ps_payload = mask w reader ps.ps_payload m }
      else None)
    (go [] w.w_log)

(* The window one reader has over one feed: not a claim on the mailbox,
   because `query events` is a read of the feed, and reads do not consume.
   Policy still applies on the way out -- an unmasked read of a classified
   feed would make the log and the ACL the same object. *)
let feed_window w reader f =
  List.map
    (fun ps ->
      let m = snd ps.ps_ref in
      { ps with ps_payload = mask w reader ps.ps_payload m })
    (List.filter (fun ps -> readable w reader ps.ps_payload (snd ps.ps_ref))
       (feed_live w.w_log f))

(* ------------------------------------------------------------------ *)
(* session, capture and cursor bookkeeping                              *)
(* ------------------------------------------------------------------ *)

let app w e = { w with w_log = w.w_log @ [ e ] }

let fail actor ch code =
  { (no_obs actor) with o_chan = ch; o_out = Rejected code }

(* `deny`/`refuse` exist so a refusal can be the `then` branch of an `if`
   without parentheses: the tuple is built inside the call, and the arm
   reads as one action. *)
let deny w actor ch code = (w, fail actor ch code)

let not_here actor ch feature =
  { (no_obs actor) with o_chan = ch; o_out = Unsupported feature }

let refuse w actor ch feature = (w, not_here actor ch feature)

let item_of ps = Itmsg ps

(* `more` is always computed from the whole collection against the page, so
   a truncated reply cannot claim to be complete and a complete one cannot
   claim to be truncated. *)
let paged actor ch page all =
  { (obs actor ch page) with o_more = List.length all > List.length page }

let paged_from actor ch off page all =
  { (obs actor ch page) with o_more = off + List.length page < List.length all }

let add_to key v tbl =
  let cur = try List.assoc key tbl with Not_found -> [] in
  if List.mem v cur then tbl else (key, v :: cur) :: List.remove_assoc key tbl

let mem_tbl key v tbl = try List.mem v (List.assoc key tbl) with Not_found -> false
let drop_from key v tbl =
  match List.assoc_opt key tbl with
  | None -> tbl
  | Some cur -> (key, List.filter (fun x -> x <> v) cur) :: List.remove_assoc key tbl

let group_get w name = List.assoc_opt name w.w_groups
let group_put w name g =
  { w with w_groups = (name, g) :: List.remove_assoc name w.w_groups }

let resolve_feed w actor = function
  | KF f -> Some f
  | KF_self -> Some (named_feed K_mailbox (principal w actor))
  | KF_focus -> List.assoc_opt actor w.w_focus

let focus_on w actor f =
  { w with w_focus = (actor, f) :: List.remove_assoc actor w.w_focus }

(* Cursors are stamped *before* a step, so `expect read cursor unchanged`
   compares what the previous observation saw with what is true now.
   Stamping after would make the assertion trivially true of its own
   write -- a gate that cannot fail. *)
let cursor_snapshot w actor =
  List.filter_map
    (fun f ->
      match read_cursor w.w_log (principal w actor) f with
      | Some c -> Some (actor, f, c)
      | None -> None)
    (log_feeds w)

let stamp_before w actor =
  let snap = cursor_snapshot w actor in
  { w with w_last_cursor =
      (List.filter (fun (p, _, _) -> p <> actor) w.w_last_cursor) @ snap }

let stamped_cursor w actor f =
  List.find_opt (fun (p, f', _) -> p = actor && feed_eq f f') w.w_last_cursor

let is_online w actor =
  match List.assoc_opt actor w.w_presence with Some b -> b | None -> false

let presence w actor on kind =
  { w with
    w_presence = (actor, on) :: List.remove_assoc actor w.w_presence;
    (* Presence never enters the log.  It is an orthogonal stream, which is
       why "a typing notification rewinds a replay" is refuted by the types
       and not by a test case. *)
    w_pstream =
      w.w_pstream
      @ [ { pv_actor = principal w actor; pv_sid = actor; pv_kind = kind } ] }

let put_session w actor s =
  { w with w_sessions = (actor, s) :: List.remove_assoc actor w.w_sessions }

let get_session w actor = List.assoc_opt actor w.w_sessions

(* A capture is recorded in the world, not in a harness table outside it:
   `capture id as m1id` is a fact about the run, and keeping it inside the
   world is what lets step and judge stay pure functions of (world, input)
   -- which is the shape the Coq lift needs. *)
let bind w name t =
  (* A capture also *moves* any policy written against that name onto the
     message it now denotes.  Two spellings of "this message is secret"
     therefore work: a seeded message whose declared id is the name (the id
     and the interned name are the same aid), and a captured message whose
     policy was written before the capture ran.  Without the move, a policy
     keyed by a scenario-local name would be silently inert. *)
  let mid = snd t in
  let move_pair (m, l) = if m = name then (mid, l) else (m, l) in
  let move_triple (m, f, l) = if m = name then (mid, f, l) else (m, f, l) in
  { w with
    w_env = (name, t) :: List.remove_assoc name w.w_env;
    w_class = List.sort_uniq Stdlib.compare (List.map move_pair w.w_class);
    w_field_hidden =
      List.sort_uniq Stdlib.compare (List.map move_triple w.w_field_hidden) }

let resolve w name =
  match List.assoc_opt name w.w_env with
  | Some t -> Some t
  | None ->
      (match find_feed_of_id w.w_log name with
       | Some f -> Some (f, name)
       | None -> None)

let open_session w actor =
  let epoch = w.w_epoch + 1 in
  let w = { w with w_epoch = epoch } in
  let w = put_session w actor
      { ss_actor = principal w actor; ss_connected = true; ss_token = 0; ss_epoch = epoch
      ; ss_fresh = true; ss_renewed = false; ss_alias = "" } in
  presence w actor true "online"

let gate w actor f =
  match f.f_kind with
  | K_mailbox when f.feed_a <> actor -> Some "access denied"
  | _ ->
      let pr = principal w actor in
      if not (in_feed w pr f) then Some "access denied"
      else if is_banned w pr f then Some "banned"
      else None

(* ------------------------------------------------------------------ *)
(* the step machine                                                     *)
(*                                                                      *)
(* Total: every command yields a world and an observation, and a world   *)
(* that is unchanged wherever the action was refused.  Refusal is never  *)
(* an exception and never a rewrite of the log.                          *)
(* ------------------------------------------------------------------ *)

(* ------------------------------------------------------------------ *)
(* replay windows and pagination                                        *)
(* ------------------------------------------------------------------ *)

let default_page = 20

(* `List.nth_opt` raises on a negative index, so `nth xs (len xs - 1)` is not
   a safe "last element" for the empty case -- which is precisely what a
   version negotiation with nothing in common produces. *)
let last_opt = function [] -> None | xs -> Some (List.nth xs (List.length xs - 1))

let take_opt n xs =
  match n with None -> xs | Some k -> List.filteri (fun i _ -> i < k) xs

let drop_opt n xs =
  match n with None -> xs | Some k -> List.filteri (fun i _ -> i >= k) xs

let set_page w actor n =
  { w with w_pages = (actor, n) :: List.remove_assoc actor w.w_pages }

let get_page w actor = try List.assoc actor w.w_pages with Not_found -> 0

(* Missing ordinals inside the window a reader was actually handed.  Derived
   from the ordinals, never from a server-side gap counter: the superseded
   oracle signalled a gap by raising unconditionally when the reader asked
   for `after 0`, which conflated "from the beginning" with "there is a
   hole", and made every assertion downstream of it pass for free. *)
let gaps_in seqs =
  match seqs with
  | [] -> []
  | _ ->
      let lo = List.fold_left min max_int seqs in
      let hi = List.fold_left max min_int seqs in
      List.filter (fun n -> not (List.mem n seqs))
        (List.init (hi - lo + 1) (fun i -> lo + i))

(* Search in the model is a case-insensitive substring test over the body,
   not a ranked query: the scenarios assert *which* messages match, never
   their score, so a ranking function would be unobserved machinery. *)
let contains_sub hay needle =
  let hl = String.length hay and nl = String.length needle in
  nl = 0 || (hl >= nl
             && let rec go i = i + nl <= hl && (String.sub hay i nl = needle || go (i + 1)) in
             go 0)

(* A redelivery is two Post events with the same (feed, id): the truth fold
   keeps one message, the window shows the duplicate.  Both statements are
   true of the same log, which is the point of separating them. *)
let dup_ids w f ids =
  List.sort_uniq Int.compare
    (List.filter
       (fun m ->
         List.length
           (List.filter (fun e ->
              match e with
              | EvPost (f', m', _, _) -> feed_eq f f' && m' = m
              | _ -> false) w.w_log) > 1)
       ids)

(* Where a replay window starts.  `after cursor` with no cursor reads from
   position zero rather than erroring; `after next` continues the page the
   reader last took; `after last` is the head only. *)
let window_after w actor f bnd items =
  match bnd with
  | KB_seq n -> List.filter (fun ps -> ps.ps_seq > n) items
  | KB_cursor ->
      (match read_cursor w.w_log (principal w actor) f with
       | None -> items
       | Some c -> List.filter (fun ps -> ps.ps_seq > c) items)
  | KB_snapshot -> items
  | KB_next -> drop_opt (Some (get_page w actor)) items
  | KB_last ->
      (match items with
       | [] -> []
       | _ -> [ List.nth items (List.length items - 1) ])

(* Every feed the reader could see: those the log mentions, those the group
   table declares, and the reader's own mailbox.  Union, not a stored list,
   so a feed cannot be both deleted and readable. *)
let all_feeds w actor =
  let gs = List.filter_map
             (fun (_, g) -> if g.gr_exists && List.mem actor g.gr_members
                            then Some g.gr_feed else None)
             w.w_groups in
  let me = named_feed K_mailbox (principal w actor) in
  List.sort_uniq feed_cmp (me :: gs @ log_feeds w)

let step_query w actor q =
  (* At L1 there is no broker, so there is nothing to query: the honest
     answer is `unsupported`, printed as SKIP, not a green run of a
     statement the tier cannot express. *)
  let l2 ch k =
    if w.w_tier = T_l1 then refuse w actor ch "the query family is L2"
    else k ()
  in
  let inbox_of w actor f lim =
    match gate w actor f with
    | Some code -> w, fail actor Ch_inbox code
    | None ->
        let all = List.filter (fun ps -> feed_eq (fst ps.ps_ref) f) (pending w actor) in
        let page = take_opt lim all in
        let w = set_page w actor (List.length page) in
        w, paged actor Ch_inbox (List.map item_of page) all
  in
  match q with
  | Q_inbox (f, lim) -> l2 Ch_inbox (fun () -> inbox_of w actor f lim)
  | Q_inbox_cont ->
      l2 Ch_inbox (fun () ->
        let all = pending w actor in
        let off = get_page w actor in
        let page = take_opt (Some default_page) (drop_opt (Some off) all) in
        let w = set_page w actor (off + List.length page) in
        w, paged_from actor Ch_inbox off (List.map item_of page) all)
  | Q_events (f, bnd, lim) ->
      l2 Ch_events (fun () ->
        match gate w actor f with
        | Some code -> w, fail actor Ch_events code
        | None ->
            let win = window_after w actor f bnd (feed_window w actor f) in
            let page = take_opt lim win in
            let w = set_page w actor (List.length page) in
            let ids = List.map (fun ps -> snd ps.ps_ref) page in
            let gaps = gaps_in (List.map (fun ps -> ps.ps_seq) page) in
            let dups = dup_ids w f ids in
            w, { (obs actor Ch_events (List.map item_of page)) with
                   o_more = List.length win > List.length page;
                   o_state = [ ("gaps", Dint (List.length gaps))
                             ; ("duplicates", Dint (List.length dups)) ] })
  | Q_cursor (f, up) ->
      l2 Ch_events (fun () ->
        match gate w actor f with
        | Some code -> w, fail actor Ch_events code
        | None ->
            let head = feed_head w.w_log f in
            let upto = min up head in
            let w = app w (EvRead (principal w actor, f, upto)) in
            let w = focus_on w actor f in
            w, { (no_obs actor) with o_chan = Ch_events;
                   o_state = [ ("cursor", Dint upto) ] })
  | Q_home (lim, prev) ->
      l2 Ch_home (fun () ->
        let fs = all_feeds w actor in
        let unread f =
          List.length (List.filter (fun ps -> feed_eq (fst ps.ps_ref) f)
                         (pending w actor))
        in
        let all = List.map (fun f -> Itfeed { feed = f; unread = unread f }) fs in
        let page = take_opt lim all in
        let w = set_page w actor (List.length page) in
        let w = (match page with
                 | Itfeed { feed = f; _ } :: _ -> focus_on w actor f
                 | _ -> w) in
        w, { (obs actor Ch_home page) with
             o_more = List.length all > List.length page;
             o_state = (match prev with
                        | Some n -> [ ("preview", Dint n) ]
                        | None -> []) })
  | Q_home_cont ->
      l2 Ch_home (fun () ->
        let fs = all_feeds w actor in
        let off = get_page w actor in
        let unread f =
          List.length (List.filter (fun ps -> feed_eq (fst ps.ps_ref) f)
                         (pending w actor))
        in
        let all = List.map (fun f -> Itfeed { feed = f; unread = unread f }) fs in
        let page = take_opt (Some default_page) (drop_opt (Some off) all) in
        let w = set_page w actor (off + List.length page) in
        w, paged_from actor Ch_home off page all)
  | Q_roster ->
      l2 Ch_roster (fun () ->
        let names =
          try List.assoc (principal w actor) w.w_roster with Not_found -> []
        in
        w, obs actor Ch_roster (List.map (fun n -> Itname n) names))
  | Q_subs ->
      l2 Ch_subs (fun () ->
        let names =
          try List.assoc (principal w actor) w.w_subs with Not_found -> []
        in
        w, obs actor Ch_subs (List.map (fun n -> Itname n) names))
  | Q_groups ->
      l2 Ch_groups (fun () ->
        let gs = List.filter_map
                   (fun (_, g) ->
                     if g.gr_exists && List.mem (principal w actor) g.gr_members
                     then Some g.gr_name
                     else None) w.w_groups in
        w, obs actor Ch_groups (List.map (fun n -> Itname n) gs))
  | Q_members name ->
      l2 Ch_members (fun () ->
        match group_get w name with
        | None -> w, fail actor Ch_members "notFound"
        | Some g ->
            if not (List.mem (principal w actor) g.gr_members) then
              (w, fail actor Ch_members "access denied")
            else (w, obs actor Ch_members (List.map (fun n -> Itname n) g.gr_members)))
  | Q_moderation scope ->
      l2 Ch_moderation (fun () ->
        let gs = List.filter_map
                   (fun (_, g) ->
                     if g.gr_exists && g.gr_owner = Some (principal w actor)
                     then (match scope with
                           | Some f -> if feed_eq g.gr_feed f then Some g.gr_name else None
                           | None -> Some g.gr_name)
                     else None) w.w_groups in
        w, obs actor Ch_moderation (List.map (fun n -> Itname n) gs))
  | Q_search (fscope, text, lim) ->
      l2 Ch_search (fun () ->
        let fs = (match fscope with
                  | None -> all_feeds w actor
                  | Some f -> [ f ])
        in
        let hits =
          List.concat_map (fun f -> feed_window w actor f) fs
          |> List.filter (fun ps ->
               (* X.422.2 searches the payload, so a term in a field is a hit
                  exactly as a term in the body is.  Restricting it to the body
                  is what made the corpus's "draft is found" row vacuous: the
                  word lives in the subject. *)
               let hay =
                 (match ps.ps_payload.pp_body with
                  | Some b -> [ b ]
                  | None -> [])
                 @ List.map (fun (_, d) -> datum_text d) ps.ps_payload.pp_fields
               in
               List.exists
                 (fun s -> contains_sub (String.lowercase_ascii s)
                             (String.lowercase_ascii text)) hay)
        in
        let page = take_opt lim hits in
        let w = set_page w actor (List.length page) in
        w, paged actor Ch_search (List.map item_of page) hits)
  | Q_search_cont ->
      l2 Ch_search (fun () ->
        let off = get_page w actor in
        let fs = all_feeds w actor in
        let hits = List.concat_map (fun f -> feed_window w actor f) fs in
        let page = take_opt (Some default_page) (drop_opt (Some off) hits) in
        let w = set_page w actor (off + List.length page) in
        w, paged_from actor Ch_search off (List.map item_of page) hits)
  | Q_discover scope ->
      l2 Ch_discovery (fun () ->
        let feats =
          (match scope with
           | "feed" | "home" -> [ "query"; "events"; "home" ]
           | "group" -> [ "roster"; "members"; "moderation" ]
           | "moderation" -> [ "ban"; "unban"; "add"; "remove" ]
           | "auth" -> [ "token"; "renew"; "resume" ]
           | _ -> w.w_features)
        in
        (* Discovery reports what the model implements, and nothing more:
           `expect feature X` is refutable precisely because this list is
           finite and written down. *)
        w, { (obs actor Ch_discovery (List.map (fun f -> Itflag f) feats)) with
             o_state = [ ("server", Datom "model"); ("scope", Datom scope) ] })

let step_raw w actor cmd =
  match cmd with
  | C_connect peer ->
      let fresh = match get_session w actor with Some x -> x.ss_token = 0 | None -> true in
      let w = open_session w actor in
      let w = (match peer with
               | Some p -> focus_on w actor (private_feed actor p)
               | None -> w) in
      (* `connect` is what establishes a session incarnation, so it is what
         the `session created` / `same session` pair is really about.
         Reporting only an epoch left that claim unjudgeable; the epoch stays
         in the state for anyone who wants the number. *)
      w, { (no_obs actor) with o_chan = Ch_auth;
             o_items = [ Itflag "connected" ];
             o_state = [ ("epoch", Dint w.w_epoch)
                       ; ((if fresh then "session created" else "same session"),
                          Datom "true") ] }
  | C_disconnect ->
      let w = (match get_session w actor with
               | Some s -> put_session w actor { s with ss_connected = false }
               | None -> w) in
      let w = presence w actor false "offline" in
      w, { (no_obs actor) with o_chan = Ch_presence; o_items = [ Itflag "offline" ] }
  | C_reconnect ->
      (* Recovery keeps the epoch when the identity already held a token: that
         is what `expect same session` measures, and it is measured in epochs,
         never in token strings. *)
      let same = match get_session w actor with
        | Some s -> s.ss_token > 0
        | None -> false
      in
      let w =
        if same then
          (match get_session w actor with
           | Some s -> put_session w actor { s with ss_connected = true
                                           ; ss_fresh = false }
           | None -> open_session w actor)
        else open_session w actor
      in
      w, { (no_obs actor) with o_chan = Ch_auth;
             o_state = [ ((if same then "same session" else "session created"),
                          Datom "true") ] }
  | C_auth a ->
      (match a with
       | KA_vsn list ->
           (* Version negotiation picks the highest mutually supported label.
              The ordering is lexical because the protocol names versions
              v1..vn; a scenario that offers nothing in common is refused
              rather than silently falling back to v1. *)
           let common = List.sort String.compare
                        (List.filter (fun v -> List.mem v w.w_supported) list) in
           (match last_opt common with
            | None -> w, fail actor Ch_auth "no common version"
            | Some sel ->
                let w = { w with w_selected = Some sel; w_vsn = sel } in
                w, { (no_obs actor) with o_chan = Ch_auth;
                       o_state = [ ("selectedVsn", Datom sel) ] })
       | KA_resume ->
           (match get_session w actor with
            | Some s when s.ss_token > 0 ->
                let w = put_session w actor { s with ss_connected = true
                                            ; ss_fresh = false } in
                (* A resumed session is the same incarnation *with its token
                   still in hand* -- which is the only reason `expect access
                   token` after `auth resume` is a claim about the protocol
                   rather than about the harness. *)
                w, { (no_obs actor) with o_chan = Ch_auth;
                       o_state = [ ("same session", Datom "true")
                                 ; ("access token", Dint s.ss_token)
                                 ; ("authenticated", Datom "true") ] }
            | _ ->
                let w = open_session w actor in
                w, { (no_obs actor) with o_chan = Ch_auth;
                       o_state = [ ("session created", Datom "true") ] })
       | KA_password _ | KA_token _ | KA_bare | KA_method _ ->
           (* The model accepts credentials and mints an opaque token.  It
              verifies no signature: `auth` is an action whose effect is a
              session, and that boundary is stated rather than assumed. *)
           let tok = w.w_token + 1 in
           let w = { w with w_token = tok } in
           let w = (match get_session w actor with
                    | Some s -> put_session w actor
                        { s with ss_connected = true; ss_token = tok }
                    | None ->
                        let w = open_session w actor in
                        match get_session w actor with
                        | Some s -> put_session w actor { s with ss_token = tok }
                        | None -> w) in
           w, { (no_obs actor) with o_chan = Ch_auth;
                  o_state = [ ("authenticated", Datom "true")
                            ; ("access token", Dint tok) ] })
  | C_renew ->
      (* Renewing rotates the token and leaves the epoch alone: a refresh is
         not a new session, and conflating them is how "expect same session"
         becomes vacuously true. *)
      let tok = w.w_token + 1 in
      let w = { w with w_token = tok } in
      let w = (match get_session w actor with
               | Some s -> put_session w actor { s with ss_token = tok
                                                ; ss_renewed = true }
               | None -> w) in
      w, { (no_obs actor) with o_chan = Ch_auth;
             o_state = [ ("access token refreshed", Dint tok) ] }
  | C_revoke ->
      let w = (match get_session w actor with
               | Some s -> put_session w actor
                   { s with ss_token = 0; ss_connected = false }
               | None -> w) in
      let w = presence w actor false "offline" in
      w, { (no_obs actor) with o_chan = Ch_auth;
             o_state = [ ("revoked", Datom "true") ] }
  | C_post (kf, p, cap) ->
      (match resolve_feed w actor kf with
       | None -> w, fail actor Ch_mutation "no feed in scope"
       | Some f ->
           if w.w_tier = T_l1 && f.f_kind = K_mailbox then
             refuse w actor Ch_mutation "mailbox is not an L1 feed"
           else match gate w actor f with
             | Some code -> w, fail actor Ch_mutation code
             | None ->
                 if not (wf_payload p) then (w, fail actor Ch_mutation "malformed payload")
                 else
                   let mid = w.w_next_mid in
                   let w = { w with w_next_mid = mid + 1 } in
                   let w = ensure_feed w f in
                   let w = app w (EvPost (f, mid, principal w actor, p)) in
                   let w = (match cap with
                             | Some name -> bind w name (f, mid)
                             | None -> w) in
                   let w = focus_on w actor f in
                   let n = match feed_seq w.w_log f mid with
                     | Some n -> n | None -> 0 in
                   w, { (obs actor Ch_mutation
                           [ Itmsg { ps_ref = (f, mid); ps_seq = n
                                   ; ps_author = actor; ps_payload = p } ]) with
                          o_state = [ ("id", Dint mid); ("seq", Dint n) ] })
  | C_read (kf, up) ->
      (match (match kf with
              | None ->
                  (* A read names exactly one feed: an explicit target, or the
                     feed in scope.  Guessing the mailbox instead would mark
                     one feed read while the inbox shows several, which is a
                     worse lie than refusing; `read for last` after a query
                     reads what that query put in scope. *)
                  List.assoc_opt actor w.w_focus
              | Some f -> resolve_feed w actor f) with
       | None -> w, fail actor Ch_mutation "no feed in scope"
       | Some f ->
           match gate w actor f with
           | Some code -> w, fail actor Ch_mutation code
           | None ->
               (* A read clamps to the head: `read up to 99` in a 3-message
                  feed sets the cursor at 3 rather than inventing a position
                  beyond the truth. *)
               let head = feed_head w.w_log f in
               let upto = (match up with Some n -> min n head | None -> head) in
               let w = app w (EvRead (principal w actor, f, upto)) in
               let w = focus_on w actor f in
               w, { (no_obs actor) with o_chan = Ch_mutation;
                      o_state = [ ("cursor", Dint upto) ] })
  | C_typing _ ->
      (* Typing writes to the presence stream and nowhere else.  That single
         line is the whole content of "presence cannot disturb replay". *)
      let w = presence w actor true "typing" in
      w, { (no_obs actor) with o_chan = Ch_presence; o_items = [ Itflag "typing" ] }
  | C_ack m ->
      (match resolve w m with
       | None -> w, fail actor Ch_acks "unknown message"
       | Some (f, mid) ->
           (* Ack is idempotent and address-shaped: (feed, id), not a bare id,
              because X.422.1 Ack carries the table it refers to.  A second
              ack of the same message adds nothing, which is the at-least-once
              claim in executable form. *)
           let e = EvAck (principal w actor, mid) in
           let w = if List.exists (fun x -> x = e) w.w_log then w else app w e in
           let w = { w with w_acks =
                 if List.mem (actor, mid) w.w_acks then w.w_acks
                 else (actor, mid) :: w.w_acks } in
           let w = focus_on w actor f in
           w, { (no_obs actor) with o_chan = Ch_acks; o_items = [ Itflag "ack" ] })
  | C_edit (m, mut) ->
      (match resolve w m with
       | None -> w, fail actor Ch_mutation "unknown message"
       | Some t ->
           match final_state w.w_log t with
           | Some MS_dead -> w, fail actor Ch_mutation "deleted"
           | None -> w, fail actor Ch_mutation "unknown message"
           | Some (MS_live p) ->
               (* Mutation addresses an existing message; the payload it
                  produces still has to be well-formed, so an edit that would
                  empty the body is refused rather than recorded. *)
               let p' = (match mut with
                         | KM_body s -> { p with pp_body = Some s }
                         | KM_field (n, d) -> set_field p n d) in
               if not (wf_payload p') then (w, fail actor Ch_mutation "malformed payload")
               else
                 let w = app w (EvEdit (fst t, snd t, p')) in
                 let author = match find_author w.w_log t with
                   | Some a -> a | None -> actor in
                 let n = match feed_seq w.w_log (fst t) (snd t) with
                   | Some n -> n | None -> 0 in
                 w, { (obs actor Ch_mutation
                         [ Itmsg { ps_ref = t; ps_seq = n
                                 ; ps_author = author; ps_payload = p' } ]) with
                        o_state = [ ("updated", Datom "true") ] })
  | C_delete m ->
      (match resolve w m with
       | None -> w, fail actor Ch_mutation "unknown message"
       | Some t ->
           (* Delete is absorbing and idempotent: deleting a dead message is
              accepted, because the requester's intent -- it must not be
              readable -- is already satisfied.  The log keeps both Delete
              events; the fold gives one answer. *)
           let w = app w (EvDelete (fst t, snd t)) in
           w, { (no_obs actor) with o_chan = Ch_mutation;
                  o_state = [ ("deleted", Datom "true") ] })
  | C_group_new name ->
      (match group_get w name with
       | Some g when g.gr_exists -> w, fail actor Ch_mutation "already exists"
       | _ ->
           let f = named_feed K_group name in
           let g = { gr_name = name; gr_feed = f
                     ; gr_owner = Some (principal w actor)
                   ; gr_members = [ actor ]; gr_banned = []; gr_exists = true } in
           let w = group_put w name g in
           let w = focus_on w actor f in
           w, { (no_obs actor) with o_chan = Ch_mutation;
                  o_items = [ Itflag "group created" ]
                ; o_state = [ ("feed", Dint name) ] })
  | C_group_del name ->
      (match group_get w name with
       | None -> w, fail actor Ch_mutation "notFound"
       | Some g ->
           if g.gr_owner <> Some (principal w actor) then
             deny w actor Ch_mutation "access denied"
           else
             (* The container goes; the log stays.  Deleting a group does not
                retroactively unreise its messages, and the model says so by
                construction rather than by comment: no branch here touches
                w_log. *)
             let w = group_put w name { g with gr_exists = false; gr_members = [] } in
             w, { (no_obs actor) with o_chan = Ch_mutation;
                    o_state = [ ("deleted", Datom "true") ] })
  | C_add (x, what) ->
      (match what with
       | KA_group name ->
           (match group_get w name with
            | None -> w, fail actor Ch_members "notFound"
            | Some g ->
                if g.gr_owner <> Some (principal w actor) then
                  deny w actor Ch_members "access denied"
                else if List.mem x g.gr_members then
                  (* idempotent: a second add is not a second membership *)
                  w, { (no_obs actor) with o_chan = Ch_members;
                         o_state = [ ("unchanged", Datom "true") ] }
                else
                  let w = group_put w name { g with gr_members = x :: g.gr_members } in
                  w, { (no_obs actor) with o_chan = Ch_members;
                         o_items = [ Itname x ] })
       | KA_roster ->
           let w =
             { w with w_roster = add_to (principal w actor) x w.w_roster } in
           w, { (no_obs actor) with o_chan = Ch_roster; o_items = [ Itname x ] })
  | C_remove (x, what) ->
      (match what with
       | KA_group name ->
           (match group_get w name with
            | None -> w, fail actor Ch_members "notFound"
            | Some g ->
                (* an owner may remove anyone; a member may remove itself.
                   Anything else is denied, and denial leaves the roster
                   untouched. *)
                if g.gr_owner <> Some (principal w actor) && x <> principal w actor then
                  w, fail actor Ch_members "access denied"
                else
                  let w = group_put w name
                      { g with gr_members = List.filter (fun y -> y <> x) g.gr_members } in
                  w, { (no_obs actor) with o_chan = Ch_members;
                         o_state = [ ("removed", Datom "true") ] })
       | KA_roster ->
           let w =
             { w with w_roster = drop_from (principal w actor) x w.w_roster } in
           w, { (no_obs actor) with o_chan = Ch_roster;
                  o_state = [ ("removed", Datom "true") ] })
  | C_ban (x, scope, on) ->
      (match scope with
       | Some name ->
          (match group_get w name with
            | None -> w, fail actor Ch_moderation "notFound"
            | Some g ->
                if g.gr_owner <> Some (principal w actor) then
                  deny w actor Ch_moderation "access denied"
                else
                  let banned =
                    if on then List.sort_uniq Int.compare (x :: g.gr_banned)
                    else List.filter (fun y -> y <> x) g.gr_banned
                  in
                  (* A ban is policy and nothing else: it touches neither the
                     log nor the membership table.  `is_banned` is the gate
                     that refuses the next post, and an unban undoes exactly
                     the ban -- which is why "ban does not delete" and "unban
                     does not lose a member" need no test case: no branch here
                     rewrites a fact, and the truth layer is not in scope. *)
                  let w = group_put w name { g with gr_banned = banned } in
                  let w = { w with w_ban =
                        (if on then (x, Some name) :: w.w_ban
                         else List.filter (fun (a, s) -> not (a = x && s = Some name)) w.w_ban) } in
                  w, { (no_obs actor) with o_chan = Ch_moderation;
                         o_state = [ ((if on then "banned" else "unbanned"),
                                      Datom "true") ] })
       | None ->
           let w = { w with w_ban =
                 (if on then (x, None) :: w.w_ban
                  else List.filter (fun (a, s) -> not (a = x && s = None)) w.w_ban) } in
           w, { (no_obs actor) with o_chan = Ch_moderation;
                  o_state = [ ((if on then "banned" else "unbanned"),
                               Datom "true") ] })
  | C_query q -> step_query w actor q
  | C_bootstrap (lim, prev) ->
      step_query w actor (Q_home (lim, prev))
  | C_authority (meth, cert) ->
      (* L1 has no broker: the local authority table is the trust anchor.
         At L2 the same statement is not a failure but a category error,
         so it reports `unsupported`, which the runner prints as SKIP. *)
      if w.w_tier = T_l2 then refuse w actor Ch_authority "authority is an L1 construct"
      else
        let id = (match cert with Some c -> c | None -> actor) in
        let tbl =
          match meth with
          | "announce" -> w.w_authority
          | "register" | "authenticate" -> add_to meth id w.w_authority
          | "dismiss" -> drop_from meth id w.w_authority
          | _ -> w.w_authority
        in
        let w = { w with w_authority = tbl } in
        let st = match meth with
          | "authenticate" -> [ ("authenticated", Datom "true") ]
          | m -> [ ("authority", Datom m) ]
        in
        w, { (no_obs actor) with o_chan = Ch_authority;
               o_items = [ Itflag meth ]; o_state = st }

let step w actor cmd =
  let w = stamp_before w actor in
  step_raw w actor cmd

(* ------------------------------------------------------------------ *)
(* probes: `when`, which decides without doing                          *)
(* ------------------------------------------------------------------ *)

(* A probe answers "is this principal allowed to", and it is the only path
   in the model that produces an access verdict without a world change.
   Keeping it total (world -> obs, not world -> world * obs) is what makes
   "the policy probe did not itself read the feed" a typing property. *)
let probe w actor p =
  let allowed f =
    if in_feed w (principal w actor) f
    && not (is_banned w (principal w actor) f) then
      { (no_obs actor) with o_chan = Ch_access }
    else fail actor Ch_access "access denied"
  in
  match p with
  | P_sends -> (match List.assoc_opt actor w.w_focus with
                | Some f -> allowed f
                | None -> fail actor Ch_access "no feed in scope")
  | P_inbox | P_home ->
      (if List.exists (fun f -> in_feed w (principal w actor) f) (all_feeds w actor)
      then
         { (no_obs actor) with o_chan = Ch_access }
       else fail actor Ch_access "access denied")
  | P_events f | P_reads f | P_search f -> allowed f

(* ------------------------------------------------------------------ *)
(* judgments: `expect`, evaluated                                         *)
(*                                                                      *)
(* evaluate returns a verdict, not a boolean.  Skip is a first-class     *)
(* answer: a construct the model does not implement reports SKIP and     *)
(* fails the run's exit code, so a green column can never be produced by *)
(* an assertion that measured nothing.                                   *)
(* ------------------------------------------------------------------ *)

type verdict =
  | Pass
  | Fail of string
  | Skip of string

(* The anti-vacuity rule, stated once.  The superseded oracle let a reply
   that never carried a message channel satisfy `expect not message ...`:
   the negation of "found" over a nonexistent collection is `true`, so the
   gate passed while asserting nothing, and it did so on the very scenario
   that was supposed to catch a gap.  Here a rejected or unsupported reply
   makes every content judgment -- positive or negative -- fail, and the
   reason string says why. *)
let blocked o =
  match o.o_out with
  | Accepted -> false
  | Rejected _ | Unsupported _ -> true

let why_blocked o =
  match o.o_out with
  | Rejected code -> "reply was rejected (" ^ code ^ "), so a content expectation cannot be judged"
  | Unsupported f -> "reply is unsupported at this tier (" ^ f ^ ")"
  | Accepted -> "no channel"

let messages_in o =
  List.filter_map (fun it -> match it with Itmsg ps -> Some ps | _ -> None) o.o_items

let flags_in o =
  List.filter_map (fun it -> match it with Itflag s -> Some s | _ -> None) o.o_items

let names_in o =
  List.filter_map (fun it -> match it with Itname n -> Some n | _ -> None) o.o_items

let unread_in o =
  List.fold_left
    (fun acc it -> match it with Itfeed { unread = u; _ } -> acc + u | _ -> acc)
    0 o.o_items

let state_of o k = List.assoc_opt k o.o_state

(* Error codes on an observation are protocol enumerations (`notFound`,
   "access denied", "gap"), not prose, so that `expect error notFound` can
   name them; report strings inside a verdict remain prose. *)
let cmp_ok n c =
  match c with
  | KCeq k -> n = k
  | KCle k -> n <= k
  | KCgt k -> n > k
  | KCnonempty -> n > 0
  | KCplain -> n > 0

(* Does a queued message match an `expect message` body?  Matching is on the
   payload the reader actually receives -- masked fields already removed --
   which is why a visibility claim and a delivery claim are the same test
   viewed from different sides. *)
let matches_body ps from body fields =
  (match from with None -> true | Some a -> ps.ps_author = a)
  && (match body with None -> true | Some b ->
        match ps.ps_payload.pp_body with
        | Some x -> String.equal x b
        | None -> false)
  && List.for_all
       (fun (name, dv) ->
         match field_value ps.ps_payload name with
         | Some d -> datum_eq d dv
         | None -> false)
       fields

(* Two layers, because only one kind of expectation has a witness.

   `judge` decides every assertion that does not consume a mailbox message
   and returns a bare verdict.  `evaluate` adds the consuming case: an
   `expect message` must hand back the message ids it matched, so that the
   runner can mark them taken.  Without that, one post in the mailbox would
   satisfy an unlimited chain of `expect message` statements, and the second
   one should have failed.                                        *)
(* The mailbox pool an `expect message` ranges over, or None when the last
   step produced no readable channel at all.  Both `judge` and `evaluate`
   need it, and only this function decides whether a step is blocked, so the
   anti-vacuity rule cannot drift between the verdict and its witnesses. *)
let msg_pool w o from body fields =
  let actor = o.o_actor in
  if blocked o then None
  else Some (List.filter (fun ps -> matches_body ps from body fields) (pending w actor))

let judge w o j =
  let actor = o.o_actor in
  match j with
  | J_msg { from; neg; inbound; body; fields } ->
      let _ = inbound in
      (match msg_pool w o from body fields with
       | None -> Fail "no readable reply to match against"
       | Some pool ->
           if neg then if pool = [] then Pass
                      else Fail "message present, expected absent"
           else if pool = [] then Fail "no matching message in the mailbox"
           else Pass)
  | J_vis { m; field; hidden } ->
      if blocked o then Fail (why_blocked o)
      else
        (match resolve w m with
        | None -> Fail "unknown message"
        | Some t ->
            let present =
              List.exists (fun it -> match it with
                        | Itmsg ps ->
                            snd ps.ps_ref = snd t
                            && (match field with
                                | None -> true
                                | Some f -> field_value ps.ps_payload f <> None)
                        | _ -> false) o.o_items
            in
            if hidden then
              (if not present then Pass
               else Fail "field is visible, expected hidden")
            else
              (if present then Pass else Fail "message or field not visible"))
  | J_field (m, f, dv) ->
      if blocked o then Fail (why_blocked o)
      else
        (* The reply is what this reader was shown; the log is what exists.
           A field present in the log but absent from the reply is masked,
           and that distinction *is* field-level visibility. *)
        (match resolve w m with
         | None -> Fail "unknown message"
         | Some t ->
             let in_reply =
               List.find_opt
                 (fun it -> match it with
                            | Itmsg ps -> mref_eq ps.ps_ref t
                            | _ -> false)
                 o.o_items
             in
             match in_reply with
             | Some (Itmsg ps) ->
                 (match field_value ps.ps_payload f with
                  | Some d -> if datum_eq d dv then Pass
                              else Fail "field value differs in the reply"
                  | None -> Fail "field absent from the reply (masked or unset)")
             | _ ->
                 (match final_state w.w_log t with
                  | Some (MS_live p) ->
                      (match field_value p f with
                       | Some d -> if datum_eq d dv then Pass
                                   else Fail "field value differs in the log"
                       | None -> Fail "field absent from the log")
                  | _ -> Fail "message is not live"))
  | J_ack m ->
      (match resolve w m with
       | None -> Fail "unknown message"
       | Some (_, mid) ->
           if List.mem (actor, mid) w.w_acks then Pass
           else Fail "not acknowledged")
  | J_state k ->
      (match state_of o k with
       | Some _ -> Pass
       | None ->
           (* `same session` and `session created` are epoch facts, and they
              are judged from the observation the command produced, never
              from a mutable harness flag. *)
           match k with
           | "same session" ->
               (match get_session w actor with
                | Some s when s.ss_epoch = w.w_epoch -> Pass
                | _ -> Fail "epoch differs")
           | "authenticated" ->
               if (match get_session w actor with Some s -> s.ss_token > 0 | None -> false)
               then Pass else Fail "no session token"
           | "session created" ->
               (match get_session w actor with
                | Some s when s.ss_fresh -> Pass
                | Some _ -> Fail "the incarnation was carried over, not created"
                | None -> Fail "no session")
           | "access token" ->
               (match get_session w actor with
                | Some s when s.ss_token > 0 -> Pass
                | _ -> Fail "no session token")
           | "access token refreshed" ->
               (match get_session w actor with
                | Some s when s.ss_renewed && s.ss_token > 0 -> Pass
                | Some _ -> Fail "the token was never rotated"
                | None -> Fail "no session")
           | _ -> Fail ("state not reported: " ^ k))
  | J_event { fam; kind; actor = pa; up_to; m; seq } ->
      let subject = match pa with Some a -> a | None -> actor in
      let msel = (match m with
                  | None -> fun _ -> true
                  | Some name ->
                      fun e ->
                        match resolve w name with
                        | Some (_, mid) ->
                            (match e with
                             | EvPost (_, m2, _, _) | EvEdit (_, m2, _)
                             | EvDelete (_, m2) -> m2 = mid
                             | _ -> false)
                        | None -> false)
      in
      let msg_fam () =
        match kind with
        | "received" ->
            List.exists (fun e -> match e with
                          | EvPost (_, _, a, _) when msel e -> a = subject
                          | _ -> false) w.w_log
        | "delivered" ->
            List.exists
              (fun e ->
                match e with
                | EvPost (f, _, a, _) when msel e && a = subject ->
                    List.exists (fun x -> x <> subject) (feed_members w f)
                    || (match feed_members w f with _ :: _ -> true | [] -> false)
                | _ -> false) w.w_log
        | "read" ->
            (* A read event carries (principal, feed, cursor).  The judgment
               asks the cursor to have reached `up_to`, which is a claim about
               the log, not a flag on the session. *)
            List.exists
              (fun e ->
                match e with
                | EvRead (a, _, c) ->
                    a = subject && (match up_to with Some n -> c >= n | None -> c > 0)
                | _ -> false) w.w_log
        | "edited" | "updated" ->
            List.exists (fun e -> match e with EvEdit _ -> msel e | _ -> false) w.w_log
        | "deleted" ->
            List.exists (fun e -> match e with EvDelete _ -> msel e | _ -> false) w.w_log
        | _ -> false
      in
      let presence_fam () =
        (* The presence stream is the only place these kinds exist, and it is
           disjoint from the message log by construction. *)
        List.exists
          (fun pv -> (pv.pv_actor = subject || pv.pv_sid = subject) && pv.pv_kind = kind)
          w.w_pstream
        || (match kind with
            | "online" -> is_online w subject || online_as w subject
            | "offline" -> not (is_online w subject || online_as w subject)
            | _ -> false)
      in
      let seq_case () =
        match seq with
        | None -> false
        | Some n ->
            List.exists
              (fun f ->
                match feed_seq w.w_log f (match m with Some x -> x | None -> 0) with
                | Some k -> k = n
                | None -> false)
              (log_feeds w)
      in
      if fam = "presence" then
        (if presence_fam () then Pass else Fail ("presence event absent: " ^ kind))
      else if seq_case () then Pass
      else if msg_fam () then Pass
      else Fail ("message event absent: " ^ kind)
  | J_access want ->
      if o.o_chan <> Ch_access then Fail "no access decision was made by the last step"
      else
        let got = match o.o_out with Accepted -> true | _ -> false in
        if got = want then Pass
        else Fail (if want then "access was denied" else "access was allowed")
  | J_error (code, neg) ->
      let got = match o.o_out with Rejected c -> Some c | _ -> None in
      if neg then (if got = Some code then Fail ("error " ^ code ^ " was raised") else Pass)
      else
        (match got with
         | Some c when String.equal c code -> Pass
         | Some c -> Fail ("error " ^ c ^ " instead of " ^ code)
         | None -> Fail ("expected error " ^ code))
  | J_coll { what; cmp; neg } ->
      if blocked o then Fail (why_blocked o)
      else
        let n =
          match what with
          | "items" | "result items" -> List.length o.o_items
          | "messages" -> List.length (messages_in o)
          | "feeds" | "previews" ->
              List.length (List.filter_map (fun it ->
                match it with Itfeed _ -> Some () | _ -> None) o.o_items)
          | "unread" -> unread_in o
          | "events" -> List.length (messages_in o)
          | "roster" | "moderation" | "groups" | "members" | "subscriptions" ->
              List.length (names_in o)
          | "mentions" ->
              (* The X.422.2 text names mentions but never says how they are
                 counted.  The model refuses to guess: this reports SKIP. *)
              (-1)
          | "replay" ->
              let ids = List.map (fun it -> match it with
                                  | Itmsg ps -> Some (snd ps.ps_ref) | _ -> None) o.o_items
              in
              let ids = List.filter_map (fun x -> x) ids in
              List.length ids
                - List.length (List.sort_uniq Int.compare ids)
          | _ -> (-1)
        in
        if n < 0 then Skip ("collection not modelled: " ^ what)
        else
          (* Two readings of the bare form, because the two nouns differ.
             "expect roster" names a *structure*: the reply was a roster, and
             an empty one still is one.  It is refutable because a refused,
             unknown or unsupported reply is `blocked` and fails above, and
             because `expect not roster` denies it -- and because the channel
             has to be the one that answers that query.
             "expect result items" names *content*: there is at least one.
             An empty inbox answering "items" is the vacuous green the Python
             oracle was built on, so counts keep demanding a witness. *)
          let shape = match what with
            | "roster" -> Some Ch_roster
            | "groups" -> Some Ch_groups
            | "subscriptions" -> Some Ch_subs
            | "members" -> Some Ch_members
            | "moderation" -> Some Ch_moderation
            | _ -> None
          in
          let ok =
            match cmp, shape with
            | KCplain, Some c -> o.o_chan = c
            | _ -> cmp_ok n cmp
          in
          if (if neg then not ok else ok) then Pass
          else Fail (what ^ " counted " ^ string_of_int n
                     ^ (if neg then " but the negated comparison held" 
                        else " and the comparison failed"))
  | J_flag s ->
      (match s with
       | "more" -> if o.o_more then Pass else Fail "reply was not truncated"
       | "not more" -> if not o.o_more then Pass else Fail "reply reported more"
       | "next" | "snapshot" | "shared snapshot" ->
           (match state_of o s with Some _ -> Pass | None -> Skip ("flag not reported: " ^ s))
       | "no gaps" ->
           let seqs = List.map (fun ps -> ps.ps_seq) (messages_in o)
           in
           if gaps_in seqs = [] then Pass
           else Fail ("gaps at " ^ string_of_int (List.length (gaps_in seqs)) ^ " ordinals")
       | "no duplicates" | "no duplicate feeds" ->
           let ids = List.map (fun ps -> snd ps.ps_ref) (messages_in o)
           in
           let dups = List.length ids - List.length (List.sort_uniq Int.compare ids) in
           if dups = 0 then Pass else Fail (string_of_int dups ^ " duplicates")
       | _ -> Skip ("flag not modelled: " ^ s))
  | J_rel { actor = x; kind; neg } ->
      (* These claims are about the *current session's* tables: the surface
         form carries no owner, so the elaborator binds them to whoever is
         speaking.  `in moderation` is not a contact list -- it says that a
         principal I moderate has banned somebody in one of my groups. *)
      let got = match kind with
        | "roster" -> mem_tbl (principal w actor) x w.w_roster
        | "subscriptions" -> mem_tbl (principal w actor) x w.w_subs
        | "moderation" ->
            List.exists
              (fun (b, sc) ->
                b = x
                && (match sc with
                   | Some g -> (match group_get w g with
                               | Some gr ->
                                   gr.gr_exists
                                   && gr.gr_owner = Some (principal w actor)
                               | None -> false)
                   | None -> false)) w.w_ban
        | _ -> false
      in
      if neg then (if got then Fail "relation present" else Pass)
      else if got then Pass else Fail "relation absent"
  | J_ban (x, scope) ->
      (* Being banned and being a member are different facts about the same
         principal, asked separately and neither implying the other. *)
      let global = List.exists (fun (a, s) -> a = x && s = None) w.w_ban in
      let scoped = (match scope with
                    | Some g -> List.exists (fun (a, s) -> a = x && s = Some g) w.w_ban
                    | None -> false)
      in
      if global || scoped then Pass else Fail "not banned"
  | J_exists (what, name) ->
      (match what with
       | "group" ->
           (match group_get w name with
            | Some g when g.gr_exists -> Pass
            | _ -> Fail "group does not exist")
       | _ -> Skip ("existence not modelled: " ^ what))
  | J_role (x, role, name) ->
      (match group_get w name with
       | None -> Fail "no such group"
       | Some g ->
           if role = "owner" then
             (if g.gr_owner = Some x then Pass else Fail "not the owner")
           else if List.mem x g.gr_members then Pass
           else Fail "not a member")
  | J_cursor (state, f) ->
      let fs = (match f with Some x -> [ x ] | None -> log_feeds w) in
      let changed =
        List.exists
          (fun fd ->
            let now = read_cursor w.w_log (principal w actor) fd in
            let then_ = (match stamped_cursor w actor fd with
                         | Some (_, _, c) -> Some c
                         | None -> None) in
            now <> then_)
          fs
      in
      (match state with
       | "unchanged" -> if changed then Fail "cursor moved" else Pass
       | "updated" -> if changed then Pass else Fail "cursor did not move"
       | _ -> Skip ("cursor state not modelled: " ^ state))
  | J_feature name ->
      let reported = List.mem name (flags_in o) in
      if reported then Pass
      else if List.mem name w.w_features then Pass
      else Fail ("feature not offered: " ^ name)
  | J_vsn v ->
      (match w.w_selected with
       | Some s when String.equal s v -> Pass
       | Some s -> Fail ("selected " ^ s)
       | None -> Fail "no version selected")

let evaluate w o j =
  (* (verdict, message ids this expectation consumes from the mailbox) *)
  match j with
  | J_msg { from; neg; inbound = _; body; fields } ->
      let v = judge w o j in
      if neg then (v, [])
      else
        (v,
         match msg_pool w o from body fields with
         | None -> []
         | Some pool -> List.map (fun ps -> snd ps.ps_ref) pool)
  | _ -> (judge w o j, [])

(* ------------------------------------------------------------------ *)
(* seeding: `given`, applied before the first action                      *)
(*                                                                        *)
(* Facts enter the world the only way anything else does -- through the   *)
(* log, or through the policy tables.  A seeded message is an `EvPost`,   *)
(* not a second mailbox, which is what keeps `message_state = fold        *)
(* events` true of a scenario that never sends anything.  Seeding is also *)
(* unmediated: `given` is ground truth about the world, so no gate runs,  *)
(* no clearance is checked and no ban is consulted.  A scenario that      *)
(* seeds an impossible state is a bad scenario, not an escape hatch.      *)
(* ------------------------------------------------------------------ *)

let consume w reader ids =
  let seen = (try List.assoc reader w.w_seen with Not_found -> []) in
  { w with
    w_seen =
      (reader, List.sort_uniq Stdlib.compare (seen @ ids))
      :: List.remove_assoc reader w.w_seen }

let rec apply_fact w (f : gfact) =
  match f with
  | GF_clearance (a, l) ->
      { w with w_clearance = (a, l) :: List.remove_assoc a w.w_clearance }
  | GF_branch (a, b) ->
      { w with w_branch = (a, b) :: List.remove_assoc a w.w_branch }
  | GF_feed_branch (feed, b) ->
      (* Feed branches share the branch table with principals.  The two are
         never looked up by the same key: a feed branch is consulted by feed
         name, a principal branch by actor. *)
      { w with w_branch = (feed, b) :: List.remove_assoc feed w.w_branch }
  | GF_org (a, o) -> { w with w_org = (a, o) :: List.remove_assoc a w.w_org }
  | GF_class (m, l) ->
      { w with w_class = (m, l) :: List.remove_assoc m w.w_class }
  | GF_field_level (m, fld, _hidden, lvl) ->
      (* The surface keyword records what the author believes the field does;
         the level records what the model enforces: a field is present for a
         reader only if that reader clears the level.  One rule, both
         spellings, so `visible at level secret` and `hidden at level
         confidential` cannot mean different things in different scenarios. *)
      { w with w_field_hidden = List.sort_uniq Stdlib.compare ((m, fld, lvl) :: w.w_field_hidden) }
  | GF_rel (a, kind, other) ->
      (match kind with
       | "subscription" -> { w with w_subs = add_to a other w.w_subs }
       | _ -> { w with w_roster = add_to a other w.w_roster })
  | GF_msg (feed, _seq, author, body, mid, alias) ->
      let w = ensure_feed w feed in
      let w = app w (EvPost (feed, mid, author, text_payload body)) in
      (match alias with Some n -> bind w n (feed, mid) | None -> w)
  | GF_read (a, feed, up_to) -> app w (EvRead (a, feed, up_to))
  | GF_exists (_what, name) ->
      (match group_get w name with
       | Some g -> group_put w name { g with gr_exists = true }
       | None ->
           group_put w name
             { gr_name = name; gr_feed = named_feed K_group name; gr_owner = None
             ; gr_members = []; gr_banned = []; gr_exists = true })
  | GF_role (a, role, name) ->
      let w = apply_fact w (GF_exists ("group", name)) in
      (match group_get w name with
       | Some g ->
           let g =
             if String.equal role "owner" then { g with gr_owner = Some a }
             else g
           in
           group_put w name { g with gr_members = List.sort_uniq Stdlib.compare (a :: g.gr_members) }
       | None -> w)
  | GF_notmember (a, name) ->
      let w = apply_fact w (GF_exists ("group", name)) in
      (match group_get w name with
       | Some g -> group_put w name { g with gr_members = List.filter (fun y -> y <> a) g.gr_members }
       | None -> w)
  | GF_ban (a, scope) -> { w with w_ban = (a, scope) :: w.w_ban }

