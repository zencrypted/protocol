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
  | Itmsg of { id : aid; actor : aid; seq : int; payload : payload }
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
  | Q_discover of string

type kcmd =
  | C_connect of aid option
  | C_disconnect
  | C_reconnect
  | C_auth of kauth
  | C_renew
  | C_revoke
  | C_post of feed * payload * aid option
  | C_read of feed option * int option
  | C_typing of aid
  | C_ack of aid
  | C_file of aid * aid option
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
  | KS_actor of aid
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
  ss_actor : aid;                 (* who this session speaks as           *)
  ss_connected : bool;
  ss_token : int;                 (* opaque token identity; regenerated by
                                     `renew`, preserved by `resume`        *)
  ss_epoch : int;                 (* session incarnation: `same session`
                                     compares epochs, never tokens         *)
  ss_alias : string;              (* surface name, for diagnostics only    *)
}

type pevent = { pv_actor : aid; pv_kind : string }

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
  w_sessions : (string * session) list;   (* keyed by surface alias         *)
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
  w_field_hidden = []; w_ban = []; w_sessions = []; w_presence = [];
  w_pstream = []; w_acks = []; w_seen = [];
  w_token = 0; w_epoch = 0;
  w_vsn = "v1"; w_supported = [ "v1" ]; w_selected = None; w_features = [];
  w_pages = []; w_last_cursor = []; w_authority = [];
  (* aid space: the interner hands out surface names from 1; protocol ids
     minted by a Post come from this disjoint range, so an interned alias can
     never be confused with a minted id, in either direction. *)
  w_next_mid = 1_000_000; w_env = [];
}

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
        if m = id && not (clears (clearance w reader) (Some lvl)) then Some fld
        else None)
      w.w_field_hidden
  in
  let fields = List.filter (fun (n, _) -> not (List.mem n drop)) payload.pp_fields in
  let body =
    if List.mem body_field drop then None else payload.pp_body
  in
  { pp_body = body; pp_fields = fields }

let readable w reader _payload id =
  clears (clearance w reader) (classification w id)

(* ---- feed construction ---- *)

let ensure_feed w f =
  match f.f_kind with
  | K_group ->
      if List.mem_assoc f.feed_a w.w_groups then w
      else { w with w_groups = (f.feed_a,
               { gr_name = f.feed_a; gr_feed = f; gr_owner = None
               ; gr_members = []; gr_banned = []; gr_exists = true }) :: w.w_groups }
  | _ -> w

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
        let keep = in_feed w reader f && not (List.mem m seen) && not dup in
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
