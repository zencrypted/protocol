(* lib/elaborator.ml -- surface AST -> kernel terms.

   This is the only pass that knows what a name *means*.  Everything
   downstream sees integers: identifiers interned from 1 upward, field names
   interned the same way ("body" excepted, it is field 0 by definition),
   message refs interned, feed kinds resolved against the acting principal.

   The elaboration invariant is the reason the Z.180 model is worth reading:

     no sugar survives into the kernel.

   Three surface spellings of a message reference (`id m1id`, `ref "doc"`,
   the bare `m1`) collapse into one aid; `send message to bob "hi"` and
   `send message to bob { body: "hi" }` collapse into one payload; `inbound`
   and `expect message` collapse into one judgment with a flag.  A second
   front-end (Z.120 textual MSC) can therefore be added as *another
   elaborator over the same kernel*, which is the only way two notations can
   be compared without also comparing two semantics.

   Tier gating deliberately does NOT happen here.  The kernel refuses the L2
   query family at run time and produces an `Unsupported` observation, which
   makes every content judgment over it fail.  Static rejection would let a
   scenario that cannot be satisfied disappear from the report instead of
   appearing in it.  One enforcement point, and it is the one the Coq model
   will carry.                                        *)

open Kernel
open Semantics
open Z180_syntax
open Ast

let ( let* ) = Result.bind

(* ---- interning ---- *)

type interner = { mutable cells : (string * aid) list; mutable next : aid }

(* Interned surface names occupy 1 upward; protocol ids minted by a post
   occupy 1_000_000 upward (see `empty_world`).  The ranges are disjoint by
   construction, so a name can never be mistaken for a minted id, and the
   kernel can resolve either through the same table without ambiguity. *)
let create () = { cells = []; next = 1 }

let intern t name =
  match List.assoc_opt name t.cells with
  | Some a -> a
  | None ->
      let a = t.next in
      t.cells <- (name, a) :: t.cells;
      t.next <- a + 1;
      a

(* Field names share the principal name space.  This is safe because the
   kernel never compares a field name with a principal: fields are looked up
   inside a payload, principals inside the world's tables.  "body" is the one
   exception, and it is not interned at all -- it *is* field 0. *)
let field_name t name = if String.equal name "body" then body_field else intern t name

let dump t = List.rev t.cells

(* ---- data ---- *)

let datum_of = function Vstr s -> Dtext s | Vint i -> Dint i | Vat a -> Datom a

(* A structured payload keeps its `body` in the kernel record's optional body
   slot and everything else as interned fields.  A payload with fields but no
   body is *not* repaired here: `wf_payload` refuses it at the gate, because
   inventing an empty body would turn a malformed message into a delivered
   one. *)
let payload_of t = function
  | Ptext s -> text_payload s
  | Pstruct fs ->
      let body_text = function
        | Vstr s -> Some s
        | Vint i -> Some (string_of_int i)
        | Vat a -> Some a
      in
      let body =
        List.find_map
          (fun (k, v) -> if String.equal k "body" then body_text v else None)
          fs
      in
      let fields =
        List.filter_map
          (fun (k, v) ->
            if String.equal k "body" then None else Some (field_name t k, datum_of v))
          fs
      in
      { pp_body = body; pp_fields = fields }

let body_of_payload t = function
  | Ptext s -> (Some s, [])
  | Pstruct fs ->
      let b =
        List.find_map
          (fun (k, v) ->
            if String.equal k "body" then
              match v with Vstr s -> Some s | Vint i -> Some (string_of_int i) | Vat a -> Some a
            else None)
          fs
      in
      let f =
        List.filter_map
          (fun (k, v) ->
            if String.equal k "body" then None else Some (field_name t k, datum_of v))
          fs
      in
      (b, f)

(* ---- addressing ---- *)

(* Every surface target needs the acting principal, because `peer bob` and a
   bare `bob` are session-relative: the same text denotes a different feed
   depending on who is speaking.  That is the whole reason addressing is
   elaborated and not looked up at run time. *)
(* A relative target -- `peer bob`, a bare `bob`, `private:bob` -- denotes a
   feed *anchored on the speaker*.  With no speaker yet declared there is no
   answer, and the honest one is an error rather than principal 0. *)
let anchored actor =
  if actor = no_principal then Error "no acting principal to anchor this target" else Ok ()

let target_feed t actor = function
  | Tpeer s -> let* () = anchored actor in Ok (private_feed actor (intern t s))
  | Tgroup g -> Ok (named_feed K_group (intern t g))
  | Tchan c -> Ok (named_feed K_chan (intern t c))
  | Tmailbox m -> Ok (named_feed K_mailbox (intern t m))
  | Tfeed { rf_kind; rf_name } -> (
      match String.lowercase_ascii rf_kind with
      | "private" -> let* () = anchored actor in Ok (private_feed actor (intern t rf_name))
      | "group" -> Ok (named_feed K_group (intern t rf_name))
      | "chan" -> Ok (named_feed K_chan (intern t rf_name))
      | "mailbox" -> Ok (named_feed K_mailbox (intern t rf_name))
      | k -> Error (Printf.sprintf "unknown feed kind %S" k))
  | Tpair (a, b) -> Ok (private_feed (intern t a) (intern t b))
  (* An address is an identity.  The model has no broker directory, so
     `bob@brokerB` interns as one principal rather than resolving through a
     table it would have to invent. *)
  | Taddr s -> Ok (private_feed actor (intern t s))
  | Tident s -> let* () = anchored actor in Ok (private_feed actor (intern t s))

let kfeed_of_target t actor t' =
  let* f = target_feed t actor t' in
  Ok (KF f)

(* A ban or a moderation query names a collection.  Anything that is not a
  named collection degrades to a global scope, which is what the surface form
  without `in group X` says. *)
let scope_aid t = function
  | Tgroup g -> Some (intern t g)
  | Tchan c -> Some (intern t c)
  | Tident s -> Some (intern t s)
  | _ -> None

(* The three message-reference spellings, collapsed.  If this function ever
   grows a case distinction, the elaboration invariant has been broken. *)
let msgref t = function Midl s | Mlitl s | Mrefl s -> intern t s

let boundary_of = function
  | Bseq n -> KB_seq n
  | Bcursor -> KB_cursor
  | Bsnapshot -> KB_snapshot
  | Bnext -> KB_next
  | Blast -> KB_last

let cmp_of = function
  | Ceq n -> KCeq n
  | Cle n -> KCle n
  | Cgt n -> KCgt n
  | Cnonempty -> KCnonempty
  | Cplain -> KCplain

(* ---- given ---- *)

let fact t actor = function
  | Fclearance { actor = a; level } -> Ok (GF_clearance (intern t a, level))
  | Fbranch { actor = a; branch } -> Ok (GF_branch (intern t a, branch))
  | Ffeed_branch { feed; branch } -> Ok (GF_feed_branch (intern t feed, branch))
  | Forg { actor = a; org } -> Ok (GF_org (intern t a, org))
  | Fclass { m; level } -> Ok (GF_class (intern t m, level))
  | Ffieldlevel { m; field; hidden; level } ->
      Ok (GF_field_level (intern t m, field_name t field, hidden, level))
  | Frel { actor = a; kind; other } ->
      Ok (GF_rel (intern t a, kind, intern t other))
  | Fmsg { feed; seq; from; body; mid; alias } ->
      let* f = target_feed t actor feed in
      let mid = intern t (match mid with Some s -> s | None -> "#" ^ string_of_int seq) in
      Ok (GF_msg (f, seq, intern t from, body, mid, Option.map (intern t) alias))
  | Fread { actor = a; feed; up_to } ->
      (* A read fact carries its own principal, so `private:alice` is relative
         to the reader named in the fact, not to whoever the session happens
         to be: `given bob read private:alice up to 1` means bob's view of the
         alice-bob feed even when it is written before any `session`. *)
      let ra = intern t a in
      let* f = target_feed t ra feed in
      Ok (GF_read (ra, f, up_to))
  | Fexists { what; name } -> Ok (GF_exists (what, intern t name))
  | Frole { actor = a; role; group } ->
      Ok (GF_role (intern t a, role, intern t group))
  | Fnotmember { actor = a; group } -> Ok (GF_notmember (intern t a, intern t group))
  | Fban { actor = a; scope } ->
      Ok (GF_ban (intern t a, Option.join (Option.map (scope_aid t) scope)))

(* ---- commands ---- *)

let rec cmd t actor = function
  | Cconnect peer -> Ok (C_connect (Option.map (intern t) peer))
  | Cdisconnect -> Ok C_disconnect
  | Creconnect -> Ok C_reconnect
  | Cauth a ->
      Ok
        (C_auth
           (match a with
            | Authbare -> KA_bare
            | Authpassword p -> KA_password p
            | Authresume -> KA_resume
            | Authvsn l -> KA_vsn l
            | Authtoken s -> KA_token s
            | Authmethod s -> KA_method s))
  | Crenew -> Ok C_renew
  | Crevoke -> Ok C_revoke
  | Csend_msg { target; payload; capture } ->
      let* f = kfeed_of_target t actor target in
      Ok (C_post (f, payload_of t payload, Option.map (intern t) capture))
  | Csend_read { target; up_to } ->
      let* kf =
        match target with
        | None -> Ok None
        | Some tg -> let* k = kfeed_of_target t actor tg in Ok (Some k)
      in
      Ok (C_read (kf, up_to))
  | Csend_typing target ->
      let* f = target_feed t actor target in
      (* The kernel records that the *actor* is typing; the target selects
         which presence channel is lit, and is carried for that reason only. *)
      Ok (C_typing (if f.feed_a = actor then f.feed_b else f.feed_a))
  | Csend_ack m -> Ok (C_ack (msgref t m))
  | Csend_file { name; target; capture } ->
      (* No sugar survives: a File elaborates to the same post a message is,
         with the object name as its body.  A media type is a payload field,
         written in the struct form, not a second keyword. *)
      let* f = kfeed_of_target t actor target in
      Ok (C_post (f, text_payload name, Option.map (intern t) capture))
  | Cedit { m; mut } ->
      let* km =
        (match mut with
         | Mubody s -> Ok (KM_body s)
         | Mufield (f, v) -> Ok (KM_field (field_name t f, datum_of v))
         (* Unproduceable by the current grammar: a tombstone is what a delete
            leaves behind, and `delete message` already says it. *)
         | Mutombstone -> Error "tombstone is a deletion, not an edit")
      in
      Ok (C_edit (msgref t m, km))
  | Cdelete m -> Ok (C_delete (msgref t m))
  | Cdelete_group g -> Ok (C_group_del (intern t g))
  | Ccreate_group g -> Ok (C_group_new (intern t g))
  | Cadd { actor = a; to_ } ->
      Ok (C_add (intern t a, match to_ with `group g -> KA_group (intern t g) | `roster -> KA_roster))
  | Cremove { actor = a; from } ->
      Ok (C_remove (intern t a, match from with `group g -> KA_group (intern t g) | `roster -> KA_roster))
  | Cban { actor = a; scope } ->
      Ok (C_ban (intern t a, Option.join (Option.map (scope_aid t) scope), true))
  | Cunban { actor = a; scope } ->
      Ok (C_ban (intern t a, Option.join (Option.map (scope_aid t) scope), false))
  | Cquery q -> let* kq = query t actor q in Ok (C_query kq)
  | Cbootstrap { limit; preview } -> Ok (C_bootstrap (limit, preview))
  | Cauthority { method_; cert } ->
      Ok (C_authority (method_, Option.map (intern t) cert))

and query t actor = function
  | Qinbox { target; limit } ->
      let* f = target_feed t actor target in
      Ok (Q_inbox (f, limit))
  | Qinbox_cont -> Ok Q_inbox_cont
  | Qevents { target; after; limit } ->
      let* f = target_feed t actor target in
      Ok (Q_events (f, boundary_of after, limit))
  | Qcursor_read { target; up_to } ->
      let* f = target_feed t actor target in
      Ok (Q_cursor (f, up_to))
  | Qhome { limit; preview } -> Ok (Q_home (limit, preview))
  | Qhome_cont -> Ok Q_home_cont
  | Qroster -> Ok Q_roster
  | Qgroups -> Ok Q_groups
  | Qmembers g -> Ok (Q_members (intern t g))
  | Qmoderation None -> Ok (Q_moderation None)
  | Qmoderation (Some target) ->
      let* f = target_feed t actor target in
      Ok (Q_moderation (Some f))
  | Qsubscriptions -> Ok Q_subs
  | Qsearch { target; text; limit } ->
      let* f =
        match target with
        | None -> Ok None
        | Some tg -> let* x = target_feed t actor tg in Ok (Some x)
      in
      Ok (Q_search (f, text, limit))
  | Qsearch_cont -> Ok Q_search_cont
  (* Discover is per scope.  The optional subject (`discover group room1`)
     selects nothing in the protocol's discovery reply, so it is dropped
     rather than smuggled into the scope string. *)
  | Qdiscover { scope; what = _ } -> Ok (Q_discover scope)

(* ---- probes ---- *)

let probe t actor = function
  | Psends -> Ok P_sends
  | Pqueries_inbox -> Ok P_inbox
  | Pqueries_home -> Ok P_home
  | Pqueries_events target ->
      let* f = target_feed t actor target in
      Ok (P_events f)
  | Pqueries_search target ->
      let* f = target_feed t actor target in
      Ok (P_search f)
  | Preads target ->
      let* f = target_feed t actor target in
      Ok (P_reads f)

(* ---- expectations ---- *)

let judgment t actor = function
  | Emsg { from; neg; inbound; content } ->
      let body, fields =
        match content with
        | Some c -> body_of_payload t c
        | None -> (None, [])
      in
      Ok (J_msg { from = Option.map (intern t) from; neg; inbound; body; fields })
  | Evis { m; field; hidden } ->
      Ok (J_vis { m = msgref t m; field = Option.map (field_name t) field; hidden })
  | Efield { m; field; value } ->
      Ok (J_field (msgref t m, field_name t field, datum_of value))
  | Eack m -> Ok (J_ack (msgref t m))
  | Emsgstate s ->
      (* "message deleted" and "message marked as read" name an observable
         state change; the kernel expresses state changes as events, so the
         surface state maps onto the event kind rather than onto a flag. *)
      let kind = if String.equal s "marked as read" then "read" else s in
      Ok (J_event { fam = "message"; kind; actor = None; up_to = None; m = None; seq = None })
  | Eevent { fam; kind; actor; up_to; m; seq } ->
      Ok (J_event { fam; kind; actor = Option.map (intern t) actor; up_to
                  ; m = Option.map (fun x -> msgref t x) m; seq })
  | Eaccess b -> Ok (J_access b)
  | Eerror (code, neg) -> Ok (J_error (code, neg))
  | Estate s -> Ok (J_state s)
  | Ecoll { what; cmpn; neg } -> Ok (J_coll { what; cmp = cmp_of cmpn; neg })
  | Eflag s -> Ok (J_flag s)
  | Erel { actor; kind; other; neg } ->
      (* The surface form carries the *other* name and no owner: the owner is
         whoever is speaking, which the judgment reads from the observation. *)
      let _ = other in
      Ok (J_rel { actor = intern t actor; kind; neg })
  | Ebanned { actor; scope } ->
      Ok (J_ban (intern t actor, Option.join (Option.map (scope_aid t) scope)))
  | Eexists { what; name } -> Ok (J_exists (what, intern t name))
  | Erole { actor; role; group } ->
      Ok (J_role (intern t actor, role, intern t group))
  | Ecursor { state; feed } ->
      let* f =
        match feed with
        | None -> Ok None
        | Some tg -> let* x = target_feed t actor tg in Ok (Some x)
      in
      Ok (J_cursor (state, f))
  | Efeature s -> Ok (J_feature s)
  | Evsn s -> Ok (J_vsn s)

(* ---- statements ---- *)

(* The walker carries the acting principal, because `session bob` is what
   makes the following commands and expectations belong to bob.  A statement
   that needs a speaker before one has been declared is an error, not a
   silent run as principal 0. *)
let stmts (sc : scenario) : (kstmt list * interner, string) result =
  let t = create () in
  let rec go sp sid pr i acc = function
    | [] -> Ok (List.rev acc, t)
    | s :: rest ->
        let named k =
          Result.map_error
            (fun m -> Printf.sprintf "%s, statement %d: %s" sc.Ast.name i m)
            k
        in
        match s with
        | SSess { session; as_ } ->
            (* `session alice2 as alice` declares a second incidence of one
               principal.  The incidence owns the session record, the presence
               bit, the read cursor and the captured pages; the principal owns
               the mailbox, the roster, the clearance and the authorship of
               anything posted from here.  Without `as_` the name is its own
               principal, which keeps every single-incidence scenario unchanged. *)
            let a = intern t session in
            (* A bare `session alice1` re-selects an incidence.  If that name
               was already declared as somebody's incarnation, its principal is
               the one already established -- restating `as alice` is not a
               precondition for coming back to the same session.  Only a first
               mention, or an explicit `as`, decides whose incidence it is. *)
            let p = match as_ with
              | Some n -> intern t n
              | None -> (match List.assoc_opt session sp with
                         | Some p -> p
                         | None -> a)
            in
            let sp = (session, p) :: List.remove_assoc session sp in
            go sp a p (i + 1) (KS_actor (a, p) :: acc) rest
        | Stier tl ->
            go sp sid pr (i + 1)
              (KS_tier (if tl = Ast.L1 then T_l1 else T_l2) :: acc)
              rest
        | SGiven f ->
            let* gf = named (fact t pr f) in
            go sp sid pr (i + 1) (KS_given gf :: acc) rest
        | Swhen { actor = a; probe = p } ->
            (* A probe is anchored on the principal being probed, not on the
               session that happens to be current -- `when carol queries events
               for group room1` asks about carol wherever it is written. *)
            let pa = intern t a in
            let* kp = named (probe t pa p) in
            go sp sid pr (i + 1) (KS_probe (pa, kp) :: acc) rest
        | SExpect e ->
            (* An expectation needs a speaker, but not necessarily a session:
               `when carol queries events ... / expect access denied` asserts
               about carol's probe, and the observation carries that actor.
               Declining to elaborate it would be wrong; the runner is the
               place that can tell whether an observation actually arrived. *)
            let* kj = named (judgment t pr e) in
            go sp sid pr (i + 1) (KS_expect kj :: acc) rest
        | SCmd c ->
            if sid = no_principal then
              Error (Printf.sprintf "%s, statement %d: command before any session" sc.Ast.name i)
            else
              (* The command acts as the incidence -- that is what makes two
                 incarnations of one principal have separate connection state --
                 while its feed targets resolve against the principal. *)
              let* kc = named (cmd t pr c) in
              go sp sid pr (i + 1) (KS_cmd (sid, kc) :: acc) rest
        | Swait ms -> go sp sid pr (i + 1) (KS_wait ms :: acc) rest
        | Sskip -> go sp sid pr (i + 1) (KS_skip :: acc) rest
  in
  go [] no_principal no_principal 1 [] sc.Ast.stmts

(* `scenario` is what the runner uses.  `names` exposes the interner's table
   afterwards, which is the only way a report can print "bob" instead of 3. *)
let scenario sc = Result.map fst (stmts sc)

let names (sc : scenario) = Result.map (fun (ks, t) -> (ks, dump t)) (stmts sc)
