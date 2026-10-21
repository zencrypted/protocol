(* lib/kernel.ml -- the truth layer of the Z.180 model.

   This module is the hand-written OCaml mirror of coq/Kernel.v.  It knows
   exactly one thing: given an append-only event log, what is the state of
   a message, of a read cursor, of a feed ordinal.  It contains no policy,
   no sessions, no access decisions -- those live in semantics.ml, and the
   separation is load-bearing (invariant P4: policy never rewrites truth).

   When the Coq proofs land, this file is *replaced* by the extracted
   implementation, not maintained beside it.  The differential check
   (hand-written vs extracted over the whole corpus) is the gate that lets
   the swap happen.

   Five decisions, each of which is a theorem in coq/Kernel.v:

   1. every name is interned to an `aid`; nothing stringly-typed survives
      elaboration into this layer;
   2. the log has no presence constructors.  Presence is an orthogonal
      stream (semantics.ml), so "typing invalidated a replay" is unfalsifiable
      by construction rather than by test;
   3. Delete absorbs: once a message is dead, Post/Edit cannot resurrect it,
      which is what makes at-least-once delivery idempotent;
   4. the read cursor is derived, last-write-wins -- a rewind is just a fold
      over a longer log, so there is no cursor state to corrupt;
   5. mutation addresses an existing message only; `edit` of an unknown id
      is a policy rejection upstream, never a silent insert.             *)

type aid = int

let aid_eq (x : aid) (y : aid) = x = y

(* The tier a scenario is written against.  It is part of the kernel
   signature because the tier decides which commands exist at all: X.422.1
   has no Query family, so an L2 query in an L1 scenario is `unsupported`,
   not a failure of the implementation. *)
type tier = T_l1 | T_l2

(* Interning hands out ids from 1, so 0 is a safe sentinel. *)
let no_principal : aid = 0
let body_field : aid = 0

(* ---- feeds ---- *)

type feed_kind = K_private | K_group | K_chan | K_mailbox

type feed = { f_kind : feed_kind; feed_a : aid; feed_b : aid }

let feed_cmp f g =
  match Stdlib.compare f.f_kind g.f_kind with
  | 0 -> (match Stdlib.compare f.feed_a g.feed_a with
          | 0 -> Stdlib.compare f.feed_b g.feed_b
          | c -> c)
  | c -> c

let feed_eq f g = feed_cmp f g = 0

(* A two-party feed is canonicalised at construction, so the symmetric
   equation is definitional rather than a lemma to remember to apply. *)
let private_feed (x : aid) (y : aid) : feed =
  { f_kind = K_private; feed_a = min x y; feed_b = max x y }

(* A named feed (group, chan, mailbox) has one owner-key and no peer. *)
let named_feed (k : feed_kind) (x : aid) : feed =
  { f_kind = k; feed_a = x; feed_b = no_principal }

(* ---- payloads ---- *)

type datum =
  | Dtext of string
  | Dint of int
  | Datom of string

type payload = {
  pp_body : string option;              (* the mandatory `body` field        *)
  pp_fields : (aid * datum) list;       (* interned field name -> value      *)
}

let datum_eq a b =
  match a, b with
  | Dtext x, Dtext y -> String.equal x y
  | Dint x, Dint y -> x = y
  | Datom x, Datom y -> String.equal x y
  | _ -> false

let field_value p name =
  match List.assoc_opt name p.pp_fields with
  | Some d -> Some d
  | None -> if aid_eq name body_field
            then (match p.pp_body with
                  | Some s -> Some (Dtext s)
                  | None -> None)
            else None

let set_field p name d =
  { p with pp_fields = (name, d) :: List.remove_assoc name p.pp_fields }

(* Well-formedness: body present, no shadowing of `body`, field names
   distinct.  The elaborator checks this; the kernel keeps it as a
   predicate so the check is stated in the same language as the fold. *)
let rec distinct_fst = function
  | [] -> true
  | (k, _) :: t -> not (List.mem_assoc k t) && distinct_fst t

let wf_payload (p : payload) : bool =
  p.pp_body <> None
  && not (List.mem_assoc body_field p.pp_fields)
  && distinct_fst p.pp_fields

let text_payload (s : string) : payload = { pp_body = Some s; pp_fields = [] }

(* ---- events ---- *)
(* The whole truth about messages is this list, in arrival order. *)

type event =
  | EvPost of feed * aid * aid * payload
      (* feed, message id, author, payload.  The author is here because
         "this message came from alice" is a fact about history, not about
         permission.  coq/Kernel.v currently omits it, so `expect message
         from alice` has no kernel denotation there: adding the field is the
         second thing the Coq pass must reconcile, and it does not disturb
         any projection theorem, because `project` ignores it. *)
  | EvEdit of feed * aid * payload
  | EvDelete of feed * aid
  | EvRead of aid * feed * int
  | EvAck of aid * aid
(* EvAck is the L1 acknowledgement (X.422.1 Ack { table, id }).  It is in
   the log because at-least-once redelivery is a claim about history, not
   about a session.  coq/Kernel.v does not have this constructor yet --
   it is the first thing to lift when the Coq pass runs. *)

type mref = feed * aid
type mstate = MS_live of payload | MS_dead

let mref_cmp (f1, m1) (f2, m2) =
  match feed_cmp f1 f2 with 0 -> Stdlib.compare m1 m2 | c -> c

let mref_eq x y = mref_cmp x y = 0

(* The fold step.  Branch policy, spelled out because it is the whole
   content of the idempotence theorems:

   - Post on the addressed message: first Post wins, later Posts are
     absorbed (at-least-once delivery is not a second message);
   - Post where nothing exists: the message comes alive with that payload;
   - Edit rewrites a live message and cannot create one;
   - Delete is absorbing: dead stays dead whatever follows. *)
let project (cur : mstate option) (t : mref) (e : event) : mstate option =
  match e with
  | EvPost (f, m, _, p) ->
      if mref_eq (f, m) t
      then (match cur with None -> Some (MS_live p) | Some s -> Some s)
      else cur
  | EvEdit (f, m, p) ->
      if mref_eq (f, m) t
      then (match cur with Some (MS_live _) -> Some (MS_live p) | _ -> cur)
      else cur
  | EvDelete (f, m) -> if mref_eq (f, m) t then Some MS_dead else cur
  | EvRead _ -> cur
  | EvAck _ -> cur

let final_state (log : event list) (t : mref) : mstate option =
  List.fold_left (fun c e -> project c t e) None log

let is_live s = match s with Some (MS_live _) -> true | _ -> false
let is_dead s = match s with Some MS_dead -> true | _ -> false

let state_payload s =
  match s with Some (MS_live p) -> Some p | _ -> None

(* ---- feed-scoped ordinals ---- *)

(* The ordinal of a message in a feed is its position among the Posts of
   that feed, counted as we walk.  Derived, never stored: a stored ordinal
   is a second source of truth and the corpus has two documents disagreeing
   about whether `last` means an ordinal or a timestamp. *)
let rec feed_seq_aux (f : feed) (n : int) (m : aid) = function
  | [] -> None
  | EvPost (f', m', _, _) :: rest ->
      if feed_eq f f'
      then if aid_eq m m' then Some n
           else feed_seq_aux f (n + 1) m rest
      else feed_seq_aux f n m rest
  | _ :: rest -> feed_seq_aux f n m rest

let feed_seq log f m = feed_seq_aux f 1 m log

(* Number of Posts in a feed: the feed's current head ordinal. *)
let rec head_seq : event list -> int = function
  | [] -> 0
  | EvPost _ :: rest -> 1 + head_seq rest
  | _ :: rest -> head_seq rest

(* Events that concern a feed's messages.  Reads and Acks are deliberately
   excluded: they are about the observer, not about the feed. *)
let feed_events log f =
  List.filter
    (fun e ->
      match e with
      | EvPost (f', _, _, _) | EvEdit (f', _, _) | EvDelete (f', _) -> feed_eq f f'
      | _ -> false)
    log

let feed_head log f = head_seq (feed_events log f)

(* ---- read cursors ---- *)

(* A cursor is (principal, feed) -> highest ordinal read, last write wins.
   Rewinding is expressible because a shorter log simply has fewer Reads in
   it; there is no cursor mutation to get wrong. *)
let read_step (p : aid) (f : feed) (cur : int option) (e : event) : int option =
  match e with
  | EvRead (p', f', c) when aid_eq p p' && feed_eq f f' -> Some c
  | _ -> cur

let read_cursor log p f =
  List.fold_left (fun c e -> read_step p f c e) None log

(* ---- lookups derived from the log ---- *)

(* Every message the log mentions, with its feed.  This is the only way
   the model finds a message by id: there is no side table of ids, so a
   deleted message's tombstone and a never-posted id are distinguishable
   by state, not by which map they appear in. *)
let rec id_index_aux = function
  | [] -> []
  | EvPost (f, m, _, _) :: rest -> (m, f) :: id_index_aux rest
  | EvEdit (f, m, _) :: rest -> (m, f) :: id_index_aux rest
  | EvDelete (f, m) :: rest -> (m, f) :: id_index_aux rest
  | _ :: rest -> id_index_aux rest

let id_index log =
  let acc = List.fold_left
    (fun acc (m, f) ->
      if List.exists (fun (m', _) -> aid_eq m m') acc then acc else (m, f) :: acc)
    [] (id_index_aux log)
  in List.rev acc

let find_feed_of_id log m = List.assoc_opt m (id_index log)

(* Posts of a feed in log order, with their feed-scoped ordinal. *)
type post = {
  ps_ref : mref;
  ps_seq : int;
  ps_author : aid;
  ps_payload : payload;
}

let feed_posts log f =
  let rec go n acc = function
    | [] -> List.rev acc
    | EvPost (f', m, a, p) :: rest ->
        if feed_eq f f'
        then go (n + 1) ({ ps_ref = (f', m); ps_seq = n
                        ; ps_author = a; ps_payload = p } :: acc) rest
        else go n acc rest
    | _ :: rest -> go n acc rest
  in go 1 [] log

(* Messages of a feed that are alive at the end of the log, with the payload
   the fold gives them -- so an Edit is visible here and a Delete is not. *)
let feed_live log f =
  List.filter_map
    (fun ps ->
      match final_state log ps.ps_ref with
      | Some (MS_live p) -> Some { ps with ps_payload = p }
      | Some MS_dead -> None
      | None -> Some ps)
    (feed_posts log f)
