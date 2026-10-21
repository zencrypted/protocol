(******************************************************************)
(*                                                               *)
(*  Z.180 KERNEL --- TRUTH LAYER                                 *)
(*                                                               *)
(*  The computational core of the Zen Crypted Dharma Test         *)
(*  Automation Language (Z.180, an MSC Z.120 extension).          *)
(*                                                               *)
(*  This file is the single source of truth for scenario          *)
(*  semantics.  Everything below is extracted to OCaml and is the *)
(*  ONLY thing the runner uses to decide PASS / FAIL.  The OCaml  *)
(*  front-end (lexer, Menhir grammar, elaborator) is surface      *)
(*  sugar; it may be rewritten freely, this layer may not be      *)
(*  duplicated.                                                   *)
(*                                                               *)
(*  Design rules baked into the types:                            *)
(*                                                               *)
(*    1. Every surface token is interned to `aid := nat` by the  *)
(*       elaborator, so the kernel is pure, total and decidable   *)
(*       and extraction is trivial (no axioms, no opaque types).  *)
(*    2. The event log has NO presence constructors.  `typing`    *)
(*       and `online` can therefore never appear in a replay ---  *)
(*       not because a filter drops them, but because the type is *)
(*       uninhabited.  Invariant by construction.                 *)
(*    3. Message state is `fold(events)`.  Deletion is absorbing: *)
(*       a tombstone is never resurrected by a late or duplicate  *)
(*       Post, and never edited away, so at-least-once delivery   *)
(*       is idempotent and Delete dominates Edit.                 *)
(*    4. The read cursor is DERIVED (last write wins over the     *)
(*       EvRead stream), never stored.  Rewind therefore needs no *)
(*       special case --- it is just a later event in a fold.     *)
(*    5. Mutation addresses an existing message only: a mutation  *)
(*       of an unknown address is a no-op on state, never a       *)
(*       phantom fact.                                            *)
(*                                                               *)
(******************************************************************)

From Stdlib Require Import Bool List PeanoNat.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* 0.  Identity identifiers                                                  *)
(*                                                                     *)
(* Principal, session id, feed name, message id and value identifiers are   *)
(* all the same Coq type here.  That is deliberate: the kernel must be *)
(* purely computational.  Type discipline lives where it matters ---  *)
(* in the *positions* identifiers occupy (a `feed` field is not a `payload`  *)
(* field) and in the elaborator, the only component that knows what    *)
(* an aid means.                                                      *)
(* ------------------------------------------------------------------ *)

Definition aid := nat.

Lemma aid_eq_dec : forall x y : aid, {x = y} + {x <> y}.
Proof. apply Nat.eq_dec. Qed.

Definition aid_eqb (x y : aid) : bool :=
  if aid_eq_dec x y then true else false.

Lemma aid_eqb_spec : forall x y, aid_eqb x y = true <-> x = y.
Proof.
  intros x y. unfold aid_eqb.
  destruct (aid_eq_dec x y) as [H|H]; simpl; split; congruence.
Qed.

(* ------------------------------------------------------------------ *)
(* 1.  Feeds                                                           *)
(*                                                                     *)
(*  L2 wire form (CHAT-L2.asn1):                                       *)
(*      MessageFeed ::= CHOICE { private [1] Privatebox,               *)
(*                               chan    [2] Streambox,                *)
(*                               mailbox [4] Mailbox,                  *)
(*                               group   [8] Groupbox }                *)
(*  L1 wire form (MESSAGE-L1.asn1):                                    *)
(*      MessageFeed ::= CHOICE { p2p [0], muc [1], chan [2] }          *)
(*  KMailbox is the L3/IPMS landing; KChan covers L1 `chan` and L2     *)
(*  `Streambox`; KPrivate covers L1 `p2p` and L2 `Privatebox`; KGroup  *)
(*  covers L1 `muc` and L2 `Groupbox`.  One feed-kind set therefore    *)
(*  spans all three tiers.                                             *)
(* ------------------------------------------------------------------ *)

Inductive feed_kind := KPrivate | KGroup | KChan | KMailbox.

Lemma feed_kind_eq_dec : forall x y : feed_kind, {x = y} + {x <> y}.
Proof. destruct x, y; auto; right; discriminate. Qed.

Definition feed_kind_eqb (x y : feed_kind) : bool :=
  if feed_kind_eq_dec x y then true else false.

Lemma feed_kind_eqb_spec : forall x y, feed_kind_eqb x y = true <-> x = y.
Proof.
  intros x y. unfold feed_kind_eqb.
  destruct (feed_kind_eq_dec x y) as [H|H]; simpl; split; congruence.
Qed.

(*  A feed is a kind plus two identifiers.  For KPrivate they are the two
    principals; for KGroup / KChan / KMailbox the first is the group or
    channel name and the second is `no_principal`.  Private feeds are
    canonicalised (`fa <= fb`) by construction, which is what makes
    "peer bob" from alice's session and "peer alice" from bob's session
    denote the *same* feed --- and makes that plain decidable equality
    rather than a symmetric-closure argument at every use site.       *)

Record feed := MkFeed
  { f_kind : feed_kind
  ; feed_a    : aid
  ; feed_b    : aid
  }.

Definition no_principal : aid := 0.

Lemma feed_eq_dec : forall x y : feed, {x = y} + {x <> y}.
Proof.
  intros x y. destruct x as [ka aa ba], y as [kb ab bb].
  destruct (feed_kind_eq_dec ka kb) as [->|H]; [ | right; intros E; injection E; contradiction ].
  destruct (aid_eq_dec aa ab) as [->|H];   [ | right; intros E; injection E; contradiction ].
  destruct (aid_eq_dec ba bb) as [->|H];   [ | right; intros E; injection E; contradiction ].
  left; reflexivity.
Qed.

Definition feed_eqb (x y : feed) : bool :=
  if feed_eq_dec x y then true else false.

Lemma feed_eqb_spec : forall x y, feed_eqb x y = true <-> x = y.
Proof.
  intros x y. unfold feed_eqb.
  destruct (feed_eq_dec x y) as [H|H]; simpl; split; congruence.
Qed.

Definition private_feed (x y : aid) : feed :=
  MkFeed KPrivate (Nat.min x y) (Nat.max x y).

(*  Canonical by construction: min/max makes the private feed an
    unordered pair, so symmetry is a computation, not an obligation. *)
Lemma private_feed_sym : forall x y, private_feed x y = private_feed y x.
Proof.
  intros x y. unfold private_feed.
  rewrite (Nat.min_comm y x), (Nat.max_comm y x). reflexivity.
Qed.

Definition group_feed   (n : aid) : feed := MkFeed KGroup   n no_principal.
Definition chan_feed    (n : aid) : feed := MkFeed KChan    n no_principal.
Definition mailbox_feed (n : aid) : feed := MkFeed KMailbox n no_principal.

(* ------------------------------------------------------------------ *)
(* 2.  Payload                                                         *)
(*                                                                     *)
(*  Canonical normal form of the DSL structured block:                 *)
(*      send message to bob { body: "hi"  priority: high }             *)
(*  pp_body is mandatory (the invariant "body is mandatory"); a field  *)
(*  literally named `body` may not also appear in pp_fields, so the    *)
(*  short form and the structured form cannot disagree; and field      *)
(*  names must be distinct, which is where `error badRequest` for a    *)
(*  duplicate field comes from --- the kernel has no representation    *)
(*  for a malformed payload at all.                                    *)
(* ------------------------------------------------------------------ *)

Definition body_field : aid := 0.   (* interned name of `body` *)

Record payload := MkPayload
  { pp_body   : option aid
  ; pp_fields : list (aid * aid)%type
  }.

Fixpoint distinct_fst (xs : list (aid * aid)%type) : bool :=
  match xs with
  | [] => true
  | (a, _) :: rest => negb (existsb (fun fv => aid_eqb a (fst fv)) rest)
                         && distinct_fst rest
  end.

Definition wf_payload (p : payload) : bool :=
  match pp_body p with
  | None => false
  | Some _ =>
      negb (existsb (fun fv => aid_eqb body_field (fst fv)) (pp_fields p))
      && distinct_fst (pp_fields p)
  end.

Definition empty_payload : payload := MkPayload None nil.

Definition text_payload (b : aid) : payload := MkPayload (Some b) nil.

Lemma text_payload_wf : forall b, wf_payload (text_payload b) = true.
Proof. intros b. unfold wf_payload, text_payload. reflexivity. Qed.

Lemma empty_payload_not_wf : forall fs, wf_payload (MkPayload None fs) = false.
Proof. intros fs. unfold wf_payload. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* 3.  Actors                                                          *)
(*                                                                     *)
(*  Wildcard vs exact actor matching is a type, not an `option`, so    *)
(*  "expect event read" (any actor) can never be silently confused     *)
(*  with "expect event read bob".                                      *)
(* ------------------------------------------------------------------ *)

Inductive actor_match := AnyActor | ExactActor (principal : aid).

Definition am_matchb (a : actor_match) (p : aid) : bool :=
  match a with
  | AnyActor     => true
  | ExactActor q => aid_eqb q p
  end.

Lemma am_matchb_spec : forall a p,
  am_matchb a p = true <->
  match a with AnyActor => True | ExactActor q => q = p end.
Proof.
  destruct a; simpl.
  - split; intros _; reflexivity.
  - apply aid_eqb_spec.
Qed.

Definition am_actor (a : actor_match) : option aid :=
  match a with AnyActor => None | ExactActor q => Some q end.

(* ------------------------------------------------------------------ *)
(* 4.  The truth layer: events and message state                       *)
(*                                                                     *)
(*  `event` is the log entry type --- server truth.  Note the absence  *)
(*  of any presence constructor: presence is transport chatter and     *)
(*  lives only in the observation layer (Semantics.v), so it is        *)
(*  unrepresentable in the log, and therefore in a replay.             *)
(*                                                                     *)
(*  Every event is feed-addressed; EvRead is additionally actor-scoped *)
(*  because a read cursor is user-scoped per feed, not per message.    *)
(* ------------------------------------------------------------------ *)

Inductive event :=
  | EvPost   : feed -> aid -> payload -> event   (* feed, message id, payload *)
  | EvEdit   : feed -> aid -> payload -> event
  | EvDelete : feed -> aid -> event
  | EvRead   : aid -> feed -> nat -> event.      (* reader, feed, up_to (seq) *)

(*  A message is addressed by (feed, id).  This is the kernel form of
    `existing_message`: elaboration resolves `ref`, `id`, `capture id
    as` into exactly one of these, and nothing unresolved reaches here. *)

Definition mref := (feed * aid)%type.

Lemma mref_eq_dec : forall x y : mref, {x = y} + {x <> y}.
Proof.
  intros x y. destruct x as [fx mx], y as [fy my].
  destruct (feed_eq_dec fx fy) as [->|H]; [ | right; intros E; injection E; contradiction ].
  destruct (aid_eq_dec mx my) as [->|H]; [ | right; intros E; injection E; contradiction ].
  left; reflexivity.
Qed.

Definition mref_eqb (x y : mref) : bool :=
  if mref_eq_dec x y then true else false.

Lemma mref_eqb_spec : forall x y, mref_eqb x y = true <-> x = y.
Proof.
  intros x y. unfold mref_eqb.
  destruct (mref_eq_dec x y) as [H|H]; simpl; split; congruence.
Qed.

(*  Live holds the current payload; Dead is the tombstone left by
    Delete.  Dead deliberately carries no payload: the observable
    consequence of Delete is "content is gone", and retaining the old
    payload here would tempt a later rule to expose it.               *)

Inductive mstate :=
  | MS_live : payload -> mstate
  | MS_dead : mstate.

(*  project: the fold step.  Given the state observed so far at one
    address, apply the next log entry *only if it targets that address*.

    The four branches are the whole conflict-resolution policy, and
    Invariants.v proves them:

      EvPost   on nothing   -> live        (first delivery wins)
      EvPost   on anything  -> unchanged   (at-least-once is idempotent;
                                           a duplicate or late post can
                                           neither overwrite nor
                                           resurrect)
      EvEdit   on live      -> live p'     (edit replaces payload)
      EvEdit   on dead      -> unchanged   (Delete dominates Edit)
      EvEdit   on nothing   -> unchanged   (mutation addresses existing)
      EvDelete on anything  -> dead        (absorbing)
      EvRead   anywhere     -> unchanged   (inert on message state)     *)

Definition project (cur : option mstate) (t : mref) (e : event) : option mstate :=
  match e with
  | EvPost f m p =>
      if mref_eqb (f, m) t
      then match cur with
           | None   => Some (MS_live p)
           | Some s => Some s
           end
      else cur
  | EvEdit f m p =>
      if mref_eqb (f, m) t
      then match cur with
           | Some (MS_live _) => Some (MS_live p)
           | _                => cur
           end
      else cur
  | EvDelete f m =>
      if mref_eqb (f, m) t then Some MS_dead else cur
  | EvRead _ _ _ => cur
  end.

(*  message_state = fold(events).  The SPEC identity, made executable:
    there is no second stored copy of a message anywhere.              *)

Definition final_state (log : list event) (t : mref) : option mstate :=
  fold_left (fun c e => project c t e) log None.

Definition is_live (log : list event) (t : mref) : bool :=
  match final_state log t with
  | Some (MS_live _) => true
  | _                => false
  end.

Definition is_dead (log : list event) (t : mref) : bool :=
  match final_state log t with
  | Some MS_dead => true
  | _            => false
  end.

Definition state_payload (log : list event) (t : mref) : option payload :=
  match final_state log t with
  | Some (MS_live p) => Some p
  | _                => None
  end.

(*  seq: the feed-scoped ordinal of a message, i.e. its position among
    the Post events of that feed.  This is what DSL `up to <n>` and
    replay boundaries count.  Derived from the log, never stored, so a
    replay and a live delivery cannot disagree about it.               *)

Fixpoint feed_seq_aux (k : nat) (f : feed) (m : aid) (xs : list event) : option nat :=
  match xs with
  | [] => None
  | e :: rest =>
      match e with
      | EvPost f' m' _ =>
          if feed_eqb f' f
          then if aid_eqb m' m then Some k else feed_seq_aux (S k) f m rest
          else feed_seq_aux k f m rest
      | _ => feed_seq_aux k f m rest
      end
  end.

Definition feed_seq (log : list event) (t : mref) : option nat :=
  feed_seq_aux 0 (fst t) (snd t) log.

(*  head_seq: how far the feed has reached --- used for `last` sugar
    and for gap detection.  Counts Posts, not events, so it stays
    aligned with feed_seq.                                             *)

Fixpoint head_seq (f : feed) (xs : list event) : nat :=
  match xs with
  | [] => 0
  | EvPost f' _ _ :: rest => if feed_eqb f' f then S (head_seq f rest) else head_seq f rest
  | _ :: rest => head_seq f rest
  end.

(*  read_cursor: derived by last-write-wins over the EvRead stream.
    Consequence, and this is the point: rewinding a read cursor to a
    smaller seq is not a special case that has to be permitted --- it is
    simply a later event that the fold honours.                        *)

Definition read_step (p : aid) (f : feed) (c : option nat) (e : event) : option nat :=
  match e with
  | EvRead p' f' n => if aid_eqb p p' && feed_eqb f f' then Some n else c
  | _ => c
  end.

Definition read_cursor (log : list event) (p : aid) (f : feed) : option nat :=
  fold_left (read_step p f) log None.

Lemma read_step_here : forall p f c n, read_step p f c (EvRead p f n) = Some n.
Proof.
  intros p f c n. unfold read_step.
  assert (Ha : aid_eqb p p = true) by (apply aid_eqb_spec; reflexivity).
  assert (Hf : feed_eqb f f = true) by (apply feed_eqb_spec; reflexivity).
  rewrite Ha, Hf. reflexivity.
Qed.

(*  The cursor is the *last* read in the stream, whatever came before it
    and whatever its value: this is the fold form of "last write wins",
    and it is what makes a rewind an ordinary event rather than a
    privileged operation. *)
Lemma read_cursor_snoc : forall log c p f n,
  fold_left (read_step p f) (log ++ [EvRead p f n]) c = Some n.
Proof.
  intros log. induction log as [| e log IH]; intros c p f n.
  - rewrite app_nil_l. cbn [fold_left]. rewrite read_step_here. reflexivity.
  - cbn [fold_left app]. rewrite IH. reflexivity.
Qed.

Lemma read_cursor_monochrome : forall log p f n,
  read_cursor (log ++ [EvRead p f n]) p f = Some n.
Proof.
  intros log p f n. unfold read_cursor.
  apply read_cursor_snoc.
Qed.

(*  feed_events: the ordered Post/Edit/Delete stream of one feed, i.e.
    what `query events` and `after <boundary>` read from.  Presence is
    not in it because it is not in the type; EvRead is excluded because
    a read is not feed content.                                        *)

Definition feed_events (log : list event) (f : feed) : list event :=
  filter (fun e => match e with
                   | EvPost f' _ _  => feed_eqb f' f
                   | EvEdit f' _ _  => feed_eqb f' f
                   | EvDelete f' _  => feed_eqb f' f
                   | EvRead _ _ _   => false
                   end) log.

