(* Surface AST of Z.180.

   This is a *syntax* model, deliberately stringly-typed: it records what
   was written, not what it means.  Interning of identifiers, session and
   peer resolution, symbolic cursor expansion and the wildcard/exact actor
   distinction all happen in the elaborator, which is the only component
   allowed to turn surface forms into kernel terms.

   Two properties are already visible at this level and are load-bearing:

   - every statement is one line (or one brace block); there is no
     indentation-sensitive syntax, so the language is LALR(1) and a
     scenario can be diffed line by line against the protocol;
   - `given` takes exactly one fact per line.  The multi-line `given`
     blocks of the earlier prose corpus were surface sugar.            *)

type tier = L1 | L2

(* ---- data terms ---- *)

type value =
  | Vstr of string
  | Vint of int
  | Vat of string            (* atom / enum / bare word: high, secret, v3 *)

type field = string * value

type payload =
  | Ptext of string                       (* "hi"        -> { body: "hi" }  *)
  | Pstruct of field list                 (* { body: "hi" priority: high }  *)

type feedref = { rf_kind : string; rf_name : string }   (* private:alice    *)

(* ---- addressing ---- *)

type target =
  | Tpeer of string            (* peer bob            (session-relative)    *)
  | Tgroup of string           (* group room1                              *)
  | Tchan of string            (* chan news          (L1 / L2 Streambox)   *)
  | Tmailbox of string         (* mailbox inbox      (L3 landing)          *)
  | Tfeed of feedref           (* feed private:alice / bare private:alice  *)
  | Tpair of string * string   (* private alice <-> bob                    *)
  | Taddr of string            (* bob@brokerB / alice@example.com          *)
  | Tident of string           (* bare alias, resolved by the elaborator   *)

type msgref =
  | Midl of string             (* id m1id        (captured protocol id)    *)
  | Mlitl of string            (* "m1"           (DSL-local ref, sugar)    *)
  | Mrefl of string            (* ref "doc"                               *)

(* ---- boundaries ---- *)

type boundary =
  | Bseq of int                (* after 100                                *)
  | Bcursor                    (* after cursor   (session replay position) *)
  | Bnext                      (* after next     (page continuation)       *)
  | Bsnapshot                  (* after snapshot (view anchor)             *)
  | Blast                      (* after last                               *)

type cmp =
  | Ceq of int | Cle of int | Cgt of int
  | Cnonempty | Cplain

(* ---- facts: the `given` layer (state only: no delivery, no authz) ---- *)

type fact =
  | Fclearance of { actor : string; level : string }
  | Fbranch of { actor : string; branch : string }
  | Ffeed_branch of { feed : string; branch : string }
  | Forg of { actor : string; org : string }
  | Fclass of { m : string; level : string }
  | Ffieldlevel of { m : string; field : string; hidden : bool
                   ; level : string }
  | Frel of { actor : string; kind : string; other : string }
      (* alice has bob in roster  (kind = "roster" | "subscription")        *)
  | Fmsg of { feed : target; seq : int; from : string; body : string
            ; mid : string option; alias : string option }
  | Fread of { actor : string; feed : target; up_to : int }
  | Fexists of { what : string; name : string }
  | Frole of { actor : string; role : string; group : string }
  | Fnotmember of { actor : string; group : string }
  | Fban of { actor : string; scope : target option }

(* ---- expectations ---- *)

type expect =
  | Emsg of { from : string option; neg : bool; inbound : bool
            ; content : payload option }
  | Evis of { m : msgref; field : string option; hidden : bool }
  | Efield of { m : msgref; field : string; value : value }
  | Eack of msgref                         (* L1: Ack { table, id }            *)
  | Emsgstate of string                    (* deleted / marked as read         *)
  | Eevent of { fam : string; kind : string; actor : string option
              ; up_to : int option; m : msgref option; seq : int option }
  | Eaccess of bool
  | Eerror of string * bool                (* code, negated                    *)
  | Estate of string                       (* authenticated | session created
              | same session | access token | access token refreshed           *)
  | Ecoll of { what : string; cmpn : cmp; neg : bool }
  | Eflag of string
  | Erel of { actor : string; kind : string; other : string; neg : bool }
  | Ebanned of { actor : string; scope : target option }
  | Eexists of { what : string; name : string }
  | Erole of { actor : string; role : string; group : string }
  | Ecursor of { state : string; feed : target option }
  | Efeature of string
  | Evsn of string

(* ---- commands ---- *)

type auth_arg =
  | Authbare
  | Authpassword of string
  | Authresume
  | Authvsn of string list
  | Authtoken of string
  | Authmethod of string

type mutation =
  | Mubody of string                      (* body "v2"                        *)
  | Mufield of string * value             (* field subject "..."              *)
  | Mutombstone                            (* delete message ...               *)

type probe =
  | Psends
  | Pqueries_inbox
  | Pqueries_events of target
  | Pqueries_home
  | Preads of target
  | Pqueries_search of target

type cmd =
  | Cconnect of string option
  | Cdisconnect
  | Creconnect
  | Cauth of auth_arg
  | Crenew
  | Crevoke
  | Csend_msg of { target : target; payload : payload
                 ; capture : string option }
  | Csend_read of { target : target option; up_to : int option }  (* None = last *)
  | Csend_typing of target
  | Csend_ack of msgref                     (* L1: Ack { table, id }           *)
  | Csend_file of { name : string; target : target
                   ; capture : string option }
      (* X.422.1 File is not a side channel: it is a message whose body names
         an object, so it takes the same target and capture as SEND MESSAGE.
         The old `as MIME` overload was a grammar wart -- a media type belongs
         in the struct payload as a field, where `expect field` can see it. *)
  | Cedit of { m : msgref; mut : mutation }
  | Cdelete of msgref
  | Cdelete_group of string
  | Ccreate_group of string
  | Cadd of { actor : string; to_ : [ `roster | `group of string ] }
  | Cremove of { actor : string; from : [ `roster | `group of string ] }
  | Cban of { actor : string; scope : target option }
  | Cunban of { actor : string; scope : target option }
  | Cquery of query
  | Cbootstrap of { limit : int option; preview : int option }
  | Cauthority of { method_ : string; cert : string option }   (* L1 Authority *)

and query =
  | Qinbox of { target : target; limit : int option }
  | Qinbox_cont
  | Qevents of { target : target; after : boundary; limit : int option }
  | Qcursor_read of { target : target; up_to : int }
  | Qhome of { limit : int option; preview : int option }
  | Qhome_cont
  | Qroster
  | Qgroups
  | Qmembers of string
  | Qmoderation of target option
  | Qsubscriptions
  | Qsearch of { target : target option; text : string; limit : int option }
  | Qsearch_cont
  | Qdiscover of { scope : string; what : string option }

(* ---- statements ---- *)

type stmt =
  | SSess of { session : string; as_ : string option }
  | SGiven of fact
  | Swhen of { actor : string; probe : probe }
  | SCmd of cmd
  | SExpect of expect
  | Swait of int
  | Sskip
  | Stier of tier

type scenario = { name : string; stmts : stmt list }
type program = { scenarios : scenario list }
