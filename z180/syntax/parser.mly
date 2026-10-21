%{
(* Menhir grammar for Z.180 surface syntax.

   The grammar is a *tier-aware superset of the two protocol layers it
   describes*: L1 (serverless multicast) and L2 (brokered TLS & PKI) share
   one statement language, and commands that do not exist in the tier a
   scenario declares are rejected by the elaborator as `unsupported`, not
   silently accepted.  Keeping one grammar rather than two is what makes a
   cross-tier invariant like "the same scenario skeleton is expressible at
   both layers" checkable at all.

   Normalisation decisions taken here, in the grammar rather than in
   semantic code:
   - statement-per-line, terminated by one or more newlines (`nl`);
     no indentation-sensitive syntax;
   - one fact per `given` line (multi-line given blocks were sugar);
   - structured payload blocks are brace-delimited, so newlines inside
     them are separators and cannot leak into the statement grammar;
   - `expect` is a single statement form whose body decides the channel
     the assertion binds to.                                             *)

open Ast
%}

/* ---- terminals carrying data ---- */
%token <string> IDENT STR LABEL TITLE
%token <string * string> FREF
%token <int> INT DUR

/* ---- structure ---- */
%token GIVEN WHEN SESSION AS TIER L1 L2 WAIT SKIP EXPECT NOT
%token EOL EOF

/* ---- session / transport ---- */
%token CONNECT DISCONNECT RECONNECT AUTH RENEW REVOKE PASSWORD RESUME

/* ---- send / mutate ---- */
%token SEND MESSAGE MESSAGES TO FROM READ TYPING ACK FILE EDIT DELETE
%token CAPTURE ID REF BODY FIELD HAS IS IN OF FOR LAST UP AT LEVEL
%token CREATE ADD REMOVE BAN UNBAN EXISTS OWNER MEMBER BANNED ROSTER
%token SENDS QUERIES

/* ---- feed kinds ---- */
%token PEER GROUP FEED CHAN MAILBOX PRIVATE

/* ---- query family ---- */
%token QUERY INBOX EVENTS CURSOR HOME CONTINUE AFTER SNAPSHOT LIMIT PREVIEW
%token SEARCH TEXT GROUPS MEMBERS MODERATION SUBSCRIPTIONS DISCOVER SCOPE
%token SERVER EXTENSION POLICY BOOTSTRAP

/* ---- expect family ---- */
%token EVENT PRESENCE ACCESS ALLOWED DENIED ERROR AUTHENTICATED CREATED
%token SAME TOKEN REFRESHED SHARED MORE NEXT EMPTY REPLAY GAPS DUPLICATES
%token DUPLICATE VISIBLE HIDDEN DELETED MARKED INBOUND RESULT ITEMS COUNT
%token FEEDS PREVIEWS MENTIONS UNREAD CLEARANCE CLASSIFICATION BRANCH ORG
%token FEATURE UNCHANGED UPDATED ACTOR SEQ TRUE
%token DELIVERED RECEIVED EDITED ONLINE OFFLINE NO NONEMPTY
%token AUTHORITY ANNOUNCE REGISTER AUTHENTICATE DISMISS
%token SELECTED_VSN SUPPORTED_VSN

/* ---- punctuation ---- */
%token LBRACE RBRACE LBRACKET RBRACKET COMMA PAIR LE EQ GT

%start <Ast.scenario list> program

%%

program:
  | eols? EOF { [] }
  | eols? scenarios EOF { $2 }

scenarios:
  | scenario { [$1] }
  | scenarios scenario { $1 @ [$2] }

scenario:
  | TITLE nl stmts { { Ast.name = $1; stmts = $3 } }

nl:
  | eols { () }
eols:
  | EOL { () }
  | eols EOL { () }

stmts:
  | stmt { [$1] }
  | stmts stmt { $1 @ [$2] }

stmt:
  | s_session { $1 }
  | s_tier { $1 }
  | s_given { $1 }
  | s_when { $1 }
  | s_expect { $1 }
  | s_cmd { $1 }
  | s_wait { $1 }
  | s_skip { $1 }

/* ------------------------------------------------------------------ */
/* context                                                            */
/* ------------------------------------------------------------------ */

s_session:
  | SESSION IDENT nl
      { SSess { session = $2; as_ = None } }
  | SESSION IDENT AS IDENT nl
      { SSess { session = $2; as_ = Some $4 } }

s_tier:
  | TIER L1 nl { Stier L1 }
  | TIER L2 nl { Stier L2 }

s_wait: | WAIT DUR nl { Swait $2 }
s_skip: | SKIP nl { Sskip }

/* ------------------------------------------------------------------ */
/* given: state facts only                                            */
/* ------------------------------------------------------------------ */

s_given: | GIVEN fact nl { SGiven $2 }

fact:
  | actor HAS CLEARANCE IDENT
      { Fclearance { actor = $1; level = $4 } }
  | actor HAS BRANCH IDENT
      { Fbranch { actor = $1; branch = $4 } }
  | actor HAS ORG IDENT
      { Forg { actor = $1; org = $4 } }
  | MESSAGE IDENT HAS CLASSIFICATION IDENT
      { Fclass { m = $2; level = $5 } }
  | MESSAGE IDENT FIELD field_name vis AT LEVEL IDENT
      { Ffieldlevel { m = $2; field = $4; hidden = $5; level = $8 } }
  | FEED IDENT HAS BRANCH IDENT
      { Ffeed_branch { feed = $2; branch = $5 } }
  | actor HAS IDENT IN ROSTER
      { Frel { actor = $1; kind = "roster"; other = $3 } }
  | actor READ target UP TO INT
      { Fread { actor = $1; feed = $3; up_to = $6 } }
  | GROUP IDENT EXISTS
      { Fexists { what = "group"; name = $2 } }
  | actor IS OWNER OF GROUP IDENT
      { Frole { actor = $1; role = "owner"; group = $6 } }
  | actor IS MEMBER OF GROUP IDENT
      { Frole { actor = $1; role = "member"; group = $6 } }
  | actor IS NOT MEMBER OF GROUP IDENT
      { Fnotmember { actor = $1; group = $7 } }
  | actor IS BANNED
      { Fban { actor = $1; scope = None } }
  | actor IS BANNED IN GROUP IDENT
      { Fban { actor = $1; scope = Some (Tgroup $6) } }
  | kwtarget MESSAGE INT FROM IDENT STR msgref_opt alias_opt
      { Fmsg { feed = $1; seq = $3; from = $5; body = $6
             ; mid = $7; alias = $8 } }

vis:
  | VISIBLE { false }
  | HIDDEN  { true }

actor: | IDENT { $1 }

kwtarget:
  | PEER IDENT    { Tpeer $2 }
  | GROUP IDENT   { Tgroup $2 }
  | CHAN IDENT    { Tchan $2 }
  | MAILBOX IDENT { Tmailbox $2 }
  | FEED FREF     { let (k, n) = $2 in Tfeed { rf_kind = k; rf_name = n } }
  | PRIVATE IDENT PAIR IDENT { Tpair ($2, $4) }

msgref_opt:
  | /* empty */ { None }
  | ID STR      { Some $2 }

alias_opt:
  | /* empty */ { None }
  | AS IDENT    { Some $2 }

/* ------------------------------------------------------------------ */
/* when: a policy probe, not an executed action                       */
/* ------------------------------------------------------------------ */

s_when: | WHEN IDENT probe nl { Swhen { actor = $2; probe = $3 } }

probe:
  | SENDS MESSAGE            { Psends }
  | QUERIES INBOX            { Pqueries_inbox }
  | QUERIES HOME             { Pqueries_home }
  | QUERIES EVENTS FOR target { Pqueries_events $4 }
  | QUERIES SEARCH target    { Pqueries_search $3 }
  | reads_kw target            { Preads $2 }

reads_kw: | READ { () }

/* ------------------------------------------------------------------ */
/* commands                                                           */
/* ------------------------------------------------------------------ */

s_cmd:
  | cmd nl { SCmd $1 }

cmd:
  | CONNECT                       { Cconnect None }
  | CONNECT IDENT                 { Cconnect (Some $2) }
  | DISCONNECT                    { Cdisconnect }
  | RECONNECT                     { Creconnect }
  | AUTH                          { Cauth Authbare }
  | AUTH PASSWORD STR             { Cauth (Authpassword $3) }
  | AUTH TOKEN STR                { Cauth (Authtoken $3) }
  | AUTH RESUME                   { Cauth Authresume }
  | AUTH SUPPORTED_VSN LBRACKET ident_list RBRACKET
      { Cauth (Authvsn $4) }
  | AUTH IDENT                    { Cauth (Authmethod $2) }
  | RENEW                         { Crenew }
  | REVOKE                        { Crevoke }
  | SEND MESSAGE TO target payload capture_opt
      { Csend_msg { target = $4; payload = $5; capture = $6 } }
  | SEND READ target FOR LAST
      { Csend_read { target = Some $3; up_to = None } }
  | SEND READ target UP TO INT
      { Csend_read { target = Some $3; up_to = Some $6 } }
  | SEND READ FOR LAST
      { Csend_read { target = None; up_to = None } }
  | SEND READ UP TO INT
      { Csend_read { target = None; up_to = Some $5 } }
  | SEND TYPING TO target
      { Csend_typing $4 }
  | SEND ACK FOR msgref
      { Csend_ack $4 }
  | SEND FILE STR
      { Csend_file { name = $3; mime = None } }
  | SEND FILE STR AS IDENT
      { Csend_file { name = $3; mime = Some $5 } }
  | EDIT MESSAGE msgref BODY STR
      { Cedit { m = $3; mut = Mubody $5 } }
  | EDIT MESSAGE msgref FIELD field_name value
      { Cedit { m = $3; mut = Mufield ($5, $6) } }
  | DELETE MESSAGE msgref
      { Cdelete $3 }
  | DELETE GROUP IDENT
      { Cdelete_group $3 }
  | CREATE GROUP IDENT
      { Ccreate_group $3 }
  | ADD IDENT TO GROUP IDENT
      { Cadd { actor = $2; to_ = `group $5 } }
  | ADD IDENT TO ROSTER
      { Cadd { actor = $2; to_ = `roster } }
  | REMOVE IDENT FROM GROUP IDENT
      { Cremove { actor = $2; from = `group $5 } }
  | REMOVE IDENT FROM ROSTER
      { Cremove { actor = $2; from = `roster } }
  | BAN IDENT
      { Cban { actor = $2; scope = None } }
  | BAN IDENT IN GROUP IDENT
      { Cban { actor = $2; scope = Some (Tgroup $5) } }
  | UNBAN IDENT
      { Cunban { actor = $2; scope = None } }
  | UNBAN IDENT IN GROUP IDENT
      { Cunban { actor = $2; scope = Some (Tgroup $5) } }
  | BOOTSTRAP HOME limit_opt preview_opt
      { Cbootstrap { limit = $3; preview = $4 } }
  | query { Cquery $1 }
  | AUTHORITY authmethod IDENT
      { Cauthority { method_ = $2; cert = Some $3 } }
  | AUTHORITY authmethod
      { Cauthority { method_ = $2; cert = None } }

authmethod:
  | ANNOUNCE   { "announce" }
  | REGISTER   { "register" }
  | AUTHENTICATE { "authenticate" }
  | DISMISS    { "dismiss" }
  | RENEW      { "renew" }

query:
  | QUERY INBOX target limit_opt     { Qinbox { target = $3; limit = $4 } }
  | QUERY INBOX CONTINUE             { Qinbox_cont }
  | QUERY EVENTS target AFTER boundary limit_opt
      { Qevents { target = $3; after = $5; limit = $6 } }
  | QUERY CURSOR READ target UP TO INT
      { Qcursor_read { target = $4; up_to = $7 } }
  | QUERY HOME limit_opt preview_opt { Qhome { limit = $3; preview = $4 } }
  | QUERY HOME CONTINUE              { Qhome_cont }
  | QUERY ROSTER                     { Qroster }
  | QUERY GROUPS                     { Qgroups }
  | QUERY MEMBERS OF GROUP IDENT     { Qmembers $5 }
  | QUERY MODERATION                 { Qmoderation None }
  | QUERY MODERATION target          { Qmoderation (Some $3) }
  | QUERY SUBSCRIPTIONS              { Qsubscriptions }
  | QUERY SEARCH target TEXT STR limit_opt
      { Qsearch { target = Some $3; text = $5; limit = $6 } }
  | QUERY SEARCH TEXT STR limit_opt
      { Qsearch { target = None; text = $4; limit = $5 } }
  | QUERY SEARCH CONTINUE            { Qsearch_cont }
  | QUERY DISCOVER SERVER            { Qdiscover { scope = "server"; what = None } }
  | QUERY DISCOVER AUTH              { Qdiscover { scope = "auth"; what = None } }
  | QUERY DISCOVER EXTENSION         { Qdiscover { scope = "extension"; what = None } }
  | QUERY DISCOVER FEED target       { Qdiscover { scope = "feed"; what = None } }
  | QUERY DISCOVER GROUP IDENT       { Qdiscover { scope = "group"; what = Some $4 } }
  | QUERY DISCOVER POLICY IDENT      { Qdiscover { scope = "policy"; what = Some $4 } }
  | QUERY DISCOVER SCOPE IDENT       { Qdiscover { scope = $4; what = None } }

boundary:
  | INT       { Bseq $1 }
  | CURSOR    { Bcursor }
  | SNAPSHOT  { Bsnapshot }
  | NEXT      { Bnext }
  | LAST      { Blast }

target:
  | kwtarget { $1 }
  | FREF     { let (k, n) = $1 in Tfeed { rf_kind = k; rf_name = n } }
  | IDENT    { Tident $1 }

msgref:
  | ID IDENT   { Midl $2 }
  | REF STR    { Mrefl $2 }
  | STR        { Midl $1 }
  | IDENT      { Midl $1 }

payload:
  | STR        { Ptext $1 }
  | LBRACE fields RBRACE { Pstruct $2 }

capture_opt:
  | /* empty */           { None }
  | CAPTURE ID AS IDENT   { Some $4 }

fields:
  | /* empty */   { [] }
  | fields field  { $1 @ [$2] }
  | fields nlsep  { $1 }

nlsep: | EOL { () } | COMMA { () }

field:
  | LABEL value { ($1, $2) }
  | BODY value  { ("body", $2) }

value:
  | STR  { Vstr $1 }
  | INT  { Vint $1 }
  | TRUE { Vat "true" }
  | IDENT { Vat $1 }

field_name:
  | IDENT { $1 }
  | BODY  { "body" }

ident_list:
  |                    { [] }
  | ident_list IDENT   { $1 @ [$2] }

limit_opt:
  | /* empty */  { None }
  | LIMIT INT    { Some $2 }

preview_opt:
  | /* empty */     { None }
  | PREVIEW INT     { Some $2 }

/* ------------------------------------------------------------------ */
/* expectations                                                       */
/*                                                                    */
/* `expect` is one statement form.  Its body determines which channel */
/* the assertion binds to: a message observation, the last reply, the  */
/* event stream, or the access decision.  Negation is part of the      */
/* body, never a statement-level modifier, which is what keeps         */
/* "expect not message ..." from being read off an unrelated channel.  */
/* ------------------------------------------------------------------ */

s_expect: | EXPECT exp nl { SExpect $2 }

exp:
  | MESSAGE FROM IDENT content_opt
      { Emsg { from = Some $3; neg = false; inbound = false; content = $4 } }
  | INBOUND MESSAGE FROM IDENT content_opt
      { Emsg { from = Some $4; neg = false; inbound = true; content = $5 } }
  | MESSAGE content
      { Emsg { from = None; neg = false; inbound = false; content = Some $2 } }
  | NOT MESSAGE FROM IDENT content_opt
      { Emsg { from = Some $4; neg = true; inbound = false; content = $5 } }
  | NOT MESSAGE content
      { Emsg { from = None; neg = true; inbound = false; content = Some $3 } }
  | MESSAGE msgref VISIBLE
      { Evis { m = $2; field = None; hidden = false } }
  | MESSAGE msgref HIDDEN
      { Evis { m = $2; field = None; hidden = true } }
  | MESSAGE msgref FIELD field_name VISIBLE
      { Evis { m = $2; field = Some $4; hidden = false } }
  | MESSAGE msgref FIELD field_name HIDDEN
      { Evis { m = $2; field = Some $4; hidden = true } }
  | MESSAGE msgref FIELD field_name value
      { Efield { m = $2; field = $4; value = $5 } }
  | ACK FOR msgref
      { Eack $3 }
  | MESSAGE DELETED
      { Emsgstate "deleted" }
  | MESSAGE MARKED AS READ
      { Emsgstate "marked as read" }
  | EVENT event_body
      { $2 }
  | ACCESS ALLOWED  { Eaccess true }
  | ACCESS DENIED   { Eaccess false }
  | ACCESS TOKEN    { Estate "access token" }
  | ACCESS TOKEN REFRESHED { Estate "access token refreshed" }
  | ERROR IDENT              { Eerror ($2, false) }
  | NOT ERROR IDENT          { Eerror ($3, true) }
  | AUTHENTICATED            { Estate "authenticated" }
  | SESSION CREATED          { Estate "session created" }
  | SAME SESSION             { Estate "same session" }
  | coll                     { $1 }
  | flag                     { $1 }
  | IDENT IN ROSTER          { Erel { actor = $1; kind = "roster"; other = ""; neg = false } }
  | IDENT NOT IN ROSTER      { Erel { actor = $1; kind = "roster"; other = ""; neg = true } }
  | IDENT IN MODERATION      { Erel { actor = $1; kind = "moderation"; other = ""; neg = false } }
  | IDENT IS BANNED          { Ebanned { actor = $1; scope = None } }
  | IDENT IS BANNED IN GROUP IDENT { Ebanned { actor = $1; scope = Some (Tgroup $6) } }
  | GROUP IDENT EXISTS       { Eexists { what = "group"; name = $2 } }
  | IDENT IS OWNER OF GROUP IDENT { Erole { actor = $1; role = "owner"; group = $6 } }
  | IDENT IS MEMBER OF GROUP IDENT { Erole { actor = $1; role = "member"; group = $6 } }
  | READ CURSOR UNCHANGED    { Ecursor { state = "unchanged"; feed = None } }
  | READ CURSOR UPDATED      { Ecursor { state = "updated"; feed = None } }
  | READ CURSOR UNCHANGED IN target { Ecursor { state = "unchanged"; feed = Some $5 } }
  | READ CURSOR UPDATED IN target   { Ecursor { state = "updated"; feed = Some $5 } }
  | FEATURE IDENT            { Efeature $2 }
  | SELECTED_VSN IDENT       { Evsn $2 }

content:
  | BODY STR   { Ptext $2 }
  | LBRACE fields RBRACE { Pstruct $2 }

content_opt:
  | /* empty */ { None }
  | content     { Some $1 }

event_body:
  | MESSAGE eventkind actor_opt upto_opt msgref_id_opt
      { Eevent { fam = "message"; kind = $2
               ; actor = $3; up_to = $4; m = $5; seq = None } }
  | MESSAGE eventkind ACTOR IDENT SEQ INT
      { Eevent { fam = "message"; kind = $2
               ; actor = Some $4; up_to = None; m = None; seq = Some $6 } }
  | eventfam eventkind actor_opt upto_opt msgref_id_opt
      { Eevent { fam = $1; kind = $2
               ; actor = $3; up_to = $4; m = $5; seq = None } }
  | eventkind actor_opt
      { Eevent { fam = "presence"; kind = $1; actor = $2
               ; up_to = None; m = None; seq = None } }

eventfam:
  | PRESENCE { "presence" }

eventkind:
  | RECEIVED  { "received" }
  | DELIVERED { "delivered" }
  | READ      { "read" }
  | EDITED    { "edited" }
  | DELETED   { "deleted" }
  | UPDATED   { "updated" }
  | ONLINE    { "online" }
  | OFFLINE   { "offline" }
  | TYPING    { "typing" }

actor_opt:
  | /* empty */ { None }
  | IDENT       { Some $1 }

upto_opt:
  | /* empty */     { None }
  | UP TO INT       { Some $3 }

msgref_id_opt:
  | /* empty */  { None }
  | ID IDENT     { Some (Midl $2) }

coll:
  | collwhat cmpv
      { Ecoll { what = $1; cmpn = $2; neg = false } }
  | NOT collwhat cmpv
      { Ecoll { what = $2; cmpn = $3; neg = true } }
  | RESULT ITEMS cmpv
      { Ecoll { what = "result items"; cmpn = $3; neg = false } }
  | NOT RESULT ITEMS cmpv
      { Ecoll { what = "result items"; cmpn = $4; neg = true } }
  | collwhat COUNT cmpv
      { Ecoll { what = $1; cmpn = $3; neg = false } }
  | NOT collwhat COUNT cmpv
      { Ecoll { what = $2; cmpn = $4; neg = true } }
  | EMPTY REPLAY
      { Ecoll { what = "replay"; cmpn = Ceq 0; neg = false } }
  | eventspec
      { $1 }

collwhat:
  | ITEMS       { "items" }
  | MESSAGES    { "messages" }
  | FEEDS       { "feeds" }
  | PREVIEWS    { "previews" }
  | MENTIONS    { "mentions" }
  | UNREAD      { "unread" }
  | ROSTER      { "roster" }
  | MODERATION  { "moderation" }
  | GROUPS      { "groups" }
  | SUBSCRIPTIONS { "subscriptions" }
  | MEMBERS     { "members" }

eventspec:
  | EVENTS cmpv
      { Ecoll { what = "events"; cmpn = $2; neg = false } }
  | NOT EVENTS cmpv
      { Ecoll { what = "events"; cmpn = $3; neg = true } }
  | EVENTS COUNT cmpv
      { Ecoll { what = "events"; cmpn = $3; neg = false } }
  | NOT EVENTS COUNT cmpv
      { Ecoll { what = "events"; cmpn = $4; neg = true } }

cmpv:
  | /* empty */   { Cplain }
  | EQ INT        { (Ceq $2) }
  | LE INT        { (Cle $2) }
  | GT INT        { (Cgt $2) }
  | NONEMPTY      { Cnonempty }

flag:
  | SNAPSHOT          { Eflag "snapshot" }
  | SHARED SNAPSHOT   { Eflag "shared snapshot" }
  | MORE              { Eflag "more" }
  | NOT MORE          { Eflag "not more" }
  | NO MORE             { Eflag "not more" }
  | NEXT              { Eflag "next" }
  | NO GAPS           { Eflag "no gaps" }
  | NO DUPLICATES     { Eflag "no duplicates" }
  | NOT DUPLICATE FEEDS { Eflag "no duplicate feeds" }

