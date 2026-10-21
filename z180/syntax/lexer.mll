{(* Lexer for Z.180 surface syntax.

   Principles:
   - Only *structural* words are keywords.  Data words (clearance levels,
     error codes, feature names, actor names, aliases) stay IDENT, so the
     grammar never has to be edited to add a vocabulary item.
   - Line orientation: a newline is a token (EOL).  There is no
     indentation-sensitive syntax.
   - `foo:bar` with no space is a feed reference (FREF); `foo:` followed by
     a space is a structured-payload field label (LABEL).  This keeps feed
     tokens and field labels in separate token classes, so the grammar
     never has to guess.                                     *)

let feed_ref s =
  let i = String.index s ':' in
  (String.sub s 0 i, String.sub s (i + 1) (String.length s - i - 1))

exception Syntax_error of string

let keyword_table : (string, Parser.token) Hashtbl.t = Hashtbl.create 96

let () =
  List.iter (fun (k, v) -> Hashtbl.add keyword_table k v)
    [ (* program structure *)
      "given", Parser.GIVEN;
      "when", Parser.WHEN;          "session", Parser.SESSION;
      "as", Parser.AS;              "tier", Parser.TIER;
      "l1", Parser.L1;              "l2", Parser.L2;
      "wait", Parser.WAIT;          "skip", Parser.SKIP;
      "expect", Parser.EXPECT;      "not", Parser.NOT;
      (* session / transport *)
      "connect", Parser.CONNECT;    "disconnect", Parser.DISCONNECT;
      "reconnect", Parser.RECONNECT;"auth", Parser.AUTH;
      "renew", Parser.RENEW;        "revoke", Parser.REVOKE;
      "password", Parser.PASSWORD;  "resume", Parser.RESUME;
      (* send / mutate *)
      "send", Parser.SEND;          "message", Parser.MESSAGE;
      "messages", Parser.MESSAGES;  "to", Parser.TO;
      "from", Parser.FROM;          "read", Parser.READ;
      "typing", Parser.TYPING;      "ack", Parser.ACK;
      "file", Parser.FILE;          "edit", Parser.EDIT;
      "delete", Parser.DELETE;      "capture", Parser.CAPTURE;
      "id", Parser.ID;              "ref", Parser.REF;
      "body", Parser.BODY;          "field", Parser.FIELD;
      "has", Parser.HAS;            "is", Parser.IS;
      "in", Parser.IN;              "of", Parser.OF;
      "for", Parser.FOR;            "last", Parser.LAST;
      "up", Parser.UP;              "at", Parser.AT; "level", Parser.LEVEL;
      "create", Parser.CREATE;      "add", Parser.ADD;
      "remove", Parser.REMOVE;      "ban", Parser.BAN;
      "unban", Parser.UNBAN;        "exists", Parser.EXISTS;
      "owner", Parser.OWNER;        "member", Parser.MEMBER;
      "banned", Parser.BANNED;      "roster", Parser.ROSTER;
      (* feed kinds *)
      "peer", Parser.PEER;          "group", Parser.GROUP;
      "feed", Parser.FEED;          "chan", Parser.CHAN;
      "mailbox", Parser.MAILBOX;    "private", Parser.PRIVATE;
      (* query family *)
      "query", Parser.QUERY;        "inbox", Parser.INBOX;
      "events", Parser.EVENTS;      "cursor", Parser.CURSOR;
      "home", Parser.HOME;          "continue", Parser.CONTINUE;
      "after", Parser.AFTER;        "snapshot", Parser.SNAPSHOT;
      "limit", Parser.LIMIT;        "preview", Parser.PREVIEW;
      "search", Parser.SEARCH;      "text", Parser.TEXT;
      "groups", Parser.GROUPS;      "members", Parser.MEMBERS;
      "moderation", Parser.MODERATION; "subscriptions", Parser.SUBSCRIPTIONS;
      "discover", Parser.DISCOVER;  "scope", Parser.SCOPE;
      "server", Parser.SERVER;      "extension", Parser.EXTENSION;
      "policy", Parser.POLICY;      "bootstrap", Parser.BOOTSTRAP;
      (* expect family *)
      "event", Parser.EVENT;        "presence", Parser.PRESENCE;
      "access", Parser.ACCESS;      "allowed", Parser.ALLOWED;
      "denied", Parser.DENIED;      "error", Parser.ERROR;
      "authenticated", Parser.AUTHENTICATED; "created", Parser.CREATED;
      "same", Parser.SAME;          "token", Parser.TOKEN;
      "refreshed", Parser.REFRESHED;"shared", Parser.SHARED;
      "more", Parser.MORE;          "next", Parser.NEXT;
      "empty", Parser.EMPTY;        "replay", Parser.REPLAY;
      "gaps", Parser.GAPS;          "duplicates", Parser.DUPLICATES;
      "duplicate", Parser.DUPLICATE;
      "visible", Parser.VISIBLE;    "hidden", Parser.HIDDEN;
      "deleted", Parser.DELETED;    "marked", Parser.MARKED;
      "inbound", Parser.INBOUND;    "result", Parser.RESULT;
      "items", Parser.ITEMS;        "count", Parser.COUNT;
      "feeds", Parser.FEEDS;        "previews", Parser.PREVIEWS;
      "mentions", Parser.MENTIONS;  "unread", Parser.UNREAD;
      "clearance", Parser.CLEARANCE;"classification", Parser.CLASSIFICATION;
      "branch", Parser.BRANCH;      "org", Parser.ORG;
      "feature", Parser.FEATURE;    "unchanged", Parser.UNCHANGED;
      "updated", Parser.UPDATED;    "actor", Parser.ACTOR;
      "seq", Parser.SEQ;            "true", Parser.TRUE;
      "sends", Parser.SENDS;        "queries", Parser.QUERIES;
      "delivered", Parser.DELIVERED;"received", Parser.RECEIVED;
      "edited", Parser.EDITED;      "online", Parser.ONLINE;
      "offline", Parser.OFFLINE;    "no", Parser.NO;
      "non-empty", Parser.NONEMPTY;
      "authority", Parser.AUTHORITY;"announce", Parser.ANNOUNCE;
      "register", Parser.REGISTER;  "authenticate", Parser.AUTHENTICATE;
      "dismiss", Parser.DISMISS;    "revoke", Parser.REVOKE;
      "selectedVsn", Parser.SELECTED_VSN; "supportedVsn", Parser.SUPPORTED_VSN;
    ]

}

rule token = parse
  (* A scenario title is free text to end of line.  Doing it in the lexer
     keeps the grammar free of "any token sequence" hacks.            *)
  | "scenario" [' ' '\t'] [^ '\n' '\r' ]* as s
      { let t = String.sub s 8 (String.length s - 8) in
        Parser.TITLE (String.trim t) }
  | [' ' '\t' '\r']+                    { token lexbuf }
  | "#" [^ '\n' '\r' ]*                 { token lexbuf }
  | ['\n']                              { Parser.EOL }
  | "<->"                               { Parser.PAIR }
  | "<="                                { Parser.LE }
  | '='                                 { Parser.EQ }
  | '>'                                 { Parser.GT }
  | '{'                                 { Parser.LBRACE }
  | '}'                                 { Parser.RBRACE }
  | '['                                 { Parser.LBRACKET }
  | ']'                                 { Parser.RBRACKET }
  | ','                                 { Parser.COMMA }
  | ['0'-'9']+ "ms" as s                { Parser.DUR (int_of_string (String.sub s 0 (String.length s - 2))) }
  | ['0'-'9']+ as s                     { Parser.INT (int_of_string s) }
  | '"'                                 { string (Buffer.create 32) lexbuf }
  | ['a'-'z' 'A'-'Z' '_']
    ['a'-'z' 'A'-'Z' '0'-'9' '_' '.' '@' '-']*
    ':'
    ['a'-'z' 'A'-'Z' '_']
    ['a'-'z' 'A'-'Z' '0'-'9' '_' '.' '@' '-']* as s
                                        { let (k, n) = feed_ref s in Parser.FREF (k, n) }
  | ['a'-'z' 'A'-'Z' '_']
    ['a'-'z' 'A'-'Z' '0'-'9' '_' '.' '@' '-']* ':' as s
                                        { Parser.LABEL (String.sub s 0 (String.length s - 1)) }
  | ['a'-'z' 'A'-'Z' '_']
    ['a'-'z' 'A'-'Z' '0'-'9' '_' '.' '@' '-']* as s
      { try Hashtbl.find keyword_table s with Not_found -> Parser.IDENT s }
  | eof                                 { Parser.EOF }
  | _ as c
      { let p = Lexing.lexeme_start_p lexbuf in
        raise (Syntax_error
          (Printf.sprintf "unexpected character %C at line %d, column %d"
             c p.Lexing.pos_lnum (p.Lexing.pos_cnum - p.Lexing.pos_bol))) }

and string buf = parse
  | '"'        { Parser.STR (Buffer.contents buf) }
  | "\\n"      { Buffer.add_char buf '\n'; string buf lexbuf }
  | "\\t"      { Buffer.add_char buf '\t'; string buf lexbuf }
  | "\\\""     { Buffer.add_char buf '"'; string buf lexbuf }
  | "\\\\"     { Buffer.add_char buf '\\'; string buf lexbuf }
  | [^ '"' '\\' '\n']+ as s { Buffer.add_string buf s; string buf lexbuf }
  | eof        { raise (Syntax_error "unterminated string literal") }
  | _ as c     { Buffer.add_char buf c; string buf lexbuf }
