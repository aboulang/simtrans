;;;-*-Base:10.; Mode:lisp; Package:CGOL-*-
;; Now the parser, written in CGOL itself.

#.(CGOL)

%=====================CGOL SOURCE FILE=========================%

%  Read PRATT;CGOLMA > if you are wondering what this is.
   If you just want to use this file as a reference manual, the part you
   probably want is the table of CGOL operators headed "BASE COMPONENT" %

=(syntax?-needed := nil;
  nil)$
 
%=================GOT - GENERALIZED OPERATOR TRANSLATOR===================%

special cibase, % input base used by cgol tokenizer %
	token,	% token currently pointed to by input pointer %
	stringnud, % null unless TOKEN is a string, when STRINGNUD is its nud %
	syntax?-needed,  % null when forms not to be eval'd by DEFFIX, DEFINE %
	drbp,       % declared in DEFFIX, used by RIGHT %
	fun,        % function name for use by RIGHTM in *FIX defs - ditto % 
	dentype, isfun,      % set by DEFFIX, used by IS  %
	silence,    % number defining "silence" when giving error messages %
	defbp,      %default binding power for DEFINE%
	ivars, whenvar, result, body, % needed (blech) for "ITER" %
	nudl, ledl, lbpl,	% list of languages currently understood %
	cnud, cled, clbp,	% language currently being learned %
        language_alist,  % ((language_name . (NUD_name LED_name lbp_name)) ...) %
        arithmetic_alist $ % table of functions to use for the operators +,-,** %

define "ADVANCE" ;	  % advances pointer %
	stringnud := nil; token := CGOLToken();
        token$

define "VERIFY"(den);  if den then (advance; den) $ % only advances if den ok %

define "NUDERR" ;  	% treats unknowns and functions as variables %
if getden lbpl
   and null funboundp(token)
 then cgolerr(token cat " MISSING PRECEDING EXPRESSION",2,t)
else let op = token, tp = CGOLTyipeek(); advance;
	["LAMBDA", nil,
		["QUOTE",
		  if funboundp(op)
		     and tp isin !'(9. 13. 32.)
		     and (stringnud
			  or getden nudl and token ne "("
			  or not getden lbpl)
		  then [op, parse("RBP" of op or 25)]
		  else op]]   $

define "FUNBOUNDP" x;
 symbolp(x) and (getl(x, !'(subr fsubr lsubr expr fexpr lexpr macro
				*expr *fexpr *lexpr autoload
				source-code-rewrite))
		     or fboundp(x))$


define "LEDERR" ;	% treats unknown token as felonious %
    cgolerr(token cat " IS NOT AN OPERATOR WITH A LEFT ARGUMENT",2,t)$


% define "GETDEN" indl; indl and ((car indl) of token or getden cdr indl) $ %

!
(progn 'compile
(defvar cgol-package (pkg-find-package "CGOL"))
(defun getden (indl)
  (and (symbolp token)
       (do ((l indl (cdr l)))
	   ((null l))
	 (let ((x (get token (car l))))
	   (and x (return x))
	   #-Maclisp (and (setq x (intern-soft token cgol-package))
			  (setq x (get x (car l)))
			  (return x))))))) $

define "NUD";   verify(stringnud or if token isnum then ["LAMBDA", nil, token]
					else getden nudl)
		or nuderr  $     % if no NUD, call user's error routine %

define "LED";	verify getden ledl or lederr $

define "PARSE" rbp;
iter for translation := funcall(nud) step funcall(led, translation)
     while rbp < (getden lbpl or 0)
     return formcheck(translation) $



"LBP" of "?" := -1 $

%-------CGOL ENTRY AND EXITS-------%

define fexpr "CGOL"(a); % To read CGOL expressions %
  cgol?-enter(a);nil$

define "EXIT"; cgol?-exit();nil$

define "SPEAK"(x);
 let lang := assoc(x,language_alist);
     if lang then lang := cdr(lang)
             else cgolerr(X cat " is an unknown language",3,t);
      nudl := car(lang)   . nudl;
      ledl := cadr(lang)  . ledl;
      lbpl := caddr(lang) . lbpl;
      nil$

define "FORGET";
cdr nudl and (nudl := cdr nudl; ledl := cdr ledl; lbpl := cdr lbpl); nil $ 

define "RESETLANGUAGE";
nudl := !'(NUD); ledl := !'(LED); lbpl := !'(LBP);
cnud := "NUD"; cled := "LED"; clbp := "LBP"; nil $

% Recommended usage with read-time evaluation:
  =LEARN "FOO"<dollarsign>
  definitions of syntax ...
  =LEARN ""<dollarsign>
%

define "LEARN"(x);
 let lang := assoc(x,language_alist);
     if lang then lang := cdr(lang)
             else (lang := [x cat "NUD",x cat "LED",x cat "LBP"];
                   language_alist := (x . lang) . language_alist);
     cnud := car(lang);
     cled := cadr(lang);
     clbp := caddr(lang);
    !`(OR (ASSOC ',X LANGUAGE_ALIST)
	  (PUSH '(,X . ,LANG) LANGUAGE_ALIST)) $

%===============BASE COMPONENT DEFINITIONAL FACILITY=====================%

nilfix	"RIGHT"		["PARSE",   drbp]  $  % to get a right hand argument %
nilfix	"RIGHTLIST"	["PARSELIST", drbp, '","']  $  % ditto, list of args %
nilfix	"RIGHTREP"	["PARSELIST", drbp, ["QUOTE", fun]] $

%------ *FIX OPERATORS -------%

define	"DEFFIX" (dentype, isfun, fun, dlbp, drbp);   % define *FIX fun %
let form := "DEFUN" .
	    [fun, dentype] .
	    (if dentype = cled then !'(left)) .
	    (advance; deprognify(parse 0));
if dlbp then form := ["PROGN", !''compile, form, ["DEFPROP", fun, dlbp, clbp]];
if syntax?-needed then eval form; form $

prefix	"NILFIX"   0	deffix(cnud, "ISN", token, nil,     nil    )  $
prefix	"PREFIX"   0	deffix(cnud, "ISP", token, nil,     advance)  $
prefix	"SUFFIX"   0	deffix(cled, "ISS", token, advance, nil    )  $
prefix	"INFIX"    0	deffix(cled, "ISI", token, advance, token  )  $
prefix	"INFIXR"   0	deffix(cled, "ISI", token, advance, token-1)  $
prefix	"INFIXD"   0	deffix(cled, "ISI", token, advance, advance)  $
prefix	"INFIXM"   0	deffix(cled, "ISM", token, advance, token  )  $

nilfix	"DELIM"	let form :=
		"PROGN" . for i in getvarlist collect ["DEFPROP", i, 0, clbp];
 		if syntax?-needed then eval form; form $

%------ "IS" OPERATOR ------%

prefix	"IS"	25	isfun .
			(if dentype = cled then !'(left)) @
			[right] @
			(if drbp then [drbp]) @
			if isfun = "ISM" then [["QUOTE", fun]]  $
% where "isfun" is one of: %

define	"ISN"(fcn);		[fcn]			$  % is nilfix %
define	"ISS"(left, fcn);	[fcn, left]		$  % is suffix %
define	"ISP"(fcn, rb);		[fcn, parse rb]		$  % is prefix %
define	"ISI"(left, fcn, rb);	[fcn, left, parse rb]	$  % is infix  %
define	"ISM"(left, fcn, rb, cont);  fcn . left . parselist(rb, cont) $ % is infixm %

%============AUXILIARY METALANGUAGE FUNCTIONS=========%

!
(defun pkgcheck (x)
  (if (symbolp x)
      (or (intern-soft x cgol-package) x))) $

define	"CHECK"	del;
if pkgcheck(token) = del or not atom del and pkgcheck(token) isin del then advance
else cgolerr("MISSING " cat del cat " INSERTED BEFORE " cat token,0,nil)$


define lexpr "CAT"(n);    % concatenates arguments  %
	implode append{explodec[arg[1 to n]]} $

define "PARSELIST"(rb, cont);
	parse rb . if pkgcheck(token) eq cont then (advance; parselist(rb, cont)) $

define	"GETVARLIST";     % for making up a list of variables - no parsing %
if pkgcheck(token) ne ";" or stringnud then (token & advance) .
		     if pkgcheck(token) = "," then (advance; getvarlist)$

define	"GETTOKENS";  % for reading a list of tokens, no commas (used in I/O) %
if not pkgcheck(token) isin !'(/) /] /'  /;) then (token & advance) . gettokens $

define "DEPROGNIFY"(x); if not atom x and car x = "PROGN" then cdr x else [x] $

define "NOTIFY" x; x ne t and if not atom x and car x = "NOT" then cadr x else ["NOT", x] $

define "ORIFY" x; x and if not atom x and null cdr x then car x else "OR" . x $

define fexpr "LITERAL" (x); for i in x do set(i,i) $

define "ARITH" x; if assoc(x,arithmetic_alist) exists then cdr(it) else x$

%=========================EXTENSION FACILITY==============================%

% Allows user to define CGOL operators without reference to the target
language.  Closely resembles LISP's DEFUN (DEFPROP f l EXPR) facility %

prefix	"DEFINE"	0 
new fun, type, argts, code, instr, lb, rb, expr, form;
  expr := if pkgcheck(token) isin !'(expr fexpr lexpr macro) then (token & advance)
						   else "EXPR";
  if stringnud or CGOLTyipeek() = 40 %left-paren% then
			(argts := nil; type := cnud; code := ["LIST"];
		     instr := ["PROG2", nil, ["QUOTE", token]] )
  else (argts := [token];   advance;   type := cled;
	code := ["LIST", ["QUOTE",token]];   instr := ["PROG2", nil, 'left'] );
  fun := token; advance;
  if pkgcheck(token) = "(" and not stringnud 
  then (advance; argts := if pkgcheck(token) ne ")" then getvarlist;
	if expr = "LEXPR" then (argts := car argts; expr := "EXPR");
        check ")"; code := nil; instr := nil)
  else while not (pkgcheck(token) = ";" or pkgcheck(token) = ",") or stringnud do
           (while stringnud do
		(instr := instr @ [["CHECK", ["QUOTE", token]]];
	 	 form := ["DEFPROP", token, 0, clbp] . form;
	 	 advance);
            code := code @ [instr];
            if (pkgcheck(token) = ";" or pkgcheck(token) = ",") and not stringnud 
		then instr := nil
     		else (instr := ["PROG2", nil, ["PARSE", "#RBP"]];
	              argts := argts @ [token] ;  advance));
  lb := if type = cled then
	if pkgcheck(token) = "," then (advance; eval parse(1)) else defbp;
  rb := if pkgcheck(token) = "," then (advance; eval parse(1)) else lb or defbp;
  code := subst(rb, "#RBP", code @ if instr then [instr]);
  check ";" ;
  if code then (form := "PROGN" .
			!''compile .
			[ !(PROGN #-NIL 'DEFUN #+NIL 'CGOL-DEFUN) , 
                         [fun, type], (if type = cled then !'(left)), code] .
			(if lb then [["DEFPROP", fun, lb, clbp]]) @
 			nreverse form;
		if syntax?-needed then eval form);
  if pkgcheck(token) ne "?"
	then form :=  form @ [ !(PROGN #-NIL 'DEFUN #+NIL 'CGOL-DEFUN)
	                                . fun .
					(if expr ne 'expr' then [expr]) @
					[argts] @
					deprognify right];
  if code then form else car form $

defbp := 25 $

%=======================LEXICAL SYNTAX===================================%

% The tokenizer has two main states, [1] token buffer empty, [2] token
  buffer not empty. These coorespond to the NUD and LED states of the parser.
  To form a token a sequence of characters is read until a special character
  is seen to be the next character in the stream. If in state [1] then
  a special routine for that character is called. If in state [2] then
  then tokenizer returns either a symbol or a number, depending on
  what the characters in the buffer look like.
  The special characters form four classes,
  [1] whitespace, including comments,
  [2] single-character-tokens,
  [3] initial character of multi-character tokens.
  [4] double-quote tokens.
  Whitespace simply delimits tokens, and is otherwise ignored.
  The single-character tokens are dollar-sign and alt-mode, they
  return without peeking at the next character.
  Multi-character tokens are read by peeking on the stream and looking
  for a continuation to follow in the ctoken?-table. If non is found then
  the token read so far is returned.
  Double-quote tokens are specially read, looking for a matching double-quote
  except that double-quote quotes a double quote.

  Dot is a very special case not covered in the above description.
  It is a special character of class [2] if and only if it is not
  part of a numeric token.
%

%--------LEXICAL EXTENSION OPERATORS--------%

initialize?-multi?-character?-token?-table
 ("-+#&'()*,/:;<=>@[\]^`{|}~!")$

define fexpr "DEFTOK"(a);  for tok in a do puttok tok $

nilfix	"NEWTOK"	let form := "DEFTOK" . getvarlist;
			if syntax?-needed then eval form; form $


%-----LEXICAL SUPPORT ROUTINES-----%

% The function CGOLTOKEN reads a cgol token from the stream bound by
  CGOLREAD. CGOLTYIPEEK peeks at the  next character.
  The comments delimited by percent-signs "%%"
  are considered as whitespace. String quotes are used to indicate
  a symbol to be read without considering its special significance
  as a token.
%

%===========================BASE COMPONENT===================================%

%------BRACKETING OPERATORS-------%
prefix	"("	0	right & check ")"    $
delim	")"	$
infixd	"("	30 0	left . if pkgcheck(token) ne ")" then rightlist & check ")"  $
delim	","	$
infixd	"{"	30 0	"APPLY" . ["FUNCTION", left] . rightlist & check "}" $
delim	"}" $
prefix	"["	0	if pkgcheck(token) ne "]" then
			 (let a = "LIST".rightlist;
			  if pkgcheck(token) = ")" then ["CIRC",a] else a)
			& check !'(] /)) $
define	"CIRC"(x); x & cdr last x := x$
delim	"]"	$
infixd	"["	30 0 
	if pkgcheck(token) = "{" then (advance;
			     sublis(['a'.left, 'b'.right],
				    'mapcar{function a . b}')&
			     check "}")
	else "MAPCAR" . ["FUNCTION", left] . rightlist
	& check "]" $
prefix	"OCT"	0	(\cibase; check "("; right)(8) & check ")" $

%---------LITERAL OPERATORS----------%
prefix	"'"	0	is "QUOTE" & check "'" $
delim	"'" $
prefix	"#"	25	token & advance   $  % removes significance of token %
prefix	"="	25	eval right  $  % for on the spot computation %
 
%--------DECLARATIVE OPERATORS---------%
prefix	"\"	0	"LAMBDA".(getvarlist & check ";"). deprognify(right)
			& if pkgcheck(token) = "\" then advance $
delim	"\"	$
prefix	"LET"	0
new vars, argts, packflag;
while pkgcheck(token) not isin !'(/; in) do
  (vars := vars @ getvarlist;
   check !'(be /:= =);
   argts := (if pkgcheck(token) = "{" then ["&UNP", advance;right & packflag:=t; check "}"]
	    else parse 1) . argts;
   if pkgcheck(token) = "," then advance);
advance;
if packflag then
  (argts := reverse for i in argts collect
	if car i = "&UNP" then cadr i else ['list', i];
   ["APPLY", ["FUNCTION", "LAMBDA".vars.deprognify right],
	     if length argts = 1 then car argts else "APPEND".argts])
else ("LAMBDA".vars.deprognify right) . nreverse argts  $

prefix	"PROG"	0	"PROG" . (getvarlist & check ";") . deprognify(right) $
prefix	"NEW"	0
	"PROG" .
	(getvarlist & check ";") . 
	let x = deprognify(right); let y = last x; car y := ["RETURN", car y]; x $
prefix	"SPECIAL" 1	["DECLARE", ("SPECIAL" . getvarlist)]   $
prefix	"LITERAL" 1	"LITERAL" . rightlist $

define fexpr "CGOLARRAY" (x);
if pkgcheck(token) = "(" then (advance; car x . (\y;["SUB1",y])[parselist(0, ",")] & check ")")
else if pkgcheck(token) = ":=" then (advance; ["FILLARRAY", car x, parse 1])
else car x $

prefix	"ARRAY"	0	if pkgcheck(token) isin !'(/( { [) then "ARRAY"
else let names = getvarlist;
let oldnuds = for name in names collect cnud of name;
for name in names do
cnud of name := ["LAMBDA", nil, ["CGOLARRAY", name]];
  if pkgcheck(token) = "(" then
  (advance; let dims = rightlist;
  check ")"; let type = if pkgcheck(token) isin !'(fixnum flonum nil t) then
  (token&advance) else t;
  let source = if pkgcheck(token) isin !'(/:= =) then (advance; parse 1);
  if pkgcheck(token) = ";" then
  (advance;
   ("LAMBDA" . names . (if source then for name in names collect
		["FILLARRAY", name, source])
			@ deprognify right) .
	for name in names collect "ARRAY" . nil . type . dims)
  else
  "PROG2" . nil . ["QUOTE", car names] .
    for name in names coalesce
	["DEFPROP", name, "NUD" of name, "NUD"] .
	["SETQ", name, "ARRAY" . nil . type . dims] .
	 if source then [["FILLARRAY", name, source]])
  else if pkgcheck(token) = ";" then (advance;right)
& for name in names, oldnud in oldnuds do
    if oldnud then cnud of name := oldnud
    else remprop(name,cnud) $

prefix	"DIM"	25	["CDR", ["ARRAYDIMS", right]] $

%--------CONTROL OPERATORS---------%
"RBP" of "EVAL" := 1 $
infixm	";"	1	is "PROGN" $
infixr	"&"	1	["PROG2", nil, left, right] $
prefix	"IF"	2	"COND" . (right . (check "THEN"; deprognify(right)))
			. (if pkgcheck(token) eq "ELSE" then
	(advance; let x=right; if not atom x and car x = "COND" 
                                  then cdr x else [t . deprognify(x)])) $
delim	"THEN"	$
delim	"ELSE"	$
"RBP" of "RETURN" := 1$
"RBP" of "GO" := 1$
prefix	"WHILE"	2	"DO" . nil . [NOTify(right)] . (check "DO"; deprognify(right)) $
prefix	"REPEAT" 2	["DO", nil, ["PROG2" .
				     deprognify(right) @
				     deprognify(check "UNTIL";right)]] $
delim	"DO"  $

prefix	"FOR"	1 
new pars, argts, inon, fcn, body;
pars:= [token]; inon := advance; advance;
fcn := assoc(inon, !'((in (do mapc) (collect mapcar) (coalesce mapcan))
 		      (on (do map) (collect maplist) (coalesce mapcon))));
if fcn then fcn := cdr fcn 
  else cgolerr(inon cat " FOUND WHERE IN OR ON EXPECTED", 2,t);
argts := [right];
while pkgcheck(token) eq "," do
   (pars := advance . pars; advance; check inon; argts := right . argts);
fcn := assoc(pkgcheck(token), fcn); if fcn then fcn := cadr fcn
      else cgolerr(token cat " FOUND WHERE DO, COLLECT OR COALESCE EXPECTED",2,t);
advance; argts := nreverse argts; pars := nreverse pars; body := right;
if fcn = "MAPC" and and{(\x;not atom x and car x = "TO")[argts]}
	then "DO" .
	     (for p in pars, a in argts collect
 	       [p, cadr a, if cadddr a = 1 then ["ADD1", p]
					   else ["PLUS", p, cadddr a]]) .
	     [ORify((\p,a; ["GREATERP", p, caddr a])[pars,argts])] .
	     deprognify(body)
else fcn . ["FUNCTION", if cdr body = pars and atom car body then car body
			else ["LAMBDA", pars, body]] . argts $

delim "IN"; delim "ON"; delim "COLLECT"; delim "COALESCE" $

prefix "ITER" 2 
	new ivars, whenvar, result, body;
	while assoc(pkgcheck(token), !'(
(for    #$     ivars := (token .
		          if advance = ":=" then (advance; right exists) .
		          if pkgcheck(token) = "STEP" then
			 [if advance = "DITTO" then (advance; it) else right])
	                       . ivars$)
(when   #$     whenvar := right$)
(until  #$     whenvar := right$)
(while  #$     whenvar := ["NOT", right]$)
(return #$     result  := right$)
(do     #$     body    := right$)))
	       exists do (advance; eval cadr it);
	if not( ivars or whenvar or result or body) then body := right;
        ["DO", nreverse ivars, [whenvar, result]] @
           if not atom body and car body eq "PROGN"
              then cdr body else ncons body  $

delim "FOR", "WHEN", "UNTIL", "WHILE", "STEP", "RETURN"$
infix "TO" 18 "TO" . left . right . [if pkgcheck(token) = "BY" then (advance;right) else 1] $
delim "BY" $

define	"TO"(aa, b, c);
if aa>b then nil
else new x; x := [aa] & while b>=aa:=aa+c do x := cdr(cdr x := [aa]) $

infixd	"LOTSOF" 19 1	["DO", '?*i', left, '?*i-1', '?*i<=0', right] $

%------OTHER OPERATORS---------%

newtok ":=" $

"NUD" of "CGOLPRINT" := '\;  ["CGOLPRINT", parse 1]' $
"NUD" of "CGOLPRIN1" := '\; ["CGOLPRIN1", parse 1]' $

%------STORAGE OPERATORS-------%
infixd	":="	25 1	if left isatom then is "SETQ"
			else if car left eq "GET" then
				["PUTPROP",cadr(left),right,caddr(left)]
			else if "STOREFORM" of car left exists then
				(\x;sublis(["LEFT".cadr left, "RIGHT".right], x))(it)
			else is "STORE" $ %prop%

'storeform' of 'car'   := 'rplaca(left,#right)';
'storeform' of 'cdr'   := 'rplacd(left,#right)';
'storeform' of 'arg'   := 'setarg(left,#right)';
'storeform' of 'plist' := 'setplist(left,#right)';
'storeform' of 'status' := 'sstatus(left,#right)' $

for i in !'(toplevel breaklevel who2 who3 ttyscan ttyread ttyint gctime) do
	"NUD" of i := subst(i, "I", !'(lambda () '(status i))) $

infixr	"OF"	26	["GET", right, left]  $
infixr	"OFQ"	26	["GET", right, ["QUOTE", left]]  $

%-----LOGICAL OPERATORS-------%
"RBP" of "NOT" := 9 $
infix	"NOT"	10	["NOT", funcall(led, left)] $
infixm	"AND"	8	is "AND" $
infixm	"OR"	7	is "OR" $

%-----RELATIONAL OPERATORS-----%
newtok "=#"; newtok "=?$"; newtok "<#"; newtok ">#";
newtok "<?$"; newtok ">?$"; newtok "<="; newtok ">=" $
infix	"="	10	is ARITH("EQUAL") $
infix	"NE"	10	["NOT", is ARITH("EQUAL")] $
infix	"EQ"	10	is "EQ" $
infixm	"<"	10	is ARITH("LESSP") $
infixm	">"	10	is ARITH("GREATERP") $
infix	"=#"	10	is "=" $
infix	"=?$"	10	is "=" $  % for those who care %
infix	"<#"	10	is "<" $
infix	">#"	10	is ">" $
infix	"<?$"	10	is "<" $  %  "    "    "   "   %
infix	">?$"	10	is ">" $  %  "    "    "   "   %
infix	"<="	10	["NOT", is ARITH("GREATERP")] $
infix	">="	10	["NOT", is ARITH("LESSP")] $
infix	"|"	10	[ARITH("ZEROP"), [ARITH("REMAINDER"), right, left]] $
infix	"ISIN"	10	is "MEMBER"  $
suffix	"ISATOM" 10	is "ATOM"   $  %  atom x  also works %
suffix	"ISNUM"	10	is "NUMBERP"   $ % numberp x also works %
suffix	"EXISTS" 10	["SETQ", "IT", left] $
"RBP" of "NULL" := 10 $

%--------LIST OPERATORS--------%
infixr	"."	15	is "CONS" $
infixm	"@"	15	is "APPEND" $

%--------SET OPERATORS---------%
prefix	"{"	0	"GATHER" . if pkgcheck(token) ne "}" then rightlist & check "}" $
infixm	""	16	is "UNION" $
infixm	""	16	is "INTERSECT" $
prefix	"~"	16	is "SETDIFF" $
infixm	"~"	16	is "SETDIFF" $
infixm	""	10	is "ELEMENTP" $
infixm	""	10	is "SUBSETP" $

!(PROGN (MAPC #'(LAMBDA (U)
                 ;; Autoload (or other "functional") property is needed
                 ;; for parsing some files.
                 (OR (FBOUNDP U) (PUTPROP U '((DSK LIBLSP)SETS FASL) 'AUTOLOAD)))
               '(GATHER UNION INTERSECT SETDIFF ELEMENTS ELEMENTP SUBSETP
                        SYMDIFF CLEARSETS))
         (IF (FBOUNDP '*LEXPR)
             (EVAL '(*LEXPR UNION INTERSECT SETDIFF SYMDIFF)))) $

%--------STRING OPERATORS-----%
infixm	"^"	18	is "CAT" $
infixm	"CAT"	18	is "CAT" $

%-----ARITHMETIC OPERATORS-----%
prefix	"|"	19	is ARITH("ABS")  & check "|"   $

prefix	"+"	20	if pkgcheck(token) isin !'(/( { [) then ARITH("PLUS") else right $
infixm	"+"	20	is ARITH("PLUS") $
infixm	"-"	20	is ARITH("DIFFERENCE") $
prefix	"-"	20	is ARITH("MINUS") $
nilfix	"*"		if pkgcheck(token) isin !'(/( [ {) then ARITH("TIMES") else "*" $
infixm	"*"	21	is ARITH("TIMES") $
infixm	"/"	21	[ARITH("QUOTIENT"), left, [ARITH("FLOAT"), right]] $
newtok	"/:"	$
infixm	"/:"	21	is ARITH("QUOTIENT") $
infix	"REM"	21	is ARITH("REMAINDER") $

%
define a "MOD" b, 21; let x := a rem b;
	    if minusp a ne minusp b and not zerop x then x+b else x $
%

newtok	"**" $
infixr	"**"	22	is ARITH("EXPT") $

%-----FIXNUM OPERATORS--------%
newtok "+#"; newtok "-#"; newtok "*#"; newtok "/#"; newtok "\\" $
infixm	"+#"	20	is "+" $
infixm	"-#"	20	is "-" $
infixm	"*#"	21	is "*" $
infixm	"/#"	21	is "/" $
infix	"\\"	19	is "\\" $

%-----FLONUM OPERATORS---------%
newtok "+?$"; newtok "-?$"; newtok "*?$"; newtok "/?$" $
infixm	"+?$"	20	is "+?$" $
infixm	"-?$"	20	is "-?$" $
infixm	"*?$"	21	is "*?$" $
infixm	"/?$"	21	is "/?$" $

%-----BIT-VECTOR OPERATORS-----%
newtok ":N:"; newtok ":A:"; newtok ":V:"; newtok ":X:"; newtok ":^:" $
prefix	":N:"	21	["BOOLE", 12, 0, right] $
infixm	":A:"	21	"BOOLE" . 1 . left . rightrep $
infixm	":V:"	20	"BOOLE" . 7 . left . rightrep $
infixm	":X:"	20	"BOOLE" . 6 . left . rightrep $
infix	":^:"	22	is "LSH" $

%-----I/O OPERATORS-----%
"RBP" of "PRINT" := 2 $
"RBP" of "PRINC" := 2 $
"RBP" of "PRIN1" := 2 $
prefix	"WRITE"	2	
   subst("LIST".rightlist,'x','newline;for i in x do princ i;princ " "')$
nilfix	"NEWLINE"	is "TERPRI"  $
nilfix	"UREAD"		"UREAD" . gettokens $
nilfix	"UWRITE"	"UWRITE" . gettokens $
nilfix	"UFILE"		"UFILE" . gettokens $

%==================INITIALIZATION================%

syntax?-needed := t;
silence := -1; defbp := 25;
nudl := !'(nud); ledl := !'(led); lbpl := !'(lbp);
cnud := "NUD"; cled := "LED"; clbp := "LBP";
fun := "TOP-LEVEL";
language_alist:= nil;
arithmetic_alist := nil;
sstatus(feature, #cgol)  $


=EXIT$


;; 3:14pm  Saturday, 6 November 1982 -George Carrette.
;; CGOL may be bootstrapped via "cross-read/printing"
;; from any existing implementation. Use a simple READ/PRINT loop,
;; with "#+" conditional information set appropriately.
;; Possible problems:
;; (1) From MACLISP, you will need to make sure that colon ":" is
;;     slashified where it needs to be in the output file.
;;     The symbols to look for have pnames: ":" ":=" ":N:" ":A:"
;;     ":V:" ":^:"
;; (2) From the LISPM, make sure that the package you are in is
;;     CGOL, or some other non-SI, or non-USER package.
;;     Otherwise :FOO or SI:FOO will print incorrectly.
;; (3) In NIL, use a non-SI package, such as USER.
