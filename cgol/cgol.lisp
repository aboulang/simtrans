;;;-*-Base:10.; Mode:lisp; Package:CGOL-*-
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                                                                      ;;;
;;;	Based on a theory of parsing presented in:                       ;;;
;;;                                                                      ;;;
;;;	    Pratt, Vaughan R., ``Top Down Operator Precedence,''         ;;;
;;;	    ACM Symposium on Principles of Programming Languages         ;;;
;;;	    Boston, MA; October, 1973.                                   ;;;
;;;                                                                      ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; The following terms may be useful in deciphering this code:
;;;
;;; NUD -- NUll left Denotation (op has nothing to its left (prefix))
;;; LED -- LEft Denotation	(op has something to left (postfix or infix))
;;;
;;; LBP -- Left Binding Power  (the stickiness to the left)
;;; RBP -- Right Binding Power (the stickiness to the right)


;; Blame for bringing up this thing up on the LISPM and in NIL may be
;; left to George Carrette. There was a need to run some of Pratt's
;; code, and one thing lead to another.
;; A note to all parser hackers: A Pratt parser in lisp is a neat and
;; powerfull thing, fast and incrementally extensible. If you want to
;; parse any computer language I can recommend it from good experience.
;; With it you can do things using a simple context-dependant parse
;; rather than a context-independant parse with hairy grammer and grammer
;; compiler.

#+(OR Maclisp NIL)        (HERALD CGOL)	       
#+Maclisp
(PROGN 'compile
       (declare (*lexpr cat)
		(*expr cgol-enter cgol-exit cgoltoken cgoltyipeek
		       puttok cgolerr)
		(MUZZLED T))
       (EVAL-WHEN (EVAL LOAD COMPILE)
	 (AND (STATUS FEATURE COMPLR)
	      (PROGN (SPECIAL IT) (*LEXPR CAT) (*EXPR PARSE)))))

#+(OR LISPM NIL)
(EVAL-WHEN (EVAL COMPILE LOAD)
  (SPECIAL IT))

;; First step: The tokenizer.

#+Maclisp
(progn 'compile
       (or (get 'CGRUB 'version) (load '((PRATT)CGRUB)))
       (eval-when (compile)
	 (macros ())
	 (SETQ DEFMACRO-FOR-COMPILING ())))

(DEFVAR EOFM (LIST 'EOFM))

(defvar token ())
(defvar stringnud ())
(defvar cibase 10.)
(defvar cgolerr () "controls throws for eof condition")
(defvar ctoken-table ())
(defvar ret-nud () "The instance variable of a recyled closure")
(defun ret-nud () ret-nud)
(defvar fun 'TOP-LEVEL)
(defvar silence -1)
(defvar free-kons ())
(defvar ctyipeek () "keep our own one-character look-ahead.")
(defvar cgol-input ())

#+(or Lispm Maclisp)
(DEFUN NORMALIZE-READ-ARGS (READ-ARGS)
  #+Lispm
  (MULTIPLE-VALUE-BIND (STREAM EOF)
		       (SI:DECODE-READ-ARGS READ-ARGS)
    (CONS STREAM EOF))
  #+Maclisp
  (LET ((STREAM (CAR READ-ARGS))
	(EOF (CADR READ-ARGS)))
    ;; apply the correction.
    (COND ((AND (NULL (CDR READ-ARGS))
		(NOT (OR (EQ STREAM T)
			 (SFAP STREAM)
			 (FILEP STREAM))))
	   (SETQ STREAM () EOF STREAM)))
    (COND ((EQ STREAM T)
	   (SETQ STREAM TYI))
	  ((EQ STREAM ())
	   (IF ^Q (SETQ STREAM INFILE) (SETQ STREAM TYI))))
    (CONS STREAM EOF)))


#+(or Lispm Maclisp)
(DEFUN CGOLREAD (&REST READ-ARGS &AUX STREAM EOFM)
  (SETQ READ-ARGS (NORMALIZE-READ-ARGS READ-ARGS))
  (SETQ STREAM (CAR READ-ARGS)
	EOFM (CDR READ-ARGS))
  (LET ((WHICH-OPERATIONS
	 #+LISPM
	 (FUNCALL STREAM ':WHICH-OPERATIONS)
	 #+MACLISP
	 (AND (SFAP STREAM) (SFA-CALL STREAM 'WHICH-OPERATIONS ()))))
    (*CATCH 'CGOLERR
      #+MACLISP
      (COND ((MEMQ 'RUBOUT-HANDLER WHICH-OPERATIONS)
	     (SFA-CALL STREAM 'RUBOUT-HANDLER #'TOPLEVEL-PARSE))
	    ('ELSE
	     (TOPLEVEL-PARSE STREAM)))
      #+LISPM
      (COND ((AND (NOT RUBOUT-HANDLER) (MEMQ ':RUBOUT-HANDLER WHICH-OPERATIONS))
	     (FUNCALL STREAM ':RUBOUT-HANDLER '() #'TOPLEVEL-PARSE STREAM))
	    ('ELSE
	     (TOPLEVEL-PARSE STREAM))))))

#+NIL
(DEFUN CGOLREAD (&RESTV READ-ARGS)
  (*CATCH 'CGOLERR
    (SI:READ-APPLY ':CGOLREAD #'CGOLREAD-RAW READ-ARGS)))

#+NIL
(DEFUN CGOLREAD-RAW (STREAM &OPTIONAL EOFM)
  (TOPLEVEL-PARSE STREAM))

(DEFUN TOPLEVEL-PARSE (CGOL-INPUT)
  (TOPLEVEL-PARSE-1 ()))

#+LISPM
(DEFUN CGOLREAD-RAW-WITH-P (CGOL-INPUT PEEK)
  (TOPLEVEL-PARSE-1 PEEK))

(DEFUN TOPLEVEL-PARSE-1 (CTYIPEEK
			 &AUX
			 ;; State variables.
			 (CGOLERR T) TOKEN STRINGNUD RET-NUD
			 (FUN 'TOP-LEVEL))
   ;; may throw the eof marker here.
  (COND ((EQ (ADVANCE) ')
	 ;; KLUDGE for old CGOL source files.
	 '')
	('ELSE
	 (SETQ CGOLERR ())
	 (PARSE -1))))

(DEFUN CGOLERR (MESSAGE LEVEL FATALP)
  (COND ((AND FATALP CGOLERR)
	 (*THROW 'CGOLERR EOFM))
	('ELSE
	 #+Maclisp
	 (PROGN  (COND ((> LEVEL SILENCE)
			(TERPRI MSGFILES)
			(PRINC MESSAGE msgfiles)
			(princ " IN " msgfiles)
			(princ FUN msgfiles)
			(terpri msgfiles)))
		 (if fatalp (force-rubout cgol-input)))
	 #+(or Lispm NIL)
	 (PROGN LEVEL
		(CERROR (NOT FATALP) ;; procedable sometimes.
			() ;; Not restartable.
			#+NIL :READ-ERROR
			#-NIL
			() ;; no condition given, since READ uses (FERROR () ...)
			"~A IN ~A"
			MESSAGE FUN)))))

#+Maclisp
(DEFUN FORCE-RUBOUT (stream)
  (COND ((and (sfap stream)
	      (memq 'force-rubout (sfa-call stream 'which-operations ())))
	 (SFA-CALL STREAM 'FORCE-RUBOUT ()))
	('ELSE
	 (COND ((AND (FILEP STREAM)
		     (LET ((MODE (STATUS FILEMODE STREAM)))
		       (AND (MEMQ 'FILEPOS (CDR MODE))
			    (MEMQ 'DSK (CAR MODE)))))
		(FILEPOS STREAM (MAX 0 (- (FILEPOS STREAM) 50.)))
		(DO ((J 0 (1+ J))
		     (C))
		    ((> J 100.))
		  (SETQ C (TYI STREAM -1))
		  (OR (= C -1) (= C #^C) (TYO C MSGFILES))
		  )))
	 (DO ()
	     ((= (TYI STREAM -1) -1)
	      (cgolerr "End of file while forcing rubout" 3 t))))))

(defmacro mtyi ()
  #+(OR MACLISP NIL)
  '(tyi cgol-input -1)
  #+LISPM
  '(LET ((C (FUNCALL CGOL-INPUT ':TYI)))
     (IF (NULL C) -1 C)))

(defun ctyi ()
  (IF (NULL CTYIPEEK)
      (MTYI)
      (PROG1 CTYIPEEK
	     (SETQ CTYIPEEK ()))))

(defun ctyipeek () 
  (IF (NULL CTYIPEEK)
      (SETQ CTYIPEEK (MTYI))
      CTYIPEEK))
(defun cuntyi (c)
  (SETQ CTYIPEEK C))
	 
(defun cgoltyipeek ()(ctyipeek))

#+NIL(DECLARE (SPECIAL READTABLE))

(DEFVAR CREAD-READTABLE READTABLE)

(defun cread ()
  (LET ((READTABLE CREAD-READTABLE))
    (read cgol-input eofm)))

;;; Macros and functions used by the tokenizer loop.

(defmacro return-token (c l &optional (quoted-p 'quoted-p) (reversed-p t))
  `(progn ,(if c `(cuntyi ,c))
	  (return (make-token ,l ,quoted-p ,reversed-p))))

;; The tokenizer is a simple loop with the character TYI'd pushed on the
;; token buffer after a series of special cases are checked.
;; The boolean state variables could be replaced with predicates
;; that look back on what in in the buffer, however the present implementation
;; is highly straightforward.

(defun cgoltoken ()
  (do ((l () (KONS c l))
       (c (cskip-whitespace) (ctyi))
       (temp)
       (quoted-p ())
       (fixnum-p ())
       (flonum-p ())
       (expt-p ())
       (digit-after-expt-p ())
       )
      (())
    (cond ((= c -1)
	   (if (null l)
	       (cgolerr "EOF encountered inside cgol-exp - CGOLREAD" 2 t)
	       (return-token c l)))
	  ((or (= c #/$) (= c #\ALT))
	   (if (null l)
	       (return ')
	       (return-token c l)))
	  ((= c #/!)
	   (if (null l)
	       (return (cread))
	       (return-token c l)))
	  ((= c #/?)
	   (setq quoted-p t)
	   (setq flonum-p ())
	   (setq fixnum-p ())
	   (setq c (ctyi)))
	  ((= c #/")
	   (if (null l)
	       (let ((x (ctoken-string)))
		 (setq ret-nud `',x
		       stringnud #'ret-nud)
		 (return x))
	       (return-token c l)))
	  ((cwhitespacep c)
	   (return-token c l))
	  ((= c #/.)
	   (cond ((null l)
		  (if (cdigit-p (ctyipeek))
		      (setq fixnum-p () flonum-p t)
		      (return '/.)))
		 ((null fixnum-p)
		  (return-token c l t))
		 ('ELSE
		  (if fixnum-p (setq flonum-p t))
		  (setq fixnum-p ()))))
	  ((and (or (= c #/E) (= c #/e))
		flonum-p
		(not expt-p))
	   (let ((p (ctyipeek)))
	     (if (not (or (= p #/+)
			  (= p #/-)
			  (cdigit-p p)))
		 (return-token c l)))
	   (setq expt-p t))
	  ((cdigit-p c)
	   (if (null l)
	       (setq fixnum-p t))
	   (if expt-p (setq digit-after-expt-p t)))
	  ((and (or (= c #/+) (= c #/-))
		flonum-p
		expt-p
		(not digit-after-expt-p)
		(cdigit-p (ctyipeek))))
	  ((setq temp (clookup (setq c (ICHAR-UPCASE c)) ctoken-table))
	   (if (null l)
	       (return-token () (KONS c (cfollow-tail (cdr temp))) t ())
	       (return-token c l)))
	  ('ELSE
	   (setq fixnum-p ())
	   (setq flonum-p ())))))


(defun cwhitespacep (c)
  (or (= c #\SP) (= c #\CR) (= c #\LF) (= c #\TAB) (= c #\FF)
      (= c #/%)))

(defun cskip-whitespace ()
  (do ((commentp ())(c))
      (())
    (setq c (ctyi))
    (cond ((= c #/%)
	   (setq commentp (not commentp)))
	  ((cwhitespacep c))
	  ((NOT COMMENTP)
	   (RETURN C)))))

(defun clookup (x y)
  #+MACLISP (assoc x y)
  #-MACLISP (ASSQ X Y))

(defun initialize-multi-character-token-table (string)
  (setq ctoken-table
	(mapcar #'list (exploden string))))

(defun cfollow-tail (alist)
  ;; this way of recognizing tokens is taken from the original cgol,
  ;; is fast and easy and passes all tokens which are subtokens
  ;; of explicitely defined tokens.
  (IF (NULL ALIST) ()
      (let ((c (ICHAR-UPCASE (ctyipeek))))
	(cond ((setq alist (clookup c alist))
	       (ctyi)
	       (KONS c (cfollow-tail (cdr alist))))
	      ('ELSE
	       ())))))

(defmacro with-working-cons (&rest l)
  #+LISPM`(let ((default-cons-area working-storage-area))
	    ,@l)
  #-LISPM `(progn ,@l))

(defun puttok (token)
  ;; entry point for defining tokens.
  (with-working-cons
    (let ((l (exploden token)))
      (or (clookup (car l) ctoken-table)
	  (error "token with illegal first character" token))
      (setq ctoken-table (inserttok l ctoken-table)))))

(defun inserttok (tok toktable) 
  (if (null tok)
      toktable
      (let ((st (clookup (car tok) toktable)))
	(cond ((null st)
	       (cons (cons (car tok)
			   (inserttok (cdr tok) ()))
		     toktable))
	      ('ELSE
	       (rplacd st (inserttok (cdr tok) (cdr st)))
	       toktable)))))

(defun ctoken-string ()
  ;; this is as in the original cgol, #/? is used to quote
  ;; #/$ or #/? and #/" is used to quote #/".
  (do ((c (ctyi) (ctyi))
       (l () (KONS c l)))
      (())
    (cond ((or (= c #/$) (= c #\ALT))
	   ;; a little Dwim.
	   (cgolerr "tokenizer has inserted missing /" before " 0 ())
	   (return-token c l ()))
	  ((= c #/")
	   (if (= (ctyipeek) #/")
	       (ctyi)
	       (return-token () l ())))
	  ((and (= c #/?) (or (= (ctyipeek) #/$)
			      (= (ctyipeek) #\ALT)))
	   (setq c (ctyi))))))
	   
(defun cdigit-p (x) (not (or (< x #/0) (> x #/9))))

(DEFUN ICHAR-UPCASE (C)
  (IF (AND (>= C #/a) (<= C #/z)) (- C #.(- #/a #/A)) C))

(defun make-token  (l do-not-try-as-number-p rp)
  ;; takes the stack of characters and makes a token.
  (if rp (setq l (nreverse l)))
  (prog1
    (if (or do-not-try-as-number-p
	    (not (ok-as-number-p l)))
	(implode l)
	(let ((ibase cibase))
	  (creadlist l)))
    (reklaim l)
    ))

(defun creadlist (l)
  (let ((readtable cread-readtable))
    (readlist l)))

(defun ok-as-number-p (l)
  ;; its more efficient to determine the type of
  ;; the token by collecting information in state variables
  ;; as it is read. However we aren't that sure of our book-keeping.
  (numberp (car (let ((errset ()))
		  (errset (creadlist l) ())))))

;; Keeping our own free-list is a way to use lists for stacks without the
;; overhead of garbage collection. It works everywhere and is a simple add-on,
;; whereas string and fill-pointer hair is not.

(defun kons (kar kdr)
  (if free-kons
      (PROGN
	(rplaca free-kons kar)
	(rplacd (prog1 free-kons (setq free-kons (cdr free-kons)))
		kdr))
      (with-working-cons
	(cons kar kdr))))

(defun reklaim (l)
  (setq free-kons (nconc l free-kons)))


;; Interface functions.

(defun cgol-/#-readmacro (stream)
  ;; #FOOBAR is a syntax escape to the FOOBAR language.
  (funcall (get-read (if (member (tyipeek () stream)
				 '(#\SP #\CR #\TAB #\FF))
			 'CGOL
			 (let ((cgol-input stream))
			   (cread))))
	   stream))

(defprop cgol cgolread read)
(defprop rat ratread read)

(defun get-read (language)
  (if (symbolp language)
      (or (get language 'read)
	  (cgolerr (cat language " is an undefined language") 3 t))
      (cgolerr (cat language " not a language symbol") 3 t)))

(defvar rat-arithmetic_alist
  '((plus . rat-plus)
    (minus . rat-minus)
    (difference . rat-difference)
    (times . rat-times)
    (float . progn)
    (quotient . rat-quotient)
    (equal . rat-equal)
    (lessp . rat-lessp)
    (greaterp . rat-greaterp)
    (expt . rat-expt)))

(defun ratread (#+NIL &restv #-NIL &rest l)
  (let ((arithmetic_alist rat-arithmetic_alist))
    (declare (special arithmetic_alist))
    (lexpr-funcall #'cgolread l)))


#+Maclisp 
(defsharp / (ignore-arg)
  (cgol-/#-readmacro ()))

#+Maclisp
(defsharp /$ (ignore-arg)
  (cgol-/#-readmacro ()))

#+Lispm
(set-syntax-/#-macro-char #\ALT
			  #'(LAMBDA (IGNORE-LIST-SO-FAR STREAM)
			      (CGOL-/#-READMACRO STREAM)))
#+Lispm
(set-syntax-/#-macro-char #/$
			  #'(LAMBDA (IGNORE-LIST-SO-FAR STREAM)
			      (CGOL-/#-READMACRO STREAM))
			  cread-readtable)

#+NIL
(DEFUN SHARP-READ-ALT ()
  (CGOLREAD-RAW STANDARD-INPUT SI:EOF-VAL))
#+NIL
(SI:ENTER-SHARP-MACRO-CHAR ~\ALT #'SHARP-READ-ALT)
#+NIL
(SI:ENTER-SHARP-MACRO-CHAR ~/$ #'SHARP-READ-ALT)


#+Maclisp
(progn 'compile
;; utility function useful to have in maclisp.
(eval-when (Eval compile)
  (or (get 'defstruct 'macro)
      (load '((lisp)struct))))
(defstruct (string-stream sfa conc-name (constructor make-string-stream-1)
			  (default-pointer self))
  char-list)
(defun make-string-stream (string)
  (make-string-stream-1 char-list (exploden string)))
(defun string-stream (self command arg)
  (caseq command
    ((which-operations) '(tyi tyipeek untyi))
    ((tyi) (pop (string-stream-char-list)))
    ((tyipeek) (car (string-stream-char-list)))
    ((untyi) (push arg (string-stream-char-list)))
    (t (error "unknown command to string-stream" command))))
)
    
;; Implementation of (CGOL) function to get into CGOL mode readtable.
#+Lispm
(progn 'compile

;; the idea here is to have a readtable such that every single
;; character causes CGOLREAD to be invoked. 

(Defvar cgol-invoking-readtable (copy-readtable si:initial-readtable))
(defvar cgol-invoking-read-char #\SP "Untyi'd by the cgol-invoking-read-macro")

(do ((char 0 (1+ char)))
    ((= char #o200))
  (set-syntax-from-char char #/' cgol-invoking-readtable))

(defun cgol-invoking-read-macro (ignore-list-so-far stream)
  (CGOLREAD-RAW-WITH-P STREAM CGOL-INVOKING-READ-CHAR))

(do ((char 0 (1+ char)))
    ((= char #o200))
  (set-syntax-macro-char char
			 (LET-CLOSED ((cgol-invoking-READ-CHAR CHAR))
			   #'cgol-invoking-read-macro)
			 cgol-invoking-readtable))
)

#+NIL
(DEFUN CGOL-TOPLEVEL-READ ()
  (*CATCH 'CGOLERR
    (CGOLREAD-RAW CGOL-INPUT SI:EOF-VAL)))
#+NIL
(DEFVAR CGOL-INVOKING-READTABLE
  (LET ((READTABLE (SI:CREATE-READTABLE)))
    (DECLARE (SPECIAL READTABLE))
    (SI:SET-READTABLE-TOPLEVEL-READ #'CGOL-TOPLEVEL-READ)
    READTABLE))
#+NIL
(SI:ENTER-READTABLE "CGOL" CGOL-INVOKING-READTABLE)

(defvar read-prin1-stack ())

(defun cgol-enter (ignore-it)
  (push (cons #+MACLISP READ
	      #+(or LISPM NIL) READTABLE
	      PRIN1)
	read-prin1-stack)
  #+MACLISP (SETQ READ #'CGOLREAD)
  #+(or LISPM NIL) (SETQ READTABLE CGOL-INVOKING-READTABLE))

(defun cgol-exit ()
  (let ((a (pop read-prin1-stack)))
    (setq #+MACLISP READ #+(or LISPM NIL) READTABLE (CAR A)
	  prin1 (cdr a))))


;; Defun compatibility.
#+NIL
(DEFMACRO CGOL-DEFUN (NAME ARGLIST &REST BODY &AUX (TYPE 'EXPR))
  (COND ((MEMQ ARGLIST '(EXPR FEXPR))
	 (SETQ TYPE ARGLIST
	       ARGLIST (POP BODY)))
	((AND ARGLIST ; hack for cross-compilation
	      (SYMBOLP ARGLIST))
	 (SETQ TYPE 'LEXPR
	       ARGLIST (LIST ARGLIST))))
  (COND ((EQ TYPE 'EXPR)
	 `(DEFUN ,NAME ,ARGLIST ,@BODY))
	((EQ TYPE 'FEXPR)
	 (LET ((FAKEN (SYMBOLCONC NAME " FEXPR")))
	   `(PROGN 'COMPILE
		   (DEFMACRO ,NAME (&REST L)
		     `(,',FAKEN ',L))
		   (DEFUN ,FAKEN ,ARGLIST ,@BODY))))
	((EQ TYPE 'LEXPR)
	 `(DEFUN ,NAME (&RESTV SI:*LEXPR-ARGVECTOR*)
	    ((LAMBDA ,ARGLIST ,@BODY) (VECTOR-LENGTH SI:*LEXPR-ARGVECTOR*))))))

#+NIL
(DEFUN AND (&RESTV ARGV)
  (DO ((J 0 (1+& J))
       (N (VECTOR-LENGTH ARGV)))
      ((=& J N) T)
    (OR (VREF ARGV J) (RETURN ()))))

(DEFUN FORMCHECK (FORM)
  ;; check for various obsolete usages.
  (COND ((ATOM FORM) FORM)
	((AND (EQ (CAR FORM) 'THROW)
	      (= (LENGTH FORM) 2))
	 `(*THROW 'CGOL-USER-THROW-TAG ,(CADR FORM)))
	('ELSE
	 FORM)))

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
