;;;-*-Base:10.; Mode:lisp; Package: CGOL-*-
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

;; Apology:
;; Blame for bringing up this thing up on the LISPM and in NIL may be
;; left to George Carrette, late of MIT's Mathlab and NIL groups and now at
;; Lisp Machines Inc. There was a desire to run some of Vaughan Pratt's hairy
;; code, and one thing lead to another. William Dubuque must share credit
;; for keeping this CGOL thing alive from a user perspective and spreading the
;; word about it. 
;;
;; A note to all parser hackers: A Pratt parser in lisp is a neat and
;; powerful thing, fast and incrementally extensible. If you want to
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
			      (CGOL-/#-READMACRO STREAM)))

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


;;AFTER CODE HERE..............


(DECLARE (SPECIAL CIBASE TOKEN STRINGNUD SYNTAX-NEEDED DRBP FUN DENTYPE
		  ISFUN SILENCE DEFBP IVARS WHENVAR RESULT BODY NUDL LEDL
		  LBPL CNUD CLED CLBP LANGUAGE_ALIST ARITHMETIC_ALIST))

(PROGN 'COMPILE
       (DEFUN (ADVANCE NUD) () (LIST (PROG2 () 'ADVANCE)))
       (DEFUN ADVANCE () 
	 (SETQ STRINGNUD ())
	 (SETQ TOKEN (CGOLTOKEN))
	 TOKEN))

(DEFUN VERIFY (DEN) (COND (DEN (ADVANCE) DEN)))

(PROGN
 'COMPILE
 (DEFUN (NUDERR NUD) () (LIST (PROG2 () 'NUDERR)))
 (DEFUN NUDERR () 
   (COND ((AND (GETDEN LBPL) (NULL (FUNBOUNDP TOKEN)))
	  (CGOLERR (CAT TOKEN '| MISSING PRECEDING EXPRESSION|) 2. T))
	 (T ((LAMBDA (OP TP) 
	       (ADVANCE)
	       (LIST 'LAMBDA
		     ()
		     (LIST 'QUOTE
			   (COND ((AND (FUNBOUNDP OP)
				       (MEMBER TP '(9. 13. 32.))
				       (OR STRINGNUD
					   (AND (GETDEN NUDL)
						(NOT (EQUAL TOKEN
							    '|(|)))
					   (NOT (GETDEN LBPL))))
				  (LIST OP
					(PARSE (OR (GET OP 'RBP)
						   25.))))
				 (T OP)))))
	     TOKEN
	     (CGOLTYIPEEK))))))

(PROGN 'COMPILE
       (DEFUN (FUNBOUNDP NUD) () 
	 (LIST (PROG2 () 'FUNBOUNDP) (PROG2 () (PARSE 25.))))
       (DEFUN FUNBOUNDP (X) 
	 (AND (SYMBOLP X)
	      (OR (GETL X
			'(SUBR FSUBR LSUBR EXPR FEXPR LEXPR MACRO *EXPR
			  *FEXPR *LEXPR AUTOLOAD))
		  (FBOUNDP X)))))

(PROGN 'COMPILE
       (DEFUN (LEDERR NUD) () (LIST (PROG2 () 'LEDERR)))
       (DEFUN LEDERR () 
	 (CGOLERR (CAT TOKEN
		       '| IS NOT AN OPERATOR WITH A LEFT ARGUMENT|)
		  2.
		  T)))

(PROGN 'COMPILE
       (DEFVAR CGOL-PACKAGE (PKG-FIND-PACKAGE "CGOL"))
       (DEFUN GETDEN (INDL) 
	 (AND (SYMBOLP TOKEN)
	      (DO ((L INDL (CDR L))) 
		  ((NULL L)) 
	       (LET ((X (GET TOKEN (CAR L)))) (AND X (RETURN X))
		(AND (SETQ X (INTERN-SOFT TOKEN CGOL-PACKAGE))
		     (SETQ X (GET X (CAR L)))
		     (RETURN X)))))))

(PROGN 'COMPILE
       (DEFUN (NUD NUD) () (LIST (PROG2 () 'NUD)))
       (DEFUN NUD () 
	 (OR (VERIFY (OR STRINGNUD
			 (COND ((NUMBERP TOKEN)
				(LIST 'LAMBDA () TOKEN))
			       (T (GETDEN NUDL)))))
	     (NUDERR))))

(PROGN 'COMPILE
       (DEFUN (LED NUD) () (LIST (PROG2 () 'LED)))
       (DEFUN LED () (OR (VERIFY (GETDEN LEDL)) (LEDERR))))

(PROGN 'COMPILE
       (DEFUN (PARSE NUD) () 
	 (LIST (PROG2 () 'PARSE) (PROG2 () (PARSE 25.))))
       (DEFUN PARSE (RBP) 
	 (DO ((TRANSLATION (FUNCALL (NUD)) (FUNCALL (LED) TRANSLATION))) 
	     ((NOT (LESSP RBP (OR (GETDEN LBPL) 0.))) TRANSLATION) 
	  ())))

(PUTPROP ' (MINUS 1.) 'LBP)

(DEFUN CGOL FEXPR (A) (CGOL-ENTER A) ())

(PROGN 'COMPILE
       (DEFUN (EXIT NUD) () (LIST (PROG2 () 'EXIT)))
       (DEFUN EXIT () (CGOL-EXIT) ()))

(DEFUN SPEAK (X) 
  ((LAMBDA (LANG) 
     (COND (LANG (SETQ LANG (CDR LANG)))
	   (T (CGOLERR (CAT X '| is an unknown language|) 3. T)))
     (SETQ NUDL (CONS (CAR LANG) NUDL))
     (SETQ LEDL (CONS (CADR LANG) LEDL))
     (SETQ LBPL (CONS (CADDR LANG) LBPL))
     ())
   (ASSOC X LANGUAGE_ALIST)))

(PROGN 'COMPILE
       (DEFUN (FORGET NUD) () (LIST (PROG2 () 'FORGET)))
       (DEFUN FORGET () 
	 (AND (CDR NUDL)
	      (PROGN (SETQ NUDL (CDR NUDL))
		     (SETQ LEDL (CDR LEDL))
		     (SETQ LBPL (CDR LBPL))))
	 ()))

(PROGN 'COMPILE
       (DEFUN (RESETLANGUAGE NUD) () 
	 (LIST (PROG2 () 'RESETLANGUAGE)))
       (DEFUN RESETLANGUAGE () 
	 (SETQ NUDL '(NUD))
	 (SETQ LEDL '(LED))
	 (SETQ LBPL '(LBP))
	 (SETQ CNUD 'NUD)
	 (SETQ CLED 'LED)
	 (SETQ CLBP 'LBP)
	 ()))

(DEFUN LEARN (X) 
  ((LAMBDA (LANG) 
     (COND (LANG (SETQ LANG (CDR LANG)))
	   (T (SETQ LANG (LIST (CAT X 'NUD)
			       (CAT X 'LED)
			       (CAT X 'LBP)))
	      (SETQ LANGUAGE_ALIST (CONS (CONS X LANG) LANGUAGE_ALIST))))
     (SETQ CNUD (CAR LANG))
     (SETQ CLED (CADR LANG))
     (SETQ CLBP (CADDR LANG))
     `(OR (ASSOC ',X LANGUAGE_ALIST)
	  (PUSH '(,X |`,/|| . LANG) LANGUAGE_ALIST)))
   (ASSOC X LANGUAGE_ALIST)))

(DEFUN (RIGHT NUD) () (LIST 'PARSE DRBP))

(DEFUN (RIGHTLIST NUD) () (LIST 'PARSELIST DRBP ''/,))

(DEFUN (RIGHTREP NUD) () 
  (LIST 'PARSELIST DRBP (LIST 'QUOTE FUN)))

(DEFUN DEFFIX (DENTYPE ISFUN FUN DLBP DRBP) 
  ((LAMBDA (FORM) 
     (COND (DLBP (SETQ FORM (LIST 'PROGN
				  ''COMPILE
				  FORM
				  (LIST 'DEFPROP FUN DLBP CLBP)))))
     (COND (SYNTAX-NEEDED (EVAL FORM)))
     FORM)
   (CONS 'DEFUN
	 (CONS (LIST FUN DENTYPE)
	       (CONS (COND ((EQUAL DENTYPE CLED) '(LEFT)))
		     (PROGN (ADVANCE) (DEPROGNIFY (PARSE 0.))))))))

(DEFUN (NILFIX NUD) () (DEFFIX CNUD 'ISN TOKEN () ()))

(DEFUN (PREFIX NUD) () (DEFFIX CNUD 'ISP TOKEN () (ADVANCE)))

(DEFUN (SUFFIX NUD) () (DEFFIX CLED 'ISS TOKEN (ADVANCE) ()))

(DEFUN (INFIX NUD) () (DEFFIX CLED 'ISI TOKEN (ADVANCE) TOKEN))

(DEFUN (INFIXR NUD) () 
  (DEFFIX CLED 'ISI TOKEN (ADVANCE) (DIFFERENCE TOKEN 1.)))

(DEFUN (INFIXD NUD) () (DEFFIX CLED 'ISI TOKEN (ADVANCE) (ADVANCE)))

(DEFUN (INFIXM NUD) () (DEFFIX CLED 'ISM TOKEN (ADVANCE) TOKEN))

(DEFUN (DELIM NUD) () 
  ((LAMBDA (FORM) (COND (SYNTAX-NEEDED (EVAL FORM))) FORM)
   (CONS 'PROGN
	 (MAPCAR #'(LAMBDA (I) (LIST 'DEFPROP I 0. CLBP))
		 (GETVARLIST)))))

(DEFUN (IS NUD) () 
  (CONS ISFUN
	(APPEND (COND ((EQUAL DENTYPE CLED) '(LEFT)))
		(LIST (PARSE 25.))
		(COND (DRBP (LIST DRBP)))
		(COND ((EQUAL ISFUN 'ISM)
		       (LIST (LIST 'QUOTE FUN)))))))

(DEFUN ISN (FCN) (LIST FCN))

(DEFUN ISS (LEFT FCN) (LIST FCN LEFT))

(DEFUN ISP (FCN RB) (LIST FCN (PARSE RB)))

(DEFUN ISI (LEFT FCN RB) (LIST FCN LEFT (PARSE RB)))

(DEFUN ISM (LEFT FCN RB CONT) (CONS FCN (CONS LEFT (PARSELIST RB CONT))))

(DEFUN PKGCHECK (X) (IF (SYMBOLP X) (OR (INTERN-SOFT X CGOL-PACKAGE) X)))

(PROGN 'COMPILE
       (DEFUN (CHECK NUD) () 
	 (LIST (PROG2 () 'CHECK) (PROG2 () (PARSE 25.))))
       (DEFUN CHECK (DEL) 
	 (COND ((OR (EQUAL (PKGCHECK TOKEN) DEL)
		    (AND (NOT (ATOM DEL)) (MEMBER (PKGCHECK TOKEN) DEL)))
		(ADVANCE))
	       (T (CGOLERR (CAT '|MISSING |
				DEL
				'| INSERTED BEFORE |
				TOKEN)
			   0.
			   ())))))

(DEFUN CAT N 
  (IMPLODE (APPLY #'APPEND
		  (MAPCAR #'EXPLODEC
			  (MAPCAR #'ARG (TO 1. N 1.))))))

(DEFUN PARSELIST (RB CONT) 
  (CONS (PARSE RB)
	(COND ((EQ (PKGCHECK TOKEN) CONT) (ADVANCE) (PARSELIST RB CONT)))))

(PROGN 'COMPILE
       (DEFUN (GETVARLIST NUD) () (LIST (PROG2 () 'GETVARLIST)))
       (DEFUN GETVARLIST () 
	 (COND ((OR (NOT (EQUAL (PKGCHECK TOKEN) '/;)) STRINGNUD)
		(CONS (PROG2 () TOKEN (ADVANCE))
		      (COND ((EQUAL (PKGCHECK TOKEN) '/,)
			     (ADVANCE)
			     (GETVARLIST))))))))

(PROGN 'COMPILE
       (DEFUN (GETTOKENS NUD) () (LIST (PROG2 () 'GETTOKENS)))
       (DEFUN GETTOKENS () 
	 (COND ((NOT (MEMBER (PKGCHECK TOKEN) '(|)| ] /'  /;)))
		(CONS (PROG2 () TOKEN (ADVANCE)) (GETTOKENS))))))

(DEFUN DEPROGNIFY (X) 
  (COND ((AND (NOT (ATOM X)) (EQUAL (CAR X) 'PROGN)) (CDR X))
	(T (LIST X))))

(PROGN 'COMPILE
       (DEFUN (NOTIFY NUD) () 
	 (LIST (PROG2 () 'NOTIFY) (PROG2 () (PARSE 25.))))
       (DEFUN NOTIFY (X) 
	 (AND (NOT (EQUAL X T))
	      (COND ((AND (NOT (ATOM X)) (EQUAL (CAR X) 'NOT))
		     (CADR X))
		    (T (LIST 'NOT X))))))

(PROGN 'COMPILE
       (DEFUN (ORIFY NUD) () 
	 (LIST (PROG2 () 'ORIFY) (PROG2 () (PARSE 25.))))
       (DEFUN ORIFY (X) 
	 (AND X
	      (COND ((AND (NOT (ATOM X)) (NULL (CDR X))) (CAR X))
		    (T (CONS 'OR X))))))

(DEFUN LITERAL FEXPR (X) (MAPC #'(LAMBDA (I) (SET I I)) X))

(PROGN 'COMPILE
       (DEFUN (ARITH NUD) () 
	 (LIST (PROG2 () 'ARITH) (PROG2 () (PARSE 25.))))
       (DEFUN ARITH (X) 
	 (COND ((SETQ IT (ASSOC X ARITHMETIC_ALIST)) (CDR IT)) (T X))))

(DEFUN (DEFINE NUD) () 
  (PROG (FUN TYPE ARGTS CODE INSTR LB RB EXPR FORM) 
	(SETQ EXPR (COND ((MEMBER (PKGCHECK TOKEN)
				  '(EXPR FEXPR LEXPR MACRO))
			  (PROG2 () TOKEN (ADVANCE)))
			 (T 'EXPR)))
	(COND ((OR STRINGNUD (EQUAL (CGOLTYIPEEK) 40.))
	       (SETQ ARGTS ())
	       (SETQ TYPE CNUD)
	       (SETQ CODE (LIST 'LIST))
	       (SETQ INSTR
		     (LIST 'PROG2 () (LIST 'QUOTE TOKEN))))
	      (T (SETQ ARGTS (LIST TOKEN))
		 (ADVANCE)
		 (SETQ TYPE CLED)
		 (SETQ CODE (LIST 'LIST (LIST 'QUOTE TOKEN)))
		 (SETQ INSTR (LIST 'PROG2 () 'LEFT))))
	(SETQ FUN TOKEN)
	(ADVANCE)
	(COND ((AND (EQUAL (PKGCHECK TOKEN) '|(|) (NOT STRINGNUD))
	       (ADVANCE)
	       (SETQ ARGTS (COND ((NOT (EQUAL (PKGCHECK TOKEN) '|)|))
				  (GETVARLIST))))
	       (COND ((EQUAL EXPR 'LEXPR)
		      (SETQ ARGTS (CAR ARGTS))
		      (SETQ EXPR 'EXPR)))
	       (CHECK '|)|)
	       (SETQ CODE ())
	       (SETQ INSTR ()))
	      (T (DO () 
		     ((NOT (OR (NOT (OR (EQUAL (PKGCHECK TOKEN) '/;)
					(EQUAL (PKGCHECK TOKEN) '/,)))
			       STRINGNUD))) 
		  (DO () ((NOT STRINGNUD))
		   (SETQ INSTR (APPEND INSTR
				       (LIST (LIST 'CHECK
						   (LIST 'QUOTE
							 TOKEN)))))
		   (SETQ FORM (CONS (LIST 'DEFPROP TOKEN 0. CLBP) FORM))
		   (ADVANCE)) 
		  (SETQ CODE (APPEND CODE (LIST INSTR)))
		  (COND ((AND (OR (EQUAL (PKGCHECK TOKEN) '/;)
				  (EQUAL (PKGCHECK TOKEN) '/,))
			      (NOT STRINGNUD))
			 (SETQ INSTR ()))
			(T (SETQ INSTR (LIST 'PROG2
					     ()
					     (LIST 'PARSE
						   '/#RBP)))
			   (SETQ ARGTS (APPEND ARGTS (LIST TOKEN)))
			   (ADVANCE))))))
	(SETQ LB (COND ((EQUAL TYPE CLED)
			(COND ((EQUAL (PKGCHECK TOKEN) '/,)
			       (ADVANCE)
			       (EVAL (PARSE 1.)))
			      (T DEFBP)))))
	(SETQ RB (COND ((EQUAL (PKGCHECK TOKEN) '/,)
			(ADVANCE)
			(EVAL (PARSE 1.)))
		       (T (OR LB DEFBP))))
	(SETQ CODE (SUBST RB
			  '/#RBP
			  (APPEND CODE (COND (INSTR (LIST INSTR))))))
	(CHECK '/;)
	(COND
	 (CODE
	  (SETQ FORM
		(CONS 'PROGN
		      (CONS ''COMPILE
			    (CONS (LIST (PROGN 'DEFUN)
					(LIST FUN TYPE)
					(COND ((EQUAL TYPE CLED)
					       '(LEFT)))
					CODE)
				  (APPEND (COND (LB (LIST (LIST 'DEFPROP
								FUN
								LB
								CLBP))))
					  (NREVERSE FORM))))))
	  (COND (SYNTAX-NEEDED (EVAL FORM)))))
	(COND
	 ((NOT (EQUAL (PKGCHECK TOKEN) '))
	  (SETQ 
	   FORM
	   (APPEND FORM
		   (LIST (CONS (PROGN 'DEFUN)
			       (CONS FUN
				     (APPEND (COND ((NOT (EQUAL EXPR
								'EXPR))
						    (LIST EXPR)))
					     (LIST ARGTS)
					     (DEPROGNIFY (PARSE 0.))))))))))
	(RETURN (COND (CODE FORM) (T (CAR FORM))))))

(SETQ DEFBP 25.)

(INITIALIZE-MULTI-CHARACTER-TOKEN-TABLE
 '|-+#&'()*,//:;<=>@[\]^`{/|}~!|)

(DEFUN DEFTOK FEXPR (A) (MAPC #'PUTTOK A))

(DEFUN (NEWTOK NUD) () 
  ((LAMBDA (FORM) (COND (SYNTAX-NEEDED (EVAL FORM))) FORM)
   (CONS 'DEFTOK (GETVARLIST))))

(DEFUN (|(| NUD) () (PROG2 () (PARSE 0.) (CHECK '|)|)))

(PROGN (DEFPROP |)| 0. LBP))

(PROGN 'COMPILE
       (DEFUN (|(| LED) (LEFT) 
	 (PROG2 ()
		(CONS LEFT
		      (COND ((NOT (EQUAL (PKGCHECK TOKEN) '|)|))
			     (PARSELIST 0. '/,))))
		(CHECK '|)|)))
       (DEFPROP |(| 30. LBP))

(PROGN (DEFPROP /, 0. LBP))

(PROGN 'COMPILE
       (DEFUN ({ LED) (LEFT) 
	 (PROG2 ()
		(CONS 'APPLY
		      (CONS (LIST 'FUNCTION LEFT)
			    (PARSELIST 0. '/,)))
		(CHECK '})))
       (DEFPROP { 30. LBP))

(PROGN (DEFPROP } 0. LBP))

(DEFUN ([ NUD) ()
  (PROG2 ()
	 (COND ((NOT (EQUAL (PKGCHECK TOKEN) ']))
		((LAMBDA (A) 
		   (COND ((EQUAL (PKGCHECK TOKEN) '|)|)
			  (LIST 'CIRC A))
			 (T A)))
		 (CONS 'LIST (PARSELIST 0. '/,)))))
	 (CHECK '(] |)|))))

(DEFUN CIRC (X) (PROG2 () X (RPLACD (LAST X) X)))

(PROGN (DEFPROP ] 0. LBP))

(PROGN 'COMPILE
       (DEFUN ([ LED) (LEFT) 
	 (PROG2 ()
		(COND ((EQUAL (PKGCHECK TOKEN) '{)
		       (PROG2 ()
			      (PROGN (ADVANCE)
				     (SUBLIS (LIST (CONS 'A LEFT)
						   (CONS 'B
							 (PARSE 0.)))
					     '(APPLY #'MAPCAR
						     (CONS #'A B))))
			      (CHECK '})))
		      (T (CONS 'MAPCAR
			       (CONS (LIST 'FUNCTION LEFT)
				     (PARSELIST 0. '/,)))))
		(CHECK '])))
       (DEFPROP [ 30. LBP))

(DEFUN (OCT NUD) () 
  (PROG2 ()
	 ((LAMBDA (CIBASE) (CHECK '|(|) (PARSE 0.)) 8.)
	 (CHECK '|)|)))

(DEFUN (/' NUD) () (PROG2 () (ISP 'QUOTE 0.) (CHECK '/')))

(PROGN (DEFPROP /' 0. LBP))

(DEFUN (/# NUD) () (PROG2 () TOKEN (ADVANCE)))

(DEFUN (= NUD) () (EVAL (PARSE 25.)))

(DEFUN (\ NUD) () 
  (PROG2 ()
	 (CONS 'LAMBDA
	       (CONS (PROG2 () (GETVARLIST) (CHECK '/;))
		     (DEPROGNIFY (PARSE 0.))))
	 (COND ((EQUAL (PKGCHECK TOKEN) '\) (ADVANCE)))))

(PROGN (DEFPROP \ 0. LBP))

(DEFUN (LET NUD) () 
  (PROG (VARS ARGTS PACKFLAG) 
	(DO () 
	    ((MEMBER (PKGCHECK TOKEN) '(/; IN))) 
	 (SETQ VARS (APPEND VARS (GETVARLIST))) 
	 (CHECK '(BE /:= =))
	 (SETQ ARGTS (CONS (COND ((EQUAL (PKGCHECK TOKEN) '{)
				  (LIST '&UNP
					(PROG2 ()
					       (PROGN (ADVANCE) (PARSE 0.))
					       (PROGN (SETQ PACKFLAG T)
						      (CHECK '})))))
				 (T (PARSE 1.)))
			   ARGTS))
	 (COND ((EQUAL (PKGCHECK TOKEN) '/,) (ADVANCE))))
	(ADVANCE)
	(RETURN
	 (COND
	  (PACKFLAG
	   (SETQ ARGTS
		 (REVERSE (MAPCAR 
			   #'(LAMBDA (I) 
			       (COND ((EQUAL (CAR I) '&UNP) (CADR I))
				     (T (LIST 'LIST I))))
			   ARGTS)))
	   (LIST 'APPLY
		 (LIST 'FUNCTION
		       (CONS 'LAMBDA
			     (CONS VARS (DEPROGNIFY (PARSE 0.)))))
		 (COND ((EQUAL (LENGTH ARGTS) 1.) (CAR ARGTS))
		       (T (CONS 'APPEND ARGTS)))))
	  (T (CONS (CONS 'LAMBDA (CONS VARS (DEPROGNIFY (PARSE 0.))))
		   (NREVERSE ARGTS)))))))

(DEFUN (PROG NUD) () 
  (CONS 'PROG
	(CONS (PROG2 () (GETVARLIST) (CHECK '/;))
	      (DEPROGNIFY (PARSE 0.)))))

(DEFUN (NEW NUD) () 
  (CONS 'PROG
	(CONS (PROG2 () (GETVARLIST) (CHECK '/;))
	      ((LAMBDA (X) 
		 ((LAMBDA (Y) (RPLACA Y (LIST 'RETURN (CAR Y))) X)
		  (LAST X)))
	       (DEPROGNIFY (PARSE 0.))))))

(DEFUN (SPECIAL NUD) () 
  (LIST 'DECLARE (CONS 'SPECIAL (GETVARLIST))))

(DEFUN (LITERAL NUD) () (CONS 'LITERAL (PARSELIST 1. '/,)))

(DEFUN CGOLARRAY FEXPR (X) 
  (COND ((EQUAL (PKGCHECK TOKEN) '|(|)
	 (PROG2 ()
		(PROGN (ADVANCE)
		       (CONS (CAR X)
			     (MAPCAR 
			      #'(LAMBDA (Y) (LIST 'SUB1 Y))
			      (PARSELIST 0. '/,))))
		(CHECK '|)|)))
	((EQUAL (PKGCHECK TOKEN) '/:=)
	 (ADVANCE)
	 (LIST 'FILLARRAY (CAR X) (PARSE 1.)))
	(T (CAR X))))

(DEFUN (ARRAY NUD) () 
  (COND
   ((MEMBER (PKGCHECK TOKEN) '(|(| { [)) 'ARRAY)
   (T
    ((LAMBDA (NAMES) 
       ((LAMBDA (OLDNUDS) 
	  (PROG2
	   ()
	   (PROGN
	    (MAPC 
	     #'(LAMBDA (NAME) 
		 (PUTPROP NAME
			  (LIST 'LAMBDA
				()
				(LIST 'CGOLARRAY NAME))
			  CNUD))
	     NAMES)
	    (COND
	     ((EQUAL (PKGCHECK TOKEN) '|(|)
	      (ADVANCE)
	      ((LAMBDA (DIMS) 
		 (CHECK '|)|)
		 ((LAMBDA (TYPE) 
		    ((LAMBDA (SOURCE) 
		       (COND
			((EQUAL (PKGCHECK TOKEN) '/;)
			 (ADVANCE)
			 (CONS
			  (CONS
			   'LAMBDA
			   (CONS
			    NAMES
			    (APPEND
			     (COND
			      (SOURCE
			       (MAPCAR #'(LAMBDA (NAME) 
					   (LIST 'FILLARRAY
						 NAME
						 SOURCE))
				       NAMES)))
			     (DEPROGNIFY (PARSE 0.)))))
			  (MAPCAR 
			   #'(LAMBDA (NAME) 
			       (CONS 'ARRAY
				     (CONS () (CONS TYPE DIMS))))
			   NAMES)))
			(T
			 (CONS
			  'PROG2
			  (CONS
			   ()
			   (CONS
			    (LIST 'QUOTE (CAR NAMES))
			    (MAPCAN 
			     #'(LAMBDA (NAME) 
				 (CONS
				  (LIST 'DEFPROP
					NAME
					(GET NAME 'NUD)
					'NUD)
				  (CONS
				   (LIST 'SETQ
					 NAME
					 (CONS 'ARRAY
					       (CONS () (CONS TYPE DIMS))))
				   (COND (SOURCE (LIST (LIST 'FILLARRAY
							     NAME
							     SOURCE)))))))
			     NAMES)))))))
		     (COND ((MEMBER (PKGCHECK TOKEN) '(/:= =))
			    (ADVANCE)
			    (PARSE 1.)))))
		  (COND ((MEMBER (PKGCHECK TOKEN)
				 '(FIXNUM FLONUM () T))
			 (PROG2 () TOKEN (ADVANCE)))
			(T T))))
	       (PARSELIST 0. '/,)))
	     ((EQUAL (PKGCHECK TOKEN) '/;) (ADVANCE) (PARSE 0.))))
	   (MAPC #'(LAMBDA (NAME OLDNUD) 
		     (COND (OLDNUD (PUTPROP NAME OLDNUD CNUD))
			   (T (REMPROP NAME CNUD))))
		 NAMES
		 OLDNUDS)))
	(MAPCAR #'(LAMBDA (NAME) (GET NAME CNUD)) NAMES)))
     (GETVARLIST)))))

(DEFUN (DIM NUD) () (LIST 'CDR (LIST 'ARRAYDIMS (PARSE 25.))))

(PUTPROP 'EVAL 1. 'RBP)

(PROGN 'COMPILE
       (DEFUN (/; LED) (LEFT) (ISM LEFT 'PROGN 1. '/;))
       (DEFPROP /; 1. LBP))

(PROGN 'COMPILE
       (DEFUN (& LED) (LEFT) (LIST 'PROG2 () LEFT (PARSE 0.)))
       (DEFPROP & 1. LBP))

(DEFUN (IF NUD) () 
  (CONS 'COND
	(CONS (CONS (PARSE 2.)
		    (PROGN (CHECK 'THEN) (DEPROGNIFY (PARSE 2.))))
	      (COND ((EQ (PKGCHECK TOKEN) 'ELSE)
		     (ADVANCE)
		     ((LAMBDA (X) 
			(COND ((AND (NOT (ATOM X))
				    (EQUAL (CAR X) 'COND))
			       (CDR X))
			      (T (LIST (CONS T (DEPROGNIFY X))))))
		      (PARSE 2.)))))))

(PROGN (DEFPROP THEN 0. LBP))

(PROGN (DEFPROP ELSE 0. LBP))

(PUTPROP 'RETURN 1. 'RBP)

(PUTPROP 'GO 1. 'RBP)

(DEFUN (WHILE NUD) () 
  (CONS 'DO
	(CONS ()
	      (CONS (LIST (NOTIFY (PARSE 2.)))
		    (PROGN (CHECK 'DO) (DEPROGNIFY (PARSE 2.)))))))

(DEFUN (REPEAT NUD) () 
  (LIST 'DO
	()
	(LIST (CONS 'PROG2
		    (APPEND (DEPROGNIFY (PARSE 2.))
			    (DEPROGNIFY (PROGN (CHECK 'UNTIL)
					       (PARSE 2.))))))))

(PROGN (DEFPROP DO 0. LBP))

(DEFUN (FOR NUD) () 
  (PROG (PARS ARGTS INON FCN BODY) 
	(SETQ PARS (LIST TOKEN))
	(SETQ INON (ADVANCE))
	(ADVANCE)
	(SETQ FCN
	      (ASSOC INON
		     '((IN (DO MAPC) (COLLECT MAPCAR) (COALESCE MAPCAN))
		       (ON (DO MAP) (COLLECT MAPLIST) (COALESCE MAPCON)))))
	(COND (FCN (SETQ FCN (CDR FCN)))
	      (T (CGOLERR (CAT INON '| FOUND WHERE IN OR ON EXPECTED|)
			  2.
			  T)))
	(SETQ ARGTS (LIST (PARSE 1.)))
	(DO () 
	    ((NOT (EQ (PKGCHECK TOKEN) '/,))) 
	 (SETQ PARS (CONS (ADVANCE) PARS)) 
	 (ADVANCE)
	 (CHECK INON)
	 (SETQ ARGTS (CONS (PARSE 1.) ARGTS)))
	(SETQ FCN (ASSOC (PKGCHECK TOKEN) FCN))
	(COND
	 (FCN (SETQ FCN (CADR FCN)))
	 (T
	  (CGOLERR (CAT TOKEN
			'| FOUND WHERE DO, COLLECT OR COALESCE EXPECTED|)
		   2.
		   T)))
	(ADVANCE)
	(SETQ ARGTS (NREVERSE ARGTS))
	(SETQ PARS (NREVERSE PARS))
	(SETQ BODY (PARSE 1.))
	(RETURN
	 (COND
	  ((AND (EQUAL FCN 'MAPC)
		(APPLY #'AND
		       (MAPCAR 
			#'(LAMBDA (X) 
			    (AND (NOT (ATOM X)) (EQUAL (CAR X) 'TO)))
			ARGTS)))
	   (CONS
	    'DO
	    (CONS
	     (MAPCAR #'(LAMBDA (P A) 
			 (LIST P
			       (CADR A)
			       (COND ((EQUAL (CADDDR A) 1.)
				      (LIST 'ADD1 P))
				     (T (LIST 'PLUS P (CADDDR A))))))
		     PARS
		     ARGTS)
	     (CONS (LIST (ORIFY (MAPCAR #'(LAMBDA (P A) 
					    (LIST 'GREATERP
						  P
						  (CADDR A)))
					PARS
					ARGTS)))
		   (DEPROGNIFY BODY)))))
	  (T (CONS FCN
		   (CONS (LIST 'FUNCTION
			       (COND ((AND (EQUAL (CDR BODY) PARS)
					   (ATOM (CAR BODY)))
				      (CAR BODY))
				     (T (LIST 'LAMBDA PARS BODY))))
			 ARGTS)))))))

(PROGN (PROGN (DEFPROP IN 0. LBP))
       (PROGN (DEFPROP ON 0. LBP))
       (PROGN (DEFPROP COLLECT 0. LBP))
       (PROGN (DEFPROP COALESCE 0. LBP)))

(DEFUN (ITER NUD) () 
  (PROG (IVARS WHENVAR RESULT BODY) 
	(DO () 
	    ((NOT
	      (SETQ 
	       IT
	       (ASSOC (PKGCHECK TOKEN)
		      '((FOR (SETQ IVARS (CONS (CONS TOKEN (COND ((EQUAL (ADVANCE) '
										    /:=) (CONS (PROGN (ADVANCE) (SETQ IT (PARSE 2.))) (COND ((EQUAL (PKGCHECK TOKEN) '
																				     STEP) (LIST (COND ((EQUAL (ADVANCE) '
																									  DITTO) (ADVANCE) IT) (T (PARSE 2.)))))))))) IVARS)))
			(WHEN (SETQ WHENVAR (PARSE 2.)))
			(UNTIL (SETQ WHENVAR (PARSE 2.)))
			(WHILE (SETQ WHENVAR (LIST 'NOT
						   (PARSE 2.))))
			(RETURN (SETQ RESULT (PARSE 2.)))
			(DO (SETQ BODY (PARSE 2.)))))))) 
	 (ADVANCE) 
	 (EVAL (CADR IT)))
	(COND ((NOT (OR IVARS WHENVAR RESULT BODY)) (SETQ BODY (PARSE 2.))))
	(RETURN (APPEND (LIST 'DO
			      (NREVERSE IVARS)
			      (LIST WHENVAR RESULT))
			(COND ((AND (NOT (ATOM BODY))
				    (EQ (CAR BODY) 'PROGN))
			       (CDR BODY))
			      (T (NCONS BODY)))))))

(PROGN (DEFPROP FOR 0. LBP)
       (DEFPROP WHEN 0. LBP)
       (DEFPROP UNTIL 0. LBP)
       (DEFPROP WHILE 0. LBP)
       (DEFPROP STEP 0. LBP)
       (DEFPROP RETURN 0. LBP))

(PROGN 'COMPILE
       (DEFUN (TO LED) (LEFT) 
	 (CONS 'TO
	       (CONS LEFT
		     (CONS (PARSE 18.)
			   (LIST (COND ((EQUAL (PKGCHECK TOKEN) 'BY)
					(ADVANCE)
					(PARSE 18.))
				       (T 1.)))))))
       (DEFPROP TO 18. LBP))

(PROGN (DEFPROP BY 0. LBP))

(DEFUN TO (AA B C) 
  (COND ((GREATERP AA B) ())
	(T (PROG (X) 
		 (RETURN (PROG2 ()
				(SETQ X (LIST AA))
				(DO () 
				    ((LESSP B (SETQ AA (PLUS AA C)))) 
				 (SETQ X (CDR (RPLACD X (LIST AA)))))))))))

(PROGN 'COMPILE
       (DEFUN (LOTSOF LED) (LEFT) 
	 (LIST 'DO
	       '*I
	       LEFT
	       '(DIFFERENCE *I 1.)
	       '(NOT (GREATERP *I 0.))
	       (PARSE 1.)))
       (DEFPROP LOTSOF 19. LBP))

(DEFTOK /:=)

(PUTPROP 'CGOLPRINT
	 '(LAMBDA () (LIST 'CGOLPRINT (PARSE 1.)))
	 'NUD)

(PUTPROP 'CGOLPRIN1
	 '(LAMBDA () (LIST 'CGOLPRIN1 (PARSE 1.)))
	 'NUD)

(PROGN 'COMPILE
       (DEFUN (/:= LED) (LEFT) 
	 (COND ((ATOM LEFT) (ISI LEFT 'SETQ 1.))
	       ((EQ (CAR LEFT) 'GET)
		(LIST 'PUTPROP (CADR LEFT) (PARSE 1.) (CADDR LEFT)))
	       ((SETQ IT (GET (CAR LEFT) 'STOREFORM))
		((LAMBDA (X) 
		   (SUBLIS (LIST (CONS 'LEFT (CADR LEFT))
				 (CONS 'RIGHT (PARSE 1.)))
			   X))
		 IT))
	       (T (ISI LEFT 'STORE 1.))))
       (DEFPROP /:= 25. LBP))

(PROGN (PUTPROP 'CAR '(RPLACA LEFT RIGHT) 'STOREFORM)
       (PUTPROP 'CDR '(RPLACD LEFT RIGHT) 'STOREFORM)
       (PUTPROP 'ARG '(SETARG LEFT RIGHT) 'STOREFORM)
       (PUTPROP 'PLIST '(SETPLIST LEFT RIGHT) 'STOREFORM)
       (PUTPROP 'STATUS
		'(SSTATUS LEFT RIGHT)
		'STOREFORM))

(MAPC #'(LAMBDA (I) 
	  (PUTPROP I
		   (SUBST I 'I '(LAMBDA () '(STATUS I)))
		   'NUD))
      '(TOPLEVEL BREAKLEVEL WHO2 WHO3 TTYSCAN TTYREAD TTYINT GCTIME))

(PROGN 'COMPILE
       (DEFUN (OF LED) (LEFT) (LIST 'GET (PARSE 25.) LEFT))
       (DEFPROP OF 26. LBP))

(PROGN 'COMPILE
       (DEFUN (OFQ LED) (LEFT) 
	 (LIST 'GET (PARSE 25.) (LIST 'QUOTE LEFT)))
       (DEFPROP OFQ 26. LBP))

(PUTPROP 'NOT 9. 'RBP)

(PROGN 'COMPILE
       (DEFUN (NOT LED) (LEFT) (LIST 'NOT (FUNCALL (LED) LEFT)))
       (DEFPROP NOT 10. LBP))

(PROGN 'COMPILE
       (DEFUN (AND LED) (LEFT) (ISM LEFT 'AND 8. 'AND))
       (DEFPROP AND 8. LBP))

(PROGN 'COMPILE
       (DEFUN (OR LED) (LEFT) (ISM LEFT 'OR 7. 'OR))
       (DEFPROP OR 7. LBP))

(PROGN (DEFTOK =/#)
       (DEFTOK =$)
       (DEFTOK </#)
       (DEFTOK >/#)
       (DEFTOK <$)
       (DEFTOK >$)
       (DEFTOK <=)
       (DEFTOK >=))

(PROGN 'COMPILE
       (DEFUN (= LED) (LEFT) (ISI LEFT (ARITH 'EQUAL) 10.))
       (DEFPROP = 10. LBP))

(PROGN 'COMPILE
       (DEFUN (NE LED) (LEFT) 
	 (LIST 'NOT (ISI LEFT (ARITH 'EQUAL) 10.)))
       (DEFPROP NE 10. LBP))

(PROGN 'COMPILE
       (DEFUN (EQ LED) (LEFT) (ISI LEFT 'EQ 10.))
       (DEFPROP EQ 10. LBP))

(PROGN 'COMPILE
       (DEFUN (< LED) (LEFT) (ISM LEFT (ARITH 'LESSP) 10. '<))
       (DEFPROP < 10. LBP))

(PROGN 'COMPILE
       (DEFUN (> LED) (LEFT) 
	 (ISM LEFT (ARITH 'GREATERP) 10. '>))
       (DEFPROP > 10. LBP))

(PROGN 'COMPILE
       (DEFUN (=/# LED) (LEFT) (ISI LEFT '= 10.))
       (DEFPROP =/# 10. LBP))

(PROGN 'COMPILE
       (DEFUN (=$ LED) (LEFT) (ISI LEFT '= 10.))
       (DEFPROP =$ 10. LBP))

(PROGN 'COMPILE
       (DEFUN (</# LED) (LEFT) (ISI LEFT '< 10.))
       (DEFPROP </# 10. LBP))

(PROGN 'COMPILE
       (DEFUN (>/# LED) (LEFT) (ISI LEFT '> 10.))
       (DEFPROP >/# 10. LBP))

(PROGN 'COMPILE
       (DEFUN (<$ LED) (LEFT) (ISI LEFT '< 10.))
       (DEFPROP <$ 10. LBP))

(PROGN 'COMPILE
       (DEFUN (>$ LED) (LEFT) (ISI LEFT '> 10.))
       (DEFPROP >$ 10. LBP))

(PROGN 'COMPILE
       (DEFUN (<= LED) (LEFT) 
	 (LIST 'NOT (ISI LEFT (ARITH 'GREATERP) 10.)))
       (DEFPROP <= 10. LBP))

(PROGN 'COMPILE
       (DEFUN (>= LED) (LEFT) 
	 (LIST 'NOT (ISI LEFT (ARITH 'LESSP) 10.)))
       (DEFPROP >= 10. LBP))

(PROGN 'COMPILE
       (DEFUN (/| LED) (LEFT) 
	 (LIST (ARITH 'ZEROP)
	       (LIST (ARITH 'REMAINDER) (PARSE 10.) LEFT)))
       (DEFPROP /| 10. LBP))

(PROGN 'COMPILE
       (DEFUN (ISIN LED) (LEFT) (ISI LEFT 'MEMBER 10.))
       (DEFPROP ISIN 10. LBP))

(PROGN 'COMPILE
       (DEFUN (ISATOM LED) (LEFT) (ISS LEFT 'ATOM))
       (DEFPROP ISATOM 10. LBP))

(PROGN 'COMPILE
       (DEFUN (ISNUM LED) (LEFT) (ISS LEFT 'NUMBERP))
       (DEFPROP ISNUM 10. LBP))

(PROGN 'COMPILE
       (DEFUN (EXISTS LED) (LEFT) (LIST 'SETQ 'IT LEFT))
       (DEFPROP EXISTS 10. LBP))

(PUTPROP 'NULL 10. 'RBP)

(PROGN 'COMPILE
       (DEFUN (|.| LED) (LEFT) (ISI LEFT 'CONS 14.))
       (DEFPROP |.| 15. LBP))

(PROGN 'COMPILE
       (DEFUN (@ LED) (LEFT) (ISM LEFT 'APPEND 15. '@))
       (DEFPROP @ 15. LBP))

(DEFUN ({ NUD) () 
  (PROG2 ()
	 (CONS 'GATHER
	       (COND ((NOT (EQUAL (PKGCHECK TOKEN) '}))
		      (PARSELIST 0. '/,))))
	 (CHECK '})))

(PROGN 'COMPILE
       (DEFUN (|| LED) (LEFT) (ISM LEFT 'UNION 16. '||))
       (DEFPROP || 16. LBP))

(PROGN 'COMPILE
       (DEFUN (/ LED) (LEFT) (ISM LEFT 'INTERSECT 16. '/))
       (DEFPROP / 16. LBP))

(DEFUN (/~ NUD) () (ISP 'SETDIFF 16.))

(PROGN 'COMPILE
       (DEFUN (/~ LED) (LEFT) (ISM LEFT 'SETDIFF 16. '/~))
       (DEFPROP /~ 16. LBP))

(PROGN 'COMPILE
       (DEFUN (/ LED) (LEFT) (ISM LEFT 'ELEMENTP 10. '/))
       (DEFPROP / 10. LBP))

(PROGN 'COMPILE
       (DEFUN (/ LED) (LEFT) (ISM LEFT 'SUBSETP 10. '/))
       (DEFPROP / 10. LBP))

(PROGN (MAPC #'(LAMBDA (U) 
		 (OR (FBOUNDP U)
		     (PUTPROP U
			      '((DSK LIBLSP) SETS FASL)
			      'AUTOLOAD)))
	     '(GATHER UNION INTERSECT SETDIFF ELEMENTS ELEMENTP SUBSETP
	       SYMDIFF CLEARSETS))
       (IF (FBOUNDP '*LEXPR)
	   (EVAL '(*LEXPR UNION INTERSECT SETDIFF SYMDIFF))))

(PROGN 'COMPILE
       (DEFUN (^ LED) (LEFT) (ISM LEFT 'CAT 18. '^))
       (DEFPROP ^ 18. LBP))

(PROGN 'COMPILE
       (DEFUN (CAT LED) (LEFT) (ISM LEFT 'CAT 18. 'CAT))
       (DEFPROP CAT 18. LBP))

(DEFUN (/| NUD) () 
  (PROG2 () (ISP (ARITH 'ABS) 19.) (CHECK '/|)))

(DEFUN (+ NUD) () 
  (COND ((MEMBER (PKGCHECK TOKEN) '(|(| { [)) (ARITH 'PLUS))
	(T (PARSE 20.))))

(PROGN 'COMPILE
       (DEFUN (+ LED) (LEFT) (ISM LEFT (ARITH 'PLUS) 20. '+))
       (DEFPROP + 20. LBP))

(PROGN 'COMPILE
       (DEFUN (- LED) (LEFT) 
	 (ISM LEFT (ARITH 'DIFFERENCE) 20. '-))
       (DEFPROP - 20. LBP))

(DEFUN (- NUD) () (ISP (ARITH 'MINUS) 20.))

(DEFUN (* NUD) () 
  (COND ((MEMBER (PKGCHECK TOKEN) '(|(| [ {)) (ARITH 'TIMES))
	(T '*)))

(PROGN 'COMPILE
       (DEFUN (* LED) (LEFT) (ISM LEFT (ARITH 'TIMES) 21. '*))
       (DEFPROP * 21. LBP))

(PROGN 'COMPILE
       (DEFUN (// LED) (LEFT) 
	 (LIST (ARITH 'QUOTIENT)
	       LEFT
	       (LIST (ARITH 'FLOAT) (PARSE 21.))))
       (DEFPROP // 21. LBP))

(DEFTOK ///:)

(PROGN 'COMPILE
       (DEFUN (///: LED) (LEFT) 
	 (ISM LEFT (ARITH 'QUOTIENT) 21. '///:))
       (DEFPROP ///: 21. LBP))



(DEFTOK **)

(PROGN 'COMPILE
       (DEFUN (** LED) (LEFT) (ISI LEFT (ARITH 'EXPT) 21.))
       (DEFPROP ** 22. LBP))

(PROGN (DEFTOK +/#) (DEFTOK -/#) (DEFTOK */#) (DEFTOK |//#|) (DEFTOK \\))

(PROGN 'COMPILE
       (DEFUN (+/# LED) (LEFT) (ISM LEFT '+ 20. '+/#))
       (DEFPROP +/# 20. LBP))

(PROGN 'COMPILE
       (DEFUN (-/# LED) (LEFT) (ISM LEFT '- 20. '-/#))
       (DEFPROP -/# 20. LBP))

(PROGN 'COMPILE
       (DEFUN (*/# LED) (LEFT) (ISM LEFT '* 21. '*/#))
       (DEFPROP */# 21. LBP))

(PROGN 'COMPILE
       (DEFUN (|//#| LED) (LEFT) (ISM LEFT '// 21. '|//#|))
       (DEFPROP |//#| 21. LBP))

(PROGN 'COMPILE
       (DEFUN (\\ LED) (LEFT) (ISI LEFT '\\ 19.))
       (DEFPROP \\ 19. LBP))

(PROGN (DEFTOK +$) (DEFTOK -$) (DEFTOK *$) (DEFTOK //$))

(PROGN 'COMPILE
       (DEFUN (+$ LED) (LEFT) (ISM LEFT '+$ 20. '+$))
       (DEFPROP +$ 20. LBP))

(PROGN 'COMPILE
       (DEFUN (-$ LED) (LEFT) (ISM LEFT '-$ 20. '-$))
       (DEFPROP -$ 20. LBP))

(PROGN 'COMPILE
       (DEFUN (*$ LED) (LEFT) (ISM LEFT '*$ 21. '*$))
       (DEFPROP *$ 21. LBP))

(PROGN 'COMPILE
       (DEFUN (//$ LED) (LEFT) (ISM LEFT '//$ 21. '//$))
       (DEFPROP //$ 21. LBP))

(PROGN (DEFTOK /:N/:) (DEFTOK /:A/:) (DEFTOK /:V/:) (DEFTOK /:X/:) (DEFTOK /:^/:))

(DEFUN (/:N/: NUD) () (LIST 'BOOLE 12. 0. (PARSE 21.)))

(PROGN 'COMPILE
       (DEFUN (/:A/: LED) (LEFT) 
	 (CONS 'BOOLE
	       (CONS 1. (CONS LEFT (PARSELIST 21. '/:A/:)))))
       (DEFPROP /:A/: 21. LBP))

(PROGN 'COMPILE
       (DEFUN (/:V/: LED) (LEFT) 
	 (CONS 'BOOLE
	       (CONS 7. (CONS LEFT (PARSELIST 20. '/:V/:)))))
       (DEFPROP /:V/: 20. LBP))

(PROGN 'COMPILE
       (DEFUN (/:X/: LED) (LEFT) 
	 (CONS 'BOOLE
	       (CONS 6. (CONS LEFT (PARSELIST 20. '/:X/:)))))
       (DEFPROP /:X/: 20. LBP))

(PROGN 'COMPILE
       (DEFUN (/:^/: LED) (LEFT) (ISI LEFT 'LSH 22.))
       (DEFPROP /:^/: 22. LBP))

(PUTPROP 'PRINT 2. 'RBP)

(PUTPROP 'PRINC 2. 'RBP)

(PUTPROP 'PRIN1 2. 'RBP)

(DEFUN (WRITE NUD) () 
  (SUBST (CONS 'LIST (PARSELIST 2. '/,))
	 'X
	 '(PROGN (TERPRI) (MAPC #'PRINC X) (PRINC '| |))))

(DEFUN (NEWLINE NUD) () (ISN 'TERPRI))

(DEFUN (UREAD NUD) () (CONS 'UREAD (GETTOKENS)))

(DEFUN (UWRITE NUD) () (CONS 'UWRITE (GETTOKENS)))

(DEFUN (UFILE NUD) () (CONS 'UFILE (GETTOKENS)))

(PROGN (SETQ SYNTAX-NEEDED T)
       (SETQ SILENCE (MINUS 1.))
       (SETQ DEFBP 25.)
       (SETQ NUDL '(NUD))
       (SETQ LEDL '(LED))
       (SETQ LBPL '(LBP))
       (SETQ CNUD 'NUD)
       (SETQ CLED 'LED)
       (SETQ CLBP 'LBP)
       (SETQ FUN 'TOP-LEVEL)
       (SETQ LANGUAGE_ALIST ())
       (SETQ ARITHMETIC_ALIST ())
       (SSTATUS FEATURE CGOL))

