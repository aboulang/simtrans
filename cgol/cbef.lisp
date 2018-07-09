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
