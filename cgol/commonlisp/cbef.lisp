;;;-*-Base:10.; Mode:lisp; Package: (CGOL use (cl)); Syntax: Common-lisp-*-
;;(scl::defpackage cgol (:use cl))
(shadow '(expolden implode))

(defmacro implode (l)
  `(intern (coerce ,l 'string)))

(defmacro cgol::exploden (atom)
  `(coerce (symbol-name ,atom) 'list))


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


(EVAL-WHEN (EVAL COMPILE LOAD)
  (SPECIAL IT))

;; First step: The tokenizer.


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

(DEFUN NORMALIZE-READ-ARGS (READ-ARGS)
  (MULTIPLE-VALUE-BIND (STREAM EOF)
		       (SI:DECODE-READ-ARGS READ-ARGS)
    (CONS STREAM EOF)))


(DEFUN CGOLREAD (&REST READ-ARGS &AUX STREAM EOFM)
  (SETQ READ-ARGS (NORMALIZE-READ-ARGS READ-ARGS))
  (SETQ STREAM (CAR READ-ARGS)
	EOFM (CDR READ-ARGS))
  (LET ((WHICH-OPERATIONS
	 (FUNCALL STREAM ':WHICH-OPERATIONS)
	 ))
    (CATCH 'CGOLERR
      (COND ((AND (NOT sys:rubout-handler) (member ':RUBOUT-HANDLER WHICH-OPERATIONS))
	     (FUNCALL STREAM ':RUBOUT-HANDLER '() #'TOPLEVEL-PARSE STREAM))
	    ('ELSE
	     (TOPLEVEL-PARSE STREAM))))))

(DEFUN TOPLEVEL-PARSE (CGOL-INPUT)
  (TOPLEVEL-PARSE-1 ()))


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
	 (THROW 'CGOLERR EOFM))
	('ELSE
	 (PROGN LEVEL
		(ZL:CERROR (NOT FATALP) ;; procedable sometimes.
			() ;; Not restartable.
			() ;; no condition given, since READ uses (FERROR () ...)
			"~A IN ~A"
			MESSAGE FUN)))))


(defmacro mtyi ()
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


(DEFVAR CREAD-READTABLE *READTABLE*)

(defun cread ()
  (LET ((*READTABLE* CREAD-READTABLE))
    (read cgol-input nil eofm)))

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
    (cond ((eq c -1)
	   (if (null l)
	       (cgolerr "EOF encountered inside cgol-exp - CGOLREAD" 2 t)
	       (return-token c l)))
	  ((or (char= c #\$) (char= c #\LOZENGE))
	   (if (null l)
	       (return ')
	       (return-token c l)))
	  ((char= c #\!)
	   (if (null l)
	       (return (cread))
	       (return-token c l)))
	  ((char= c #\?)
	   (setq quoted-p t)
	   (setq flonum-p ())
	   (setq fixnum-p ())
	   (setq c (ctyi)))
	  ((char= c #\" )
	   (if (null l)
	       (let ((x (ctoken-string)))
		 (setq ret-nud `',x
		       stringnud #'ret-nud)
		 (return x))
	       (return-token c l)))
	  ((cwhitespacep c)
	   (return-token c l))
	  ((char= c #\.)
	   (cond ((null l)
		  (if (cdigit-p (ctyipeek))
		      (setq fixnum-p () flonum-p t)
		      (return '\.)))
		 ((null fixnum-p)
		  (return-token c l t))
		 ('ELSE
		  (if fixnum-p (setq flonum-p t))
		  (setq fixnum-p ()))))
	  ((and (or (char= c #\E) (char= c #\e))
		flonum-p
		(not expt-p))
	   (let ((p (ctyipeek)))
	     (if (not (or (char= p #\+)
			  (char= p #\-)
			  (cdigit-p p)))
		 (return-token c l)))
	   (setq expt-p t))
	  ((cdigit-p c)
	   (if (null l)
	       (setq fixnum-p t))
	   (if expt-p (setq digit-after-expt-p t)))
	  ((and (or (char= c #\+) (char= c #\-))
		flonum-p
		expt-p
		(not digit-after-expt-p)
		(cdigit-p (ctyipeek))))
	  ((setq temp (clookup (setq c (ICHAR-UPCASE c)) ctoken-table))
	   (if (null l)
	       (return-token () (KONS c (cfollow-tail (cdr temp))) t ())
	       (return-token c l)))
	  (T
	   (setq fixnum-p ())
	   (setq flonum-p ())))))


(defun cwhitespacep (c)
  (or (char= c #\SP) (char= c #\CR) (char= c #\LF) (char= c #\TAB) (char= c #\FF)
      (char= c #\%)))

(defun cskip-whitespace ()
  (do ((commentp ())(c))
      (())
    (setq c (ctyi))
    (cond ((char= c #\%)
	   (setq commentp (not commentp)))
	  ((cwhitespacep c))
	  ((NOT COMMENTP)
	   (RETURN C)))))

(defun clookup (x y) (assoc X Y))

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
  `(let ((sys:default-cons-area sys:working-storage-area))
	    ,@l))

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
    (cond ((or (char= c #\$) (char= c #\LOZENGE))
	   ;; a little Dwim.
	   (cgolerr "tokenizer has inserted missing \" before " 0 ())
	   (return-token c l ()))
	  ((char= c #\")
	   (if (char= (ctyipeek) #\")
	       (ctyi)
	       (return-token () l ())))
	  ((and (char= c #\?) (or (char= (ctyipeek) #\$)
			      (char= (ctyipeek) #\LOZENGE)))
	   (setq c (ctyi))))))
	   
(defun cdigit-p (x) (not (or (char< x #\0) (char> x #\9))))

(DEFUN ICHAR-UPCASE (C &aux c1)
  (setq c1 (char-int c))
  (IF (AND (>= C1 #.(char-int #\a)) (<= C1 #.(char-int #\z)))
      (int-char (- C1 #.(- (char-int #\a) (char-int #\A)))) C))

(defun make-token  (l do-not-try-as-number-p rp)
  ;; takes the stack of characters and makes a token.
  (if rp (setq l (nreverse l)))
  (prog1
    (if (or do-not-try-as-number-p
	    (not (ok-as-number-p l)))
	(implode l)
	(let ((*read-base* cibase))
	  (creadlist l)))
    (reklaim l)
    ))

(defun creadlist (l)
  (let ((*readtable* cread-readtable))
    (zl:readlist l)))

(defun ok-as-number-p (l)
  ;; its more efficient to determine the type of
  ;; the token by collecting information in state variables
  ;; as it is read. However we aren't that sure of our book-keeping.
  (numberp (ignore-errors (creadlist l))))

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

(defun cgol-#-readmacro (stream)
  ;; #FOOBAR is a syntax escape to the FOOBAR language.
  (funcall (get-read (if (member (peek-char () stream)
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

(defun ratread ( &rest l)
  (let ((arithmetic_alist rat-arithmetic_alist))
    (declare (special arithmetic_alist))
    (apply #'cgolread l)))



(set-syntax-#-macro-char #\LOZENGE
			  #'(LAMBDA (IGNORE-LIST-SO-FAR STREAM)
			      (CGOL-#-READMACRO STREAM)))

(set-syntax-#-macro-char #\$
			  #'(LAMBDA (IGNORE-LIST-SO-FAR STREAM)
			      (CGOL-#-READMACRO STREAM)))



    
;; Implementation of (CGOL) function to get into CGOL mode readtable.
(progn 'compile

;; the idea here is to have a readtable such that every single
;; character causes CGOLREAD to be invoked. 

(Defvar cgol-invoking-readtable (copy-readtable si:*INITIAL-COMMON-LISP-READTABLE* ))
(defvar cgol-invoking-read-char #\SP "Untyi'd by the cgol-invoking-read-macro")

(setf (si:RDTBL-MACRO-ALIST cgol-invoking-readtable) ())
(do ((char 0 (1+ char)))
    ((= char #o200))
  (setf (si:RDTBL-TRANS cgol-invoking-readtable char) char)
  (zl:set-syntax-from-char (int-char char) #\' cgol-invoking-readtable))

(defun cgol-invoking-read-macro (ignore-list-so-far stream)
  (CGOLREAD-RAW-WITH-P STREAM CGOL-INVOKING-READ-CHAR))

(do ((char 0 (1+ char)))
    ((= char #o200))
  (zl:set-syntax-macro-char (int-char char)
			 (scl:let-and-make-dynamic-closure ((cgol-invoking-READ-CHAR CHAR))
			   #'cgol-invoking-read-macro)
			 cgol-invoking-readtable))
)


(defvar read-prin1-stack ())

(defun cgol-enter (ignore-it)
  (push (cons 
	      *READTABLE*
	      PRIN1)
	read-prin1-stack)
  
  (SETQ *READTABLE* CGOL-INVOKING-READTABLE))

(defun cgol-exit ()
  (let ((a (pop read-prin1-stack)))
    (setq  *READTABLE* (CAR A)
	  prin1 (cdr a))))


;; Defun compatibility.


(DEFUN FORMCHECK (FORM)
  ;; check for various obsolete usages.
  (COND ((ATOM FORM) FORM)
	((AND (EQ (CAR FORM) 'THROW)
	      (= (length FORM) 2))
	 `(throw 'CGOL-USER-THROW-TAG ,(CADR FORM)))
	('ELSE
	 FORM)))

#||

The following functions were referenced but don't seem defined:
 ADVANCE referenced by TOPLEVEL-PARSE-1
 PARSE referenced by TOPLEVEL-PARSE-1
 CAT referenced by GET-READ
||#

;; Now the parser, written in CGOL itself.
